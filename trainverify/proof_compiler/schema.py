"""Closed runtime schema validation for proof-compiler JSON inputs."""
from __future__ import annotations

import re
import math
from typing import Any

LEAN_SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")


def is_int(value: Any) -> bool:
    """JSON integer, deliberately excluding Python bool."""
    return type(value) is int


def json_value_error(value: Any) -> str | None:
    if value is None or isinstance(value, (str, bool)) or is_int(value):
        return None
    if isinstance(value, float):
        return None if math.isfinite(value) else "nonfinite numbers are not valid JSON"
    if isinstance(value, list):
        for item in value:
            error = json_value_error(item)
            if error is not None:
                return error
        return None
    if isinstance(value, dict):
        if any(not isinstance(key, str) for key in value):
            return "JSON object keys must be strings"
        for item in value.values():
            error = json_value_error(item)
            if error is not None:
                return error
        return None
    return f"unsupported JSON value type: {type(value).__name__}"


def relation_error(relation: Any) -> str | None:
    if not isinstance(relation, dict) or not isinstance(relation.get("kind"), str):
        return "relation must be an object with a string kind"
    kind = relation["kind"]
    schemas = {
        "equal": {"kind"},
        "replicated": {"kind"},
        "contiguous_shard": {"kind", "dim", "parts"},
        "zigzag": {"kind", "dim", "parts", "block_size"},
        "expert_partition": {"kind", "dim", "parts"},
        "partial_reduction": {"kind", "op", "parts"},
        "permuted_ownership": {"kind", "permutation"},
    }
    if kind not in schemas:
        return f"unknown relation kind: {kind}"
    if set(relation) != schemas[kind]:
        return f"{kind} relation fields must be {sorted(schemas[kind])}"
    if kind in {"contiguous_shard", "zigzag", "expert_partition"}:
        if not is_int(relation["dim"]) or relation["dim"] < 0:
            return f"{kind}.dim must be a nonnegative integer"
    if kind in {"contiguous_shard", "zigzag", "expert_partition", "partial_reduction"}:
        if not is_int(relation["parts"]) or relation["parts"] <= 0:
            return f"{kind}.parts must be a positive integer"
    if kind == "zigzag" and (
        not is_int(relation["block_size"]) or relation["block_size"] <= 0
    ):
        return "zigzag.block_size must be a positive integer"
    if kind == "partial_reduction" and (
        not isinstance(relation["op"], str)
        or relation["op"] not in {"sum", "mean"}
    ):
        return "partial_reduction.op must be sum or mean"
    if kind == "permuted_ownership":
        permutation = relation["permutation"]
        if (
            not isinstance(permutation, list)
            or any(not is_int(rank) or rank < 0 for rank in permutation)
            or len(permutation) != len(set(permutation))
        ):
            return "permuted_ownership.permutation must contain unique nonnegative ranks"
    return None


def relation_mapping_error(
    relation: dict[str, Any], pm_tids: list[dict[str, int]], num_ranks: int
) -> dict[str, Any] | None:
    ranks = [entry["rank"] for entry in pm_tids]
    if len(ranks) != len(set(ranks)):
        return {"reason": "relation_tensor_ranks_must_be_unique", "actual_ranks": ranks}
    kind = relation["kind"]
    if kind == "equal" and len(pm_tids) != 1:
        return {
            "expected_parts": 1,
            "actual_parts": len(pm_tids),
            "reason": "relation_tensor_cardinality_mismatch",
        }
    if kind == "replicated" and ranks != list(range(num_ranks)):
        return {
            "expected_ranks": list(range(num_ranks)),
            "actual_ranks": ranks,
            "reason": "replicated_seed_requires_exact_rank_coverage",
        }
    if kind in {
        "contiguous_shard", "zigzag", "expert_partition", "partial_reduction"
    }:
        expected_parts = relation["parts"]
        if expected_parts > num_ranks or len(pm_tids) != expected_parts:
            return {
                "expected_parts": expected_parts,
                "actual_parts": len(pm_tids),
                "reason": "relation_tensor_cardinality_mismatch",
            }
    if kind == "permuted_ownership":
        expected_ranks = relation["permutation"]
        if ranks != expected_ranks:
            return {
                "expected_ranks": expected_ranks,
                "actual_ranks": ranks,
                "reason": "permuted_ownership_rank_order_mismatch",
            }
    return None


def schema_failure(
    source: str, path: str, reason: str, *, detail: str | None = None
) -> dict[str, Any]:
    failure: dict[str, Any] = {
        "category": "certificate_bug" if source == "library" else "ambiguous_authority",
        "stage": "schema_validation",
        "source": source,
        "path": path,
        "reason": reason,
    }
    if detail is not None:
        failure["detail"] = detail
    return {"schema_version": 1, "status": "failure", "failure": failure}


def _validate_mapping(value: Any, path: str, num_ranks: int) -> dict[str, Any] | None:
    if not isinstance(value, list):
        return schema_failure("job", path, "tensor_mapping_must_be_list")
    for index, entry in enumerate(value):
        entry_path = f"{path}[{index}]"
        if not isinstance(entry, dict) or set(entry) != {"rank", "tid"}:
            return schema_failure("job", entry_path, "tensor_mapping_entry_fields_invalid")
        if not is_int(entry["rank"]) or not 0 <= entry["rank"] < num_ranks:
            return schema_failure("job", f"{entry_path}.rank", "rank_out_of_range")
        if not is_int(entry["tid"]) or entry["tid"] < 0:
            return schema_failure("job", f"{entry_path}.tid", "tid_must_be_nonnegative_integer")
    return None


def validate_inputs(job: Any, library: Any) -> dict[str, Any] | None:
    """Validate every JSON shape before inference indexes into it."""
    if not isinstance(job, dict):
        return schema_failure("job", "$", "job_must_be_object")
    if not isinstance(library, dict):
        return schema_failure("library", "$", "library_must_be_object")
    job_allowed = {
        "schema_version", "num_ranks", "target_manifest_sha256", "sm_nodes",
        "pm_nodes", "input_relations", "observables",
    }
    if not set(job) <= job_allowed:
        return schema_failure("job", "$", "unknown_job_fields")
    if set(library) - {"rules", "denotations"}:
        return schema_failure("library", "$", "unknown_library_fields")
    for field in ("rules", "denotations"):
        if not isinstance(library.get(field), list):
            return schema_failure("library", field, "required_field_must_be_list")

    num_ranks_value = job.get("num_ranks")
    if type(num_ranks_value) is not int:
        return None  # compile_job preserves its established exact diagnostic.
    num_ranks: int = num_ranks_value
    if num_ranks <= 0:
        return None

    node_required = {"logical_id", "rank", "op", "ins", "outs"}
    node_allowed = node_required | {"attrs"}
    for graph_field in ("sm_nodes", "pm_nodes"):
        nodes = job.get(graph_field)
        if not isinstance(nodes, list):
            continue
        for index, node in enumerate(nodes):
            path = f"{graph_field}[{index}]"
            if (
                not isinstance(node, dict)
                or not node_required <= set(node)
                or not set(node) <= node_allowed
            ):
                return schema_failure("job", path, "node_fields_invalid")
            if not isinstance(node["logical_id"], str) or not node["logical_id"]:
                return schema_failure("job", f"{path}.logical_id", "logical_id_must_be_nonempty_string")
            if not isinstance(node["op"], str) or not node["op"]:
                return schema_failure("job", f"{path}.op", "operator_must_be_nonempty_string")
            if not is_int(node["rank"]) or node["rank"] < 0:
                return schema_failure("job", f"{path}.rank", "rank_must_be_nonnegative_integer")
            if graph_field == "pm_nodes" and node["rank"] >= num_ranks:
                return schema_failure("job", f"{path}.rank", "rank_out_of_range")
            for tids_field in ("ins", "outs"):
                tids = node[tids_field]
                if not isinstance(tids, list) or any(
                    not is_int(tid) or tid < 0 for tid in tids
                ):
                    return schema_failure(
                        "job", f"{path}.{tids_field}", "tids_must_be_nonnegative_integers"
                    )
            if "attrs" in node and not isinstance(node["attrs"], dict):
                return schema_failure("job", f"{path}.attrs", "operator_attrs_must_be_object")
            if "attrs" in node:
                error = json_value_error(node["attrs"])
                if error is not None:
                    return schema_failure(
                        "job", f"{path}.attrs", "invalid_operator_attrs", detail=error
                    )

    seeds = job.get("input_relations")
    if isinstance(seeds, list):
        for index, seed in enumerate(seeds):
            path = f"input_relations[{index}]"
            if (
                not isinstance(seed, dict)
                or set(seed) != {"sm_tid", "pm_tids", "relation", "provenance"}
            ):
                return schema_failure("job", path, "input_relation_fields_invalid")
            if not is_int(seed["sm_tid"]) or seed["sm_tid"] < 0:
                return schema_failure("job", f"{path}.sm_tid", "tid_must_be_nonnegative_integer")
            failure = _validate_mapping(seed["pm_tids"], f"{path}.pm_tids", num_ranks)
            if failure is not None:
                return failure
            if not isinstance(seed["provenance"], dict):
                return schema_failure("job", f"{path}.provenance", "provenance_must_be_object")

    observables = job.get("observables")
    if isinstance(observables, list):
        for index, observable in enumerate(observables):
            path = f"observables[{index}]"
            allowed = {"sm_tid", "pm_tids", "relation"}
            if (
                not isinstance(observable, dict)
                or not {"sm_tid", "pm_tids"} <= set(observable)
                or not set(observable) <= allowed
            ):
                return schema_failure("job", path, "observable_fields_invalid")
            if not is_int(observable["sm_tid"]) or observable["sm_tid"] < 0:
                return schema_failure("job", f"{path}.sm_tid", "tid_must_be_nonnegative_integer")
            failure = _validate_mapping(observable["pm_tids"], f"{path}.pm_tids", num_ranks)
            if failure is not None:
                return failure
            if "relation" in observable:
                error = relation_error(observable["relation"])
                if error is not None:
                    return schema_failure(
                        "job", f"{path}.relation", "invalid_relation", detail=error
                    )
                mapping_error = relation_mapping_error(
                    observable["relation"], observable["pm_tids"], num_ranks
                )
                if mapping_error is not None:
                    failure = schema_failure(
                        "job", f"{path}.pm_tids", mapping_error["reason"]
                    )
                    failure["failure"].update(
                        {key: value for key, value in mapping_error.items() if key != "reason"}
                    )
                    return failure

    for index, entry in enumerate(library["denotations"]):
        path = f"denotations[{index}]"
        if not isinstance(entry, dict) or set(entry) != {"op", "lean_definition"}:
            return schema_failure("library", path, "denotation_fields_invalid")
        if not isinstance(entry["op"], str) or not entry["op"]:
            return schema_failure("library", f"{path}.op", "operator_must_be_nonempty_string")
        symbol = entry["lean_definition"]
        if not isinstance(symbol, str) or LEAN_SYMBOL.fullmatch(symbol) is None:
            return schema_failure(
                "library", f"{path}.lean_definition", "lean_symbol_must_be_qualified_string"
            )

    required = {
        "name", "sm_op", "pm_op", "input_relations", "output_relations", "lean_theorem"
    }
    allowed = required | {"sm_attrs", "pm_attrs"}
    for index, rule in enumerate(library["rules"]):
        path = f"rules[{index}]"
        if (
            not isinstance(rule, dict)
            or not required <= set(rule)
            or not set(rule) <= allowed
        ):
            return schema_failure("library", path, "rule_fields_invalid")
        for field in ("name", "sm_op", "pm_op"):
            if not isinstance(rule[field], str) or not rule[field]:
                return schema_failure("library", f"{path}.{field}", "field_must_be_nonempty_string")
        if not isinstance(rule["input_relations"], list) or not isinstance(
            rule["output_relations"], list
        ):
            return schema_failure("library", path, "rule_relations_must_be_lists")
        for output_index, transfer in enumerate(rule["output_relations"]):
            if not isinstance(transfer, dict):
                return schema_failure(
                    "library",
                    f"{path}.output_relations[{output_index}]",
                    "rule_output_transfer_must_be_object",
                )
        for field in ("sm_attrs", "pm_attrs"):
            if field in rule and not isinstance(rule[field], dict):
                return schema_failure("library", f"{path}.{field}", "operator_attrs_must_be_object")
            if field in rule:
                error = json_value_error(rule[field])
                if error is not None:
                    return schema_failure(
                        "library", f"{path}.{field}", "invalid_operator_attrs", detail=error
                    )
        theorem = rule["lean_theorem"]
        if not isinstance(theorem, str) or LEAN_SYMBOL.fullmatch(theorem) is None:
            return schema_failure(
                "library", f"{path}.lean_theorem", "lean_symbol_must_be_qualified_string"
            )
    return None
