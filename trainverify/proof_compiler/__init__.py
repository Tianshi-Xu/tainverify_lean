"""Typed graph-relation inference and proof-certificate DAG synthesis."""
from __future__ import annotations

from collections import defaultdict
from copy import deepcopy
import hashlib
import json
import re
from typing import Any

from .schema import (
    LEAN_SYMBOL,
    is_int,
    json_value_error,
    relation_error as _relation_error,
    relation_mapping_error as _relation_mapping_error,
    validate_inputs,
)

REPLICATION_SEED_PROVENANCE = {
    "authority_input",
    "collective_broadcast",
    "shared_constant",
}


def _replication_provenance_error(provenance: Any, sm_tid: int, ranks: list[int]) -> str | None:
    if not isinstance(provenance, dict):
        return "replication provenance must be an object"
    if set(provenance) != {
        "kind", "source", "authority_sha256", "value_witness", "ownership_witness"
    }:
        return "replication provenance fields are not closed"
    if not isinstance(provenance["source"], str) or not provenance["source"]:
        return "replication provenance requires a nonempty source"
    digest = provenance.get("authority_sha256")
    if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
        return "replication provenance requires a lowercase authority_sha256"
    ownership = provenance.get("ownership_witness")
    if (
        not isinstance(ownership, dict)
        or ownership.get("kind") != "exact_rank_set"
        or not isinstance(ownership.get("ranks"), list)
        or any(not is_int(rank) for rank in ownership["ranks"])
        or ownership["ranks"] != ranks
    ):
        return "replication ownership_witness must name the exact rank set"
    value = provenance.get("value_witness")
    if provenance.get("kind") == "authority_input":
        if (
            not isinstance(value, dict)
            or set(value) != {"kind", "sm_tid"}
            or value.get("kind") != "same_authority_tensor"
            or not is_int(value.get("sm_tid"))
            or value["sm_tid"] != sm_tid
        ):
            return "authority_input requires a same_authority_tensor value_witness"
    elif provenance.get("kind") == "collective_broadcast":
        if (
            not isinstance(value, dict)
            or value.get("kind") != "collective_broadcast"
            or not isinstance(value.get("collective_id"), str)
            or not is_int(value.get("root_rank"))
            or value["root_rank"] not in ranks
        ):
            return "collective_broadcast requires collective_id and valid root_rank"
    elif provenance.get("kind") == "shared_constant":
        if (
            not isinstance(value, dict)
            or value.get("kind") != "shared_constant"
            or not isinstance(value.get("value_sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", value["value_sha256"]) is None
        ):
            return "shared_constant requires a content-addressed value_witness"
    else:
        return "unsupported replication provenance kind"
    return None


def _relation_id(sm_tid: int) -> str:
    return f"rel:{sm_tid}"


def _json_equal(left: Any, right: Any) -> bool:
    options = {"sort_keys": True, "separators": (",", ":")}
    return json.dumps(left, **options) == json.dumps(right, **options)


def _seed_provenance_error(
    provenance: Any,
    sm_tid: int,
    pm_tids: list[dict[str, int]],
    relation: dict[str, Any],
) -> str | None:
    if relation["kind"] == "replicated":
        return _replication_provenance_error(
            provenance, sm_tid, [entry["rank"] for entry in pm_tids]
        )
    if not isinstance(provenance, dict):
        return "seed provenance must be an object"
    if set(provenance) != {
        "kind", "source", "authority_sha256", "value_witness", "ownership_witness"
    }:
        return "seed provenance fields are not closed"
    if provenance.get("kind") != "authority_input":
        return "non-replicated seed requires authority_input provenance"
    if not isinstance(provenance.get("source"), str) or not provenance["source"]:
        return "seed provenance requires a nonempty source"
    digest = provenance.get("authority_sha256")
    if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
        return "seed provenance requires a lowercase authority_sha256"
    expected_value = {
        "kind": "authority_tensor_mapping",
        "sm_tid": sm_tid,
        "pm_tids": pm_tids,
    }
    if not _json_equal(provenance.get("value_witness"), expected_value):
        return "seed value_witness must bind the exact SM/PM tensor mapping"
    expected_ownership = {
        "kind": "exact_rank_set",
        "ranks": [entry["rank"] for entry in pm_tids],
    }
    if not _json_equal(provenance.get("ownership_witness"), expected_ownership):
        return "seed ownership_witness must bind the exact rank set"
    return None


def _group_pm_nodes(nodes: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for node in nodes:
        grouped[node["logical_id"]].append(node)
    for group in grouped.values():
        group.sort(key=lambda node: node["rank"])
    return grouped


def validate_certificate_dag(
    certificate_dag: list[dict[str, Any]],
    observables: list[dict[str, Any]],
    library: dict[str, Any] | None = None,
    *,
    num_ranks: int | None = None,
    target_manifest_sha256: str | None = None,
    target_observables: list[dict[str, Any]] | None = None,
) -> dict[str, Any] | None:
    def failure(reason: str, **fields: Any) -> dict[str, Any]:
        return {
            "category": "certificate_bug",
            "stage": "certificate_validation",
            **fields,
            "reason": reason,
        }

    if not isinstance(certificate_dag, list) or not isinstance(observables, list):
        return failure("certificate_dag_and_observables_must_be_lists")
    ids: set[str] = set()
    for index, node in enumerate(certificate_dag):
        if (
            not isinstance(node, dict)
            or not isinstance(node.get("id"), str)
            or not node["id"]
            or not isinstance(node.get("premises"), list)
            or any(not isinstance(premise, str) for premise in node["premises"])
        ):
            return failure("invalid_certificate_node_schema", node_index=index)
        certificate = node["id"]
        if certificate in ids:
            return failure("duplicate_certificate_id", certificate=certificate)
        ids.add(certificate)

    seen: set[str] = set()
    for node in certificate_dag:
        for premise in node["premises"]:
            if premise not in ids:
                return failure(
                    "certificate_dag_reference_not_found",
                    certificate=node["id"],
                    dangling_reference=premise,
                )
            if premise not in seen:
                return failure(
                    "certificate_dag_must_be_topologically_ordered",
                    certificate=node["id"],
                    forward_reference=premise,
                )
        seen.add(node["id"])

    seed_fields = {
        "id", "kind", "sm_tid", "pm_tids", "relation", "provenance", "premises"
    }
    rule_fields = {
        "id", "kind", "logical_id", "output_index", "rule", "lean_theorem",
        "sm_node", "pm_nodes", "premises", "sm_tid", "pm_tids", "relation",
    }
    by_id: dict[str, dict[str, Any]] = {}
    for index, node in enumerate(certificate_dag):
        kind = node.get("kind")
        expected_fields = seed_fields if kind == "seed_relation" else rule_fields
        if (
            not isinstance(kind, str)
            or kind not in {"seed_relation", "rule_application"}
            or set(node) != expected_fields
        ):
            return failure("invalid_certificate_node_schema", node_index=index)
        if (
            not is_int(node["sm_tid"])
            or node["sm_tid"] < 0
            or node["id"] != _relation_id(node["sm_tid"])
            or not isinstance(node["pm_tids"], list)
            or any(
                not isinstance(entry, dict) or set(entry) != {"rank", "tid"}
                or not is_int(entry["rank"]) or not is_int(entry["tid"])
                for entry in node["pm_tids"]
            )
            or _relation_error(node["relation"]) is not None
        ):
            return failure("invalid_certificate_node_schema", node_index=index)
        if kind == "seed_relation":
            if node["premises"] or not isinstance(node["provenance"], dict):
                return failure("invalid_certificate_node_schema", node_index=index)
        else:
            if (
                not isinstance(node["logical_id"], str)
                or not isinstance(node["rule"], str)
                or not isinstance(node["lean_theorem"], str)
                or not is_int(node["output_index"])
                or not isinstance(node["sm_node"], dict)
                or not isinstance(node["pm_nodes"], list)
            ):
                return failure("invalid_certificate_node_schema", node_index=index)
        by_id[node["id"]] = node

    all_ranks = [
        entry["rank"]
        for node in certificate_dag
        for entry in node["pm_tids"]
    ]
    inferred_num_ranks = max(all_ranks, default=0) + 1
    validation_num_ranks = (
        num_ranks if type(num_ranks) is int and num_ranks > 0 else inferred_num_ranks
    )

    def valid_graph_node(node: Any) -> bool:
        required = {"logical_id", "rank", "op", "ins", "outs"}
        if (
            not isinstance(node, dict)
            or not required <= set(node)
            or not set(node) <= required | {"attrs"}
            or not isinstance(node["logical_id"], str)
            or not isinstance(node["op"], str)
            or not is_int(node["rank"])
            or not isinstance(node["ins"], list)
            or not isinstance(node["outs"], list)
            or any(not is_int(tid) for tid in node["ins"] + node["outs"])
        ):
            return False
        if "attrs" not in node:
            return True
        return isinstance(node["attrs"], dict) and json_value_error(node["attrs"]) is None

    for index, node in enumerate(certificate_dag):
        if any(
            not 0 <= entry["rank"] < validation_num_ranks
            for entry in node["pm_tids"]
        ):
            return failure(
                "invalid_relation_mapping",
                node_index=index,
                certificate=node["id"],
                detail="rank outside authority num_ranks",
            )
        mapping_error = _relation_mapping_error(
            node["relation"], node["pm_tids"], validation_num_ranks
        )
        if mapping_error is not None:
            return failure(
                "invalid_relation_mapping",
                node_index=index,
                certificate=node["id"],
                detail=mapping_error,
            )
        if node["kind"] == "seed_relation":
            provenance_error = _seed_provenance_error(
                node["provenance"], node["sm_tid"], node["pm_tids"], node["relation"]
            )
            if provenance_error is not None:
                reason = (
                    "invalid_replication_provenance"
                    if node["relation"]["kind"] == "replicated"
                    else "invalid_seed_provenance"
                )
                return failure(
                    reason,
                    node_index=index,
                    certificate=node["id"],
                    detail=provenance_error,
                )
            continue

        sm_node = node["sm_node"]
        pm_nodes = node["pm_nodes"]
        output_index = node["output_index"]
        coherent = (
            valid_graph_node(sm_node)
            and isinstance(pm_nodes, list)
            and bool(pm_nodes)
            and all(valid_graph_node(pm_node) for pm_node in pm_nodes)
            and LEAN_SYMBOL.fullmatch(node["lean_theorem"]) is not None
            and bool(node["rule"])
            and node["logical_id"] == sm_node["logical_id"]
            and is_int(output_index)
            and 0 <= output_index < len(sm_node["outs"])
            and sm_node["outs"][output_index] == node["sm_tid"]
            and len(node["premises"]) == len(sm_node["ins"])
        )
        if coherent:
            pm_ranks = [pm_node["rank"] for pm_node in pm_nodes]
            coherent = pm_ranks == list(range(validation_num_ranks)) and all(
                pm_node["logical_id"] == node["logical_id"]
                and len(pm_node["ins"]) == len(sm_node["ins"])
                and len(pm_node["outs"]) == len(sm_node["outs"])
                for pm_node in pm_nodes
            )
        if coherent:
            expected_pm_tids = [
                {"rank": pm_node["rank"], "tid": pm_node["outs"][output_index]}
                for pm_node in pm_nodes
            ]
            coherent = expected_pm_tids == node["pm_tids"]
        if coherent:
            for input_index, premise_id in enumerate(node["premises"]):
                premise = by_id[premise_id]
                expected_inputs = [
                    {"rank": pm_node["rank"], "tid": pm_node["ins"][input_index]}
                    for pm_node in pm_nodes
                ]
                if (
                    premise["sm_tid"] != sm_node["ins"][input_index]
                    or premise["pm_tids"] != expected_inputs
                ):
                    coherent = False
                    break
        if not coherent:
            return failure(
                "incoherent_rule_application_payload",
                node_index=index,
                certificate=node["id"],
            )

    rule_nodes = [node for node in certificate_dag if node["kind"] == "rule_application"]
    if rule_nodes:
        if library is None:
            return failure("semantic_library_required_for_rule_validation")
        dummy_job = {
            "schema_version": 1,
            "num_ranks": 1,
            "sm_nodes": [],
            "pm_nodes": [],
            "input_relations": [],
            "observables": [],
        }
        library_failure = validate_inputs(dummy_job, library)
        if library_failure is not None:
            return failure(
                "invalid_semantic_library",
                detail=library_failure["failure"],
            )
        rules_by_name: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for rule in library["rules"]:
            rules_by_name[rule["name"]].append(rule)
        denotations_by_op: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for denotation in library["denotations"]:
            denotations_by_op[denotation["op"]].append(denotation)
        if any(len(entries) != 1 for entries in rules_by_name.values()) or any(
            len(entries) != 1 for entries in denotations_by_op.values()
        ):
            return failure("invalid_semantic_library", detail="duplicate registry entry")
        for rule in library["rules"]:
            if any(_relation_error(relation) is not None for relation in rule["input_relations"]):
                return failure("invalid_semantic_library", detail="invalid input relation")
            for transfer in rule["output_relations"]:
                if set(transfer) == {"from_input"}:
                    source_index = transfer["from_input"]
                    if (
                        not is_int(source_index)
                        or not 0 <= source_index < len(rule["input_relations"])
                    ):
                        return failure("invalid_semantic_library", detail="invalid transfer")
                elif set(transfer) == {"relation"}:
                    if _relation_error(transfer["relation"]) is not None:
                        return failure("invalid_semantic_library", detail="invalid output relation")
                else:
                    return failure("invalid_semantic_library", detail="invalid transfer")

        for index, node in enumerate(certificate_dag):
            if node["kind"] != "rule_application":
                continue
            candidates = rules_by_name.get(node["rule"], [])
            if len(candidates) != 1:
                return failure(
                    "rule_application_not_in_semantic_library",
                    node_index=index,
                    certificate=node["id"],
                )
            rule = candidates[0]
            sm_node = node["sm_node"]
            pm_nodes = node["pm_nodes"]
            premises = [by_id[premise_id] for premise_id in node["premises"]]
            output_index = node["output_index"]
            registry_match = (
                node["lean_theorem"] == rule["lean_theorem"]
                and sm_node["op"] == rule["sm_op"]
                and _json_equal(sm_node.get("attrs", {}), rule.get("sm_attrs", {}))
                and all(
                    pm_node["op"] == rule["pm_op"]
                    and _json_equal(pm_node.get("attrs", {}), rule.get("pm_attrs", {}))
                    for pm_node in pm_nodes
                )
                and len(denotations_by_op.get(rule["sm_op"], [])) == 1
                and len(denotations_by_op.get(rule["pm_op"], [])) == 1
                and len(rule["input_relations"]) == len(premises)
                and all(
                    _json_equal(expected, premise["relation"])
                    for expected, premise in zip(rule["input_relations"], premises)
                )
                and len(rule["output_relations"]) == len(sm_node["outs"])
            )
            if registry_match:
                transfer = rule["output_relations"][output_index]
                if set(transfer) == {"from_input"}:
                    source_index = transfer["from_input"]
                    registry_match = (
                        is_int(source_index)
                        and 0 <= source_index < len(premises)
                        and _json_equal(node["relation"], premises[source_index]["relation"])
                    )
                elif set(transfer) == {"relation"}:
                    registry_match = _json_equal(node["relation"], transfer["relation"])
                else:
                    registry_match = False
            if not registry_match:
                return failure(
                    "rule_application_not_in_semantic_library",
                    node_index=index,
                    certificate=node["id"],
                )

    observable_fields = {"sm_tid", "pm_tids", "relation", "certificate"}
    for index, observable in enumerate(observables):
        if not isinstance(observable, dict) or set(observable) != observable_fields:
            return failure("invalid_observable_certificate_schema", observable_index=index)
        certificate = observable["certificate"]
        if certificate not in ids:
            return failure("observable_certificate_not_found", certificate=certificate)
        node = by_id[certificate]
        if (
            observable["sm_tid"] != node["sm_tid"]
            or observable["pm_tids"] != node["pm_tids"]
            or observable["relation"] != node["relation"]
            or certificate != _relation_id(observable["sm_tid"])
        ):
            return failure(
                "observable_certificate_payload_mismatch",
                certificate=certificate,
                observable_index=index,
            )

    if (
        type(num_ranks) is not int
        or num_ranks <= 0
        or not isinstance(target_manifest_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", target_manifest_sha256) is None
        or not isinstance(target_observables, list)
        or not target_observables
    ):
        return failure("certificate_authority_context_required")
    if json_value_error(target_observables) is not None:
        return failure("invalid_target_manifest")
    target_payload = json.dumps(
        target_observables, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    actual_target_digest = hashlib.sha256(target_payload).hexdigest()
    if actual_target_digest != target_manifest_sha256:
        return failure(
            "target_manifest_digest_mismatch",
            expected_target_manifest_sha256=target_manifest_sha256,
            actual_target_manifest_sha256=actual_target_digest,
        )
    if len(observables) != len(target_observables):
        return failure("certificate_observables_do_not_match_target_manifest")
    for target, observable in zip(target_observables, observables):
        if (
            not isinstance(target, dict)
            or not {"sm_tid", "pm_tids"} <= set(target)
            or not set(target) <= {"sm_tid", "pm_tids", "relation"}
            or target["sm_tid"] != observable["sm_tid"]
            or not _json_equal(target["pm_tids"], observable["pm_tids"])
            or (
                "relation" in target
                and not _json_equal(target["relation"], observable["relation"])
            )
        ):
            return failure("certificate_observables_do_not_match_target_manifest")
    return None


def compile_job(job: dict[str, Any], library: dict[str, Any]) -> dict[str, Any]:
    """Infer edge relations and emit an explicit, deterministic certificate DAG."""
    input_failure = validate_inputs(job, library)
    if input_failure is not None:
        return input_failure
    if not is_int(job.get("schema_version")) or job["schema_version"] != 1:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "ambiguous_authority",
                "stage": "schema_validation",
                "field": "schema_version",
                "expected": 1,
                "actual": job.get("schema_version"),
                "reason": "unsupported_job_schema_version",
            },
        }
    if not is_int(job.get("num_ranks")) or job["num_ranks"] <= 0:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "ambiguous_authority",
                "stage": "schema_validation",
                "field": "num_ranks",
                "actual": job.get("num_ranks"),
                "reason": "num_ranks_must_be_positive_integer",
            },
        }
    for field in ("sm_nodes", "pm_nodes", "input_relations", "observables"):
        if not isinstance(job.get(field), list):
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "schema_validation",
                    "field": field,
                    "reason": "required_job_field_must_be_list",
                },
            }
    rules = library["rules"]
    seen_rule_names: set[str] = set()
    for rule in rules:
        if rule["name"] in seen_rule_names:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "certificate_bug",
                    "stage": "library_validation",
                    "rule": rule["name"],
                    "reason": "duplicate_rule_name",
                },
            }
        seen_rule_names.add(rule["name"])
        for input_index, relation in enumerate(rule["input_relations"]):
            relation_error = _relation_error(relation)
            if relation_error is not None:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "certificate_bug",
                        "stage": "library_validation",
                        "rule": rule["name"],
                        "input_index": input_index,
                        "reason": "invalid_rule_input_relation",
                        "detail": relation_error,
                    },
                }
        for output_index, transfer in enumerate(rule["output_relations"]):
            if set(transfer) == {"from_input"}:
                source_index = transfer["from_input"]
                if (
                    not is_int(source_index)
                    or source_index < 0
                    or source_index >= len(rule["input_relations"])
                ):
                    return {
                        "schema_version": 1,
                        "status": "failure",
                        "failure": {
                            "category": "certificate_bug",
                            "stage": "library_validation",
                            "rule": rule["name"],
                            "output_index": output_index,
                            "reason": "invalid_rule_output_transfer",
                            "detail": "from_input must index an input relation",
                        },
                    }
                continue
            if set(transfer) != {"relation"}:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "certificate_bug",
                        "stage": "library_validation",
                        "rule": rule["name"],
                        "output_index": output_index,
                        "reason": "invalid_rule_output_transfer",
                        "detail": "output transfer must contain exactly relation or from_input",
                    },
                }
            relation_error = _relation_error(transfer["relation"])
            if relation_error is not None:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "certificate_bug",
                        "stage": "library_validation",
                        "rule": rule["name"],
                        "output_index": output_index,
                        "reason": "invalid_rule_output_relation",
                        "detail": relation_error,
                    },
                }
    denotation_definitions: dict[str, list[str]] = defaultdict(list)
    for entry in library["denotations"]:
        denotation_definitions[entry["op"]].append(entry["lean_definition"])
    for operator, definitions in denotation_definitions.items():
        if len(definitions) > 1:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "certificate_bug",
                    "stage": "library_validation",
                    "operator": operator,
                    "definitions": definitions,
                    "reason": "duplicate_faithful_denotation",
                },
            }
    denoted_ops = set(denotation_definitions)
    for graph_name, nodes in (("sm", job["sm_nodes"]), ("pm", job["pm_nodes"])):
        for node in nodes:
            if node["op"] not in denoted_ops:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "unsupported_operator",
                        "stage": "authority_validation",
                        "graph": graph_name,
                        "logical_id": node["logical_id"],
                        "operator": node["op"],
                        "node": deepcopy(node),
                        "reason": "missing_faithful_denotation",
                    },
                }
        producers: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for node in nodes:
            for tid in node["outs"]:
                producers[tid].append(node)
        for tid in sorted(producers):
            if len(producers[tid]) > 1:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "authority_validation",
                        "graph": graph_name,
                        "tid": tid,
                        "producer_logical_ids": [
                            node["logical_id"] for node in producers[tid]
                        ],
                        "reason": "tensor_must_have_at_most_one_producer",
                    },
                }
    pm_by_logical = _group_pm_nodes(job["pm_nodes"])
    sm_logical_sequence = [node["logical_id"] for node in job["sm_nodes"]]
    seen_logical_ids: set[str] = set()
    for logical_id in sm_logical_sequence:
        if logical_id in seen_logical_ids:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "logical_id": logical_id,
                    "reason": "sm_logical_id_must_be_unique",
                },
            }
        seen_logical_ids.add(logical_id)
    sm_logical_ids = sorted(sm_logical_sequence)
    pm_logical_ids = sorted(pm_by_logical)
    if sm_logical_ids != pm_logical_ids:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "ambiguous_authority",
                "stage": "authority_validation",
                "expected_sm_logical_ids": sm_logical_ids,
                "actual_pm_logical_ids": pm_logical_ids,
                "reason": "sm_pm_logical_groups_must_match",
            },
        }
    expected_ranks = list(range(job["num_ranks"]))
    for sm_node in job["sm_nodes"]:
        logical_id = sm_node["logical_id"]
        actual_ranks = [node["rank"] for node in pm_by_logical.get(logical_id, [])]
        if actual_ranks != expected_ranks:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "logical_id": logical_id,
                    "expected_ranks": expected_ranks,
                    "actual_ranks": actual_ranks,
                    "reason": "pm_logical_group_must_have_exactly_one_node_per_rank",
                },
            }
        for pm_node in pm_by_logical[logical_id]:
            if len(pm_node["ins"]) != len(sm_node["ins"]):
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "authority_validation",
                        "logical_id": logical_id,
                        "rank": pm_node["rank"],
                        "expected_input_arity": len(sm_node["ins"]),
                        "actual_input_arity": len(pm_node["ins"]),
                        "reason": "sm_pm_node_input_arity_mismatch",
                    },
                }
            if len(pm_node["outs"]) != len(sm_node["outs"]):
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "authority_validation",
                        "logical_id": logical_id,
                        "rank": pm_node["rank"],
                        "expected_output_arity": len(sm_node["outs"]),
                        "actual_output_arity": len(pm_node["outs"]),
                        "reason": "sm_pm_node_output_arity_mismatch",
                    },
                }
    relations: dict[int, dict[str, Any]] = {}
    certificate_dag: list[dict[str, Any]] = []
    seeded_sm_tids: set[int] = set()
    produced_sm_tids = {tid for node in job["sm_nodes"] for tid in node["outs"]}
    graph_input_tids = {
        tid
        for node in job["sm_nodes"]
        for tid in node["ins"]
        if tid not in produced_sm_tids
    }
    seed_ids = [seed["sm_tid"] for seed in job["input_relations"]]
    duplicate_seed = next(
        (sm_tid for sm_tid in seed_ids if seed_ids.count(sm_tid) > 1), None
    )
    if duplicate_seed is not None:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "ambiguous_authority",
                "stage": "authority_validation",
                "sm_tid": duplicate_seed,
                "reason": "duplicate_input_relation_seed",
            },
        }
    for seed in job["input_relations"]:
        if seed.get("sm_tid") in seeded_sm_tids:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "sm_tid": seed.get("sm_tid"),
                    "reason": "duplicate_input_relation_seed",
                },
            }
        seeded_sm_tids.add(seed.get("sm_tid"))
        seed_producer = next(
            (
                node
                for node in job["sm_nodes"]
                if seed.get("sm_tid") in node["outs"]
            ),
            None,
        )
        if seed_producer is not None:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "sm_tid": seed.get("sm_tid"),
                    "producer_logical_id": seed_producer["logical_id"],
                    "reason": "input_relation_seed_must_reference_graph_input",
                },
            }
        relation_error = _relation_error(seed.get("relation"))
        if relation_error is not None:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "sm_tid": seed.get("sm_tid"),
                    "relation": deepcopy(seed.get("relation")),
                    "reason": "invalid_relation",
                    "detail": relation_error,
                },
            }
        mapping_error = _relation_mapping_error(
            seed["relation"], seed["pm_tids"], job["num_ranks"]
        )
        if mapping_error is not None:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "sm_tid": seed["sm_tid"],
                    **mapping_error,
                },
            }
        if seed["relation"]["kind"] == "replicated":
            expected_seed_ranks = list(range(job["num_ranks"]))
            provenance_kind = seed["provenance"].get("kind")
            if (
                not isinstance(provenance_kind, str)
                or provenance_kind not in REPLICATION_SEED_PROVENANCE
            ):
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "authority_validation",
                        "sm_tid": seed["sm_tid"],
                        "pm_tids": deepcopy(seed["pm_tids"]),
                        "expected_relation": deepcopy(seed["relation"]),
                        "actual_inferred_relation": None,
                        "reason": "identity_fanout_does_not_prove_cross_rank_value_equality",
                    },
                }
            provenance_error = _replication_provenance_error(
                seed["provenance"], seed["sm_tid"], expected_seed_ranks
            )
            if provenance_error is not None:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "authority_validation",
                        "sm_tid": seed["sm_tid"],
                        "reason": "replicated_seed_requires_value_ownership_provenance",
                        "detail": provenance_error,
                    },
                }
        else:
            provenance_error = _seed_provenance_error(
                seed["provenance"], seed["sm_tid"], seed["pm_tids"], seed["relation"]
            )
            if provenance_error is not None:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "authority_validation",
                        "sm_tid": seed["sm_tid"],
                        "reason": "input_relation_seed_requires_authority_provenance",
                        "detail": provenance_error,
                    },
                }
        if seed["sm_tid"] not in graph_input_tids:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "authority_validation",
                    "sm_tid": seed["sm_tid"],
                    "reason": "input_relation_seed_must_reference_graph_input",
                },
            }
        relation_id = _relation_id(seed["sm_tid"])
        relations[seed["sm_tid"]] = {
            "pm_tids": deepcopy(seed["pm_tids"]),
            "relation": deepcopy(seed["relation"]),
            "relation_id": relation_id,
            "certificate": relation_id,
            "provenance": deepcopy(seed["provenance"]),
        }
        certificate_dag.append(
            {
                "id": relation_id,
                "kind": "seed_relation",
                "sm_tid": seed["sm_tid"],
                "pm_tids": deepcopy(seed["pm_tids"]),
                "relation": deepcopy(seed["relation"]),
                "provenance": deepcopy(seed["provenance"]),
                "premises": [],
            }
        )

    for sm_node in job["sm_nodes"]:
        logical_id = sm_node["logical_id"]
        pm_nodes = pm_by_logical[logical_id]
        for input_index, sm_tid in enumerate(sm_node["ins"]):
            if sm_tid not in relations:
                pm_tids = [
                    {"rank": pm["rank"], "tid": pm["ins"][input_index]}
                    for pm in pm_nodes
                ]
                if sm_tid in produced_sm_tids:
                    return {
                        "schema_version": 1,
                        "status": "failure",
                        "failure": {
                            "category": "ambiguous_authority",
                            "stage": "relation_inference",
                            "logical_id": logical_id,
                            "sm_tid": sm_tid,
                            "pm_tids": pm_tids,
                            "reason": "relation_dependency_not_available_in_topological_order",
                        },
                    }
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "missing_input_contract",
                        "stage": "relation_inference",
                        "logical_id": logical_id,
                        "sm_tid": sm_tid,
                        "pm_tids": pm_tids,
                        "reason": "no_relation_for_graph_input",
                    },
                }
            expected_pm_tids = relations[sm_tid]["pm_tids"]
            actual_pm_tids = [
                {"rank": pm["rank"], "tid": pm["ins"][input_index]}
                for pm in pm_nodes
            ]
            if actual_pm_tids != expected_pm_tids:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "ambiguous_authority",
                        "stage": "relation_inference",
                        "logical_id": logical_id,
                        "input_index": input_index,
                        "sm_tid": sm_tid,
                        "expected_pm_tids": deepcopy(expected_pm_tids),
                        "actual_pm_tids": actual_pm_tids,
                        "reason": "pm_node_inputs_do_not_match_inferred_relation",
                    },
                }
        input_relations = [relations[tid] for tid in sm_node["ins"]]
        operator_candidates = [
            rule
            for rule in rules
            if rule["sm_op"] == sm_node["op"]
            and _json_equal(rule.get("sm_attrs", {}), sm_node.get("attrs", {}))
            and all(
                pm["op"] == rule["pm_op"]
                and _json_equal(pm.get("attrs", {}), rule.get("pm_attrs", {}))
                for pm in pm_nodes
            )
        ]
        actual_input_relations = [
            relation["relation"] for relation in input_relations
        ]
        candidates = [
            rule
            for rule in operator_candidates
            if rule["input_relations"] == actual_input_relations
        ]
        if len(candidates) > 1:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "certificate_bug",
                    "stage": "rule_selection",
                    "logical_id": logical_id,
                    "sm_node": deepcopy(sm_node),
                    "pm_nodes": deepcopy(pm_nodes),
                    "actual_input_relations": deepcopy(actual_input_relations),
                    "rule_candidates": [rule["name"] for rule in candidates],
                    "reason": "multiple_relation_rules_match",
                },
            }
        if not candidates:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "missing_relation_rule",
                    "stage": "rule_selection",
                    "logical_id": logical_id,
                    "sm_node": deepcopy(sm_node),
                    "pm_nodes": deepcopy(pm_nodes),
                    "expected_relation": None,
                    "actual_input_relations": deepcopy(actual_input_relations),
                    "rule_candidates": [rule["name"] for rule in operator_candidates],
                },
            }
        rule = candidates[0]
        if len(rule["output_relations"]) != len(sm_node["outs"]):
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "certificate_bug",
                    "stage": "rule_selection",
                    "logical_id": logical_id,
                    "rule": rule["name"],
                    "expected_output_arity": len(sm_node["outs"]),
                    "actual_output_arity": len(rule["output_relations"]),
                    "reason": "rule_output_arity_mismatch",
                },
            }
        premises = [relation["relation_id"] for relation in input_relations]
        for output_index, sm_tid in enumerate(sm_node["outs"]):
            transfer = rule["output_relations"][output_index]
            if "from_input" in transfer:
                output_relation = deepcopy(
                    input_relations[transfer["from_input"]]["relation"]
                )
            else:
                output_relation = deepcopy(transfer["relation"])
            pm_tids = [
                {"rank": pm["rank"], "tid": pm["outs"][output_index]}
                for pm in pm_nodes
            ]
            mapping_error = _relation_mapping_error(
                output_relation, pm_tids, job["num_ranks"]
            )
            if mapping_error is not None:
                return {
                    "schema_version": 1,
                    "status": "failure",
                    "failure": {
                        "category": "certificate_bug",
                        "stage": "relation_inference",
                        "logical_id": logical_id,
                        "sm_tid": sm_tid,
                        "rule": rule["name"],
                        **mapping_error,
                    },
                }
            certificate = _relation_id(sm_tid)
            relations[sm_tid] = {
                "pm_tids": pm_tids,
                "relation": deepcopy(output_relation),
                "relation_id": _relation_id(sm_tid),
                "certificate": certificate,
                "provenance": {
                    "kind": "rule_application",
                    "rule": rule["name"],
                    "premises": premises,
                },
            }
            certificate_dag.append(
                {
                    "id": certificate,
                    "kind": "rule_application",
                    "logical_id": logical_id,
                    "output_index": output_index,
                    "rule": rule["name"],
                    "lean_theorem": rule["lean_theorem"],
                    "sm_node": deepcopy(sm_node),
                    "pm_nodes": deepcopy(pm_nodes),
                    "premises": premises,
                    "sm_tid": sm_tid,
                    "pm_tids": deepcopy(pm_tids),
                    "relation": deepcopy(output_relation),
                }
            )

    observables = []
    for observable in job["observables"]:
        if observable["sm_tid"] not in relations:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "goal_validation",
                    "sm_tid": observable["sm_tid"],
                    "pm_tids": deepcopy(observable["pm_tids"]),
                    "reason": "observable_tensor_relation_not_inferred",
                },
            }
        inferred = relations[observable["sm_tid"]]
        if inferred["pm_tids"] != observable["pm_tids"]:
            expected_pm_tids = deepcopy(observable["pm_tids"])
            actual_pm_tids = deepcopy(inferred["pm_tids"])
            mismatch = next(
                (
                    (expected, actual)
                    for expected, actual in zip(expected_pm_tids, actual_pm_tids)
                    if expected != actual
                ),
                None,
            )
            if mismatch is None:
                expected = expected_pm_tids[len(actual_pm_tids)] if len(expected_pm_tids) > len(actual_pm_tids) else None
                actual = actual_pm_tids[len(expected_pm_tids)] if len(actual_pm_tids) > len(expected_pm_tids) else None
            else:
                expected, actual = mismatch
            if expected is not None:
                rank = expected["rank"]
            elif actual is not None:
                rank = actual["rank"]
            else:
                raise AssertionError("mismatched PM mappings had no differing entry")
            counterexample = {
                "rank": rank,
                "expected_tid": None if expected is None else expected["tid"],
                "actual_tid": None if actual is None else actual["tid"],
            }
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "false_goal",
                    "stage": "goal_validation",
                    "sm_tid": observable["sm_tid"],
                    "expected_pm_tids": expected_pm_tids,
                    "actual_pm_tids": actual_pm_tids,
                    "expected_relation": observable.get("relation"),
                    "actual_inferred_relation": deepcopy(inferred["relation"]),
                    "counterexample": counterexample,
                },
            }
        expected_relation = observable.get("relation")
        if expected_relation is not None and expected_relation != inferred["relation"]:
            return {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "false_goal",
                    "stage": "goal_validation",
                    "sm_tid": observable["sm_tid"],
                    "expected_pm_tids": deepcopy(observable["pm_tids"]),
                    "actual_pm_tids": deepcopy(inferred["pm_tids"]),
                    "expected_relation": deepcopy(expected_relation),
                    "actual_inferred_relation": deepcopy(inferred["relation"]),
                    "counterexample": {
                        "expected_relation": deepcopy(expected_relation),
                        "actual_relation": deepcopy(inferred["relation"]),
                    },
                },
            }
        observables.append(
            {
                "sm_tid": observable["sm_tid"],
                "pm_tids": deepcopy(observable["pm_tids"]),
                "relation": deepcopy(inferred["relation"]),
                "certificate": inferred["certificate"],
            }
        )
    if not observables:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "missing_input_contract",
                "stage": "goal_validation",
                "reason": "proof_job_requires_nonempty_observables",
            },
        }
    target_digest = job.get("target_manifest_sha256")
    if (
        not isinstance(target_digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", target_digest) is None
    ):
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "missing_input_contract",
                "stage": "goal_validation",
                "reason": "proof_job_requires_target_manifest_sha256",
            },
        }
    target_payload = json.dumps(
        job["observables"], sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    actual_target_digest = hashlib.sha256(target_payload).hexdigest()
    if target_digest != actual_target_digest:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": {
                "category": "ambiguous_authority",
                "stage": "goal_validation",
                "expected_target_manifest_sha256": target_digest,
                "actual_target_manifest_sha256": actual_target_digest,
                "reason": "target_manifest_digest_mismatch",
            },
        }
    certificate_failure = validate_certificate_dag(
        certificate_dag,
        observables,
        library,
        num_ranks=job["num_ranks"],
        target_manifest_sha256=target_digest,
        target_observables=job["observables"],
    )
    if certificate_failure is not None:
        return {
            "schema_version": 1,
            "status": "failure",
            "failure": certificate_failure,
        }
    return {
        "schema_version": 1,
        "status": "certificate",
        "num_ranks": job["num_ranks"],
        "target_manifest_sha256": target_digest,
        "target_observables": deepcopy(job["observables"]),
        "certificate_dag": certificate_dag,
        "observables": observables,
    }
