from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

from trainverify.proof_compiler import compile_job, validate_certificate_dag


def target_manifest_sha256(observables: list[dict]) -> str:
    payload = json.dumps(observables, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def replicated_provenance(source: str = "fixture") -> dict:
    return {
        "kind": "authority_input",
        "source": source,
        "authority_sha256": "a" * 64,
        "value_witness": {"kind": "same_authority_tensor", "sm_tid": 1},
        "ownership_witness": {"kind": "exact_rank_set", "ranks": [0, 1]},
    }


def authority_input_provenance(
    sm_tid: int = 1,
    pm_tids: list[dict] | None = None,
    source: str = "fixture",
) -> dict:
    mapping = pm_tids or [{"rank": 0, "tid": 11}]
    return {
        "kind": "authority_input",
        "source": source,
        "authority_sha256": "a" * 64,
        "value_witness": {
            "kind": "authority_tensor_mapping",
            "sm_tid": sm_tid,
            "pm_tids": mapping,
        },
        "ownership_witness": {
            "kind": "exact_rank_set",
            "ranks": [entry["rank"] for entry in mapping],
        },
    }


def test_unseen_dag_composes_registered_rules_into_certificate_dag() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [
            {"logical_id": "scale", "rank": 0, "op": "FW_scale", "ins": [1], "outs": [2]},
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [2], "outs": [3]},
        ],
        "pm_nodes": [
            {"logical_id": "scale", "rank": 0, "op": "FW_scale", "ins": [11], "outs": [12]},
            {"logical_id": "scale", "rank": 1, "op": "FW_scale", "ins": [21], "outs": [22]},
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [12], "outs": [13]},
            {"logical_id": "relu", "rank": 1, "op": "FW_relu", "ins": [22], "outs": [23]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
                "relation": {"kind": "replicated"},
                "provenance": replicated_provenance("toy-residual-fixture"),
            }
        ],
        "observables": [
            {"sm_tid": 3, "pm_tids": [{"rank": 0, "tid": 13}, {"rank": 1, "tid": 23}]}
        ],
    }
    job["target_manifest_sha256"] = target_manifest_sha256(job["observables"])
    rules = [
        {
            "name": "scale_preserves_replicated",
            "sm_op": "FW_scale",
            "pm_op": "FW_scale",
            "input_relations": [{"kind": "replicated"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.fw_scale_replicated",
        },
        {
            "name": "relu_preserves_replicated",
            "sm_op": "FW_relu",
            "pm_op": "FW_relu",
            "input_relations": [{"kind": "replicated"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.fw_relu_replicated",
        },
    ]

    result = compile_job(
        job,
        {
            "denotations": [
                {"op": "FW_scale", "lean_definition": "TrainVerify.Denote.fw_scale"},
                {"op": "FW_relu", "lean_definition": "TrainVerify.Denote.fw_relu"},
            ],
            "rules": rules,
        },
    )

    assert result["status"] == "certificate"
    rule_nodes = [
        node for node in result["certificate_dag"]
        if node["kind"] == "rule_application"
    ]
    assert [node["logical_id"] for node in rule_nodes] == ["scale", "relu"]
    assert next(node for node in rule_nodes if node["id"] == "rel:3")["premises"] == ["rel:2"]
    assert result["observables"] == [
        {
            "sm_tid": 3,
            "pm_tids": [{"rank": 0, "tid": 13}, {"rank": 1, "tid": 23}],
            "relation": {"kind": "replicated"},
            "certificate": "rel:3",
        }
    ]
    certificate_ids = {node["id"] for node in result["certificate_dag"]}
    assert len(certificate_ids) == len(result["certificate_dag"])
    references = {
        premise
        for node in result["certificate_dag"]
        for premise in node["premises"]
    }
    references.update(observable["certificate"] for observable in result["observables"])
    assert references <= certificate_ids


def test_missing_rule_returns_localized_structured_failure() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [11], "outs": [12]},
            {"logical_id": "relu", "rank": 1, "op": "FW_relu", "ins": [21], "outs": [22]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
                "relation": {"kind": "replicated"},
                "provenance": replicated_provenance(),
            }
        ],
        "observables": [],
    }

    result = compile_job(
        job,
        {
            "denotations": [
                {"op": "FW_relu", "lean_definition": "TrainVerify.Denote.fw_relu"},
            ],
            "rules": [],
        },
    )

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "missing_relation_rule",
            "stage": "rule_selection",
            "logical_id": "relu",
            "sm_node": job["sm_nodes"][0],
            "pm_nodes": job["pm_nodes"],
            "expected_relation": None,
            "actual_input_relations": [{"kind": "replicated"}],
            "rule_candidates": [],
        },
    }


def test_multiref_identity_cannot_establish_replication() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
                "relation": {"kind": "replicated"},
                "provenance": {
                    "kind": "identity_fanout",
                    "operator": "FW_multiref",
                },
            }
        ],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
            "expected_relation": {"kind": "replicated"},
            "actual_inferred_relation": None,
            "reason": "identity_fanout_does_not_prove_cross_rank_value_equality",
        },
    }


def test_duplicate_or_missing_pm_rank_is_ambiguous_authority() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [11], "outs": [12]},
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [21], "outs": [22]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
                "relation": {"kind": "replicated"},
                "provenance": replicated_provenance(),
            }
        ],
        "observables": [],
    }
    rules = [
        {
            "name": "relu_preserves_replicated",
            "sm_op": "FW_relu",
            "pm_op": "FW_relu",
            "input_relations": [{"kind": "replicated"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.fw_relu_replicated",
        }
    ]

    result = compile_job(
        job,
        {
            "denotations": [
                {"op": "FW_relu", "lean_definition": "TrainVerify.Denote.fw_relu"},
            ],
            "rules": rules,
        },
    )

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "logical_id": "relu",
            "expected_ranks": [0, 1],
            "actual_ranks": [0, 0],
            "reason": "pm_logical_group_must_have_exactly_one_node_per_rank",
        },
    }


def test_missing_faithful_denotation_is_unsupported_operator() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "mystery", "rank": 0, "op": "FW_mystery", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "mystery", "rank": 0, "op": "FW_mystery", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "unsupported_operator",
            "stage": "authority_validation",
            "graph": "sm",
            "logical_id": "mystery",
            "operator": "FW_mystery",
            "node": job["sm_nodes"][0],
            "reason": "missing_faithful_denotation",
        },
    }


def test_one_command_driver_is_byte_deterministic(tmp_path: Path) -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(source="cli-fixture"),
            }
        ],
        "observables": [
            {"sm_tid": 2, "pm_tids": [{"rank": 0, "tid": 12}]},
        ],
    }
    job["target_manifest_sha256"] = target_manifest_sha256(job["observables"])
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [
            {
                "name": "identity_preserves_equal",
                "sm_op": "FW_identity",
                "pm_op": "FW_identity",
                "input_relations": [{"kind": "equal"}],
                "output_relations": [{"from_input": 0}],
                "lean_theorem": "TrainVerify.Denote.fw_identity_equal",
            }
        ],
    }
    job_path = tmp_path / "job.json"
    library_path = tmp_path / "library.json"
    job_path.write_text(json.dumps(job), encoding="utf-8")
    library_path.write_text(json.dumps(library), encoding="utf-8")
    root = Path(__file__).resolve().parents[2]
    command = [
        sys.executable,
        str(root / "trainverify/scripts/proof_compile.py"),
        "--job",
        str(job_path),
        "--library",
        str(library_path),
    ]

    first = subprocess.run(command, cwd=root, text=True, capture_output=True)
    second = subprocess.run(command, cwd=root, text=True, capture_output=True)

    assert first.returncode == second.returncode == 0, first.stderr
    assert first.stdout == second.stdout
    output = json.loads(first.stdout)
    assert output["status"] == "certificate"
    assert any(
        node.get("logical_id") == "identity"
        for node in output["certificate_dag"]
    )


def test_unseeded_graph_input_is_missing_input_contract() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [99], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [199], "outs": [12]},
            {"logical_id": "relu", "rank": 1, "op": "FW_relu", "ins": [299], "outs": [22]},
        ],
        "input_relations": [],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_relu", "lean_definition": "TrainVerify.Denote.fw_relu"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "missing_input_contract",
            "stage": "relation_inference",
            "logical_id": "relu",
            "sm_tid": 99,
            "pm_tids": [{"rank": 0, "tid": 199}, {"rank": 1, "tid": 299}],
            "reason": "no_relation_for_graph_input",
        },
    }


def test_wrong_observable_mapping_is_preserved_as_false_goal() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [
            {"sm_tid": 2, "pm_tids": [{"rank": 0, "tid": 13}]},
        ],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [
            {
                "name": "identity_preserves_equal",
                "sm_op": "FW_identity",
                "pm_op": "FW_identity",
                "input_relations": [{"kind": "equal"}],
                "output_relations": [{"from_input": 0}],
                "lean_theorem": "TrainVerify.Denote.fw_identity_equal",
            }
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "false_goal",
            "stage": "goal_validation",
            "sm_tid": 2,
            "expected_pm_tids": [{"rank": 0, "tid": 13}],
            "actual_pm_tids": [{"rank": 0, "tid": 12}],
            "expected_relation": None,
            "actual_inferred_relation": {"kind": "equal"},
            "counterexample": {
                "rank": 0,
                "expected_tid": 13,
                "actual_tid": 12,
            },
        },
    }


def test_duplicate_sm_producer_is_ambiguous_authority() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "first", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
            {"logical_id": "second", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "first", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
            {"logical_id": "second", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [13]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "graph": "sm",
            "tid": 2,
            "producer_logical_ids": ["first", "second"],
            "reason": "tensor_must_have_at_most_one_producer",
        },
    }


def test_pm_node_inputs_must_match_inferred_relation_tensors() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "relu", "rank": 0, "op": "FW_relu", "ins": [11], "outs": [12]},
            {"logical_id": "relu", "rank": 1, "op": "FW_relu", "ins": [999], "outs": [22]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
                "relation": {"kind": "replicated"},
                "provenance": replicated_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_relu", "lean_definition": "TrainVerify.Denote.fw_relu"},
        ],
        "rules": [
            {
                "name": "relu_preserves_replicated",
                "sm_op": "FW_relu",
                "pm_op": "FW_relu",
                "input_relations": [{"kind": "replicated"}],
                "output_relations": [{"from_input": 0}],
                "lean_theorem": "TrainVerify.Denote.fw_relu_replicated",
            }
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "relation_inference",
            "logical_id": "relu",
            "input_index": 0,
            "sm_tid": 1,
            "expected_pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
            "actual_pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 999}],
            "reason": "pm_node_inputs_do_not_match_inferred_relation",
        },
    }


def test_multiple_matching_rules_are_certificate_bug() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    common = {
        "sm_op": "FW_identity",
        "pm_op": "FW_identity",
        "input_relations": [{"kind": "equal"}],
        "output_relations": [{"from_input": 0}],
        "lean_theorem": "TrainVerify.Denote.fw_identity_equal",
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [
            {"name": "identity_rule_a", **common},
            {"name": "identity_rule_b", **common},
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "rule_selection",
            "logical_id": "identity",
            "sm_node": job["sm_nodes"][0],
            "pm_nodes": job["pm_nodes"],
            "actual_input_relations": [{"kind": "equal"}],
            "rule_candidates": ["identity_rule_a", "identity_rule_b"],
            "reason": "multiple_relation_rules_match",
        },
    }


def test_collective_rule_can_change_relation_type() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [
            {"logical_id": "sum", "rank": 0, "op": "FW_allreduce", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "sum", "rank": 0, "op": "FW_allreduce", "ins": [11], "outs": [12]},
            {"logical_id": "sum", "rank": 1, "op": "FW_allreduce", "ins": [21], "outs": [22]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
                "relation": {"kind": "partial_reduction", "op": "sum", "parts": 2},
                "provenance": authority_input_provenance(
                    pm_tids=[{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}]
                ),
            }
        ],
        "observables": [
            {"sm_tid": 2, "pm_tids": [{"rank": 0, "tid": 12}, {"rank": 1, "tid": 22}]},
        ],
    }
    job["target_manifest_sha256"] = target_manifest_sha256(job["observables"])
    library = {
        "denotations": [
            {"op": "FW_allreduce", "lean_definition": "TrainVerify.Denote.fw_allreduce"},
        ],
        "rules": [
            {
                "name": "allreduce_completes_sum",
                "sm_op": "FW_allreduce",
                "pm_op": "FW_allreduce",
                "input_relations": [
                    {"kind": "partial_reduction", "op": "sum", "parts": 2},
                ],
                "output_relations": [
                    {"relation": {"kind": "replicated"}},
                ],
                "lean_theorem": "TrainVerify.Denote.fw_allreduce_sum_replicated",
            }
        ],
    }

    result = compile_job(job, library)

    assert result["status"] == "certificate"
    assert result["observables"][0]["relation"] == {"kind": "replicated"}
    assert next(
        node for node in result["certificate_dag"] if node["id"] == "rel:2"
    )["relation"] == {"kind": "replicated"}


def test_observable_relation_mismatch_is_false_goal() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [
            {
                "sm_tid": 2,
                "pm_tids": [{"rank": 0, "tid": 12}],
                "relation": {"kind": "contiguous_shard", "dim": 0, "parts": 1},
            },
        ],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [
            {
                "name": "identity_preserves_equal",
                "sm_op": "FW_identity",
                "pm_op": "FW_identity",
                "input_relations": [{"kind": "equal"}],
                "output_relations": [{"from_input": 0}],
                "lean_theorem": "TrainVerify.Denote.fw_identity_equal",
            }
        ],
    }

    result = compile_job(job, library)

    assert result["status"] == "failure"
    assert result["failure"] == {
        "category": "false_goal",
        "stage": "goal_validation",
        "sm_tid": 2,
        "expected_pm_tids": [{"rank": 0, "tid": 12}],
        "actual_pm_tids": [{"rank": 0, "tid": 12}],
        "expected_relation": {"kind": "contiguous_shard", "dim": 0, "parts": 1},
        "actual_inferred_relation": {"kind": "equal"},
        "counterexample": {
            "expected_relation": {"kind": "contiguous_shard", "dim": 0, "parts": 1},
            "actual_relation": {"kind": "equal"},
        },
    }


def test_unknown_relation_variant_is_ambiguous_authority() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "banana"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "sm_tid": 1,
            "relation": {"kind": "banana"},
            "reason": "invalid_relation",
            "detail": "unknown relation kind: banana",
        },
    }


def test_duplicate_input_relation_seed_is_ambiguous_authority() -> None:
    seed = {
        "sm_tid": 1,
        "pm_tids": [{"rank": 0, "tid": 11}],
        "relation": {"kind": "equal"},
        "provenance": authority_input_provenance(),
    }
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [seed, dict(seed)],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "sm_tid": 1,
            "reason": "duplicate_input_relation_seed",
        },
    }


def test_replicated_seed_requires_exact_rank_coverage() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "replicated"},
                "provenance": replicated_provenance(),
            }
        ],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "sm_tid": 1,
            "expected_ranks": [0, 1],
            "actual_ranks": [0],
            "reason": "replicated_seed_requires_exact_rank_coverage",
        },
    }


def test_extra_pm_logical_group_is_ambiguous_authority() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
            {"logical_id": "extra", "rank": 0, "op": "FW_identity", "ins": [31], "outs": [32]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "expected_sm_logical_ids": ["identity"],
            "actual_pm_logical_ids": ["extra", "identity"],
            "reason": "sm_pm_logical_groups_must_match",
        },
    }


def test_duplicate_sm_logical_id_is_ambiguous_authority() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "same", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
            {"logical_id": "same", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [3]},
        ],
        "pm_nodes": [
            {"logical_id": "same", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "logical_id": "same",
            "reason": "sm_logical_id_must_be_unique",
        },
    }


def test_seed_cannot_claim_tensor_produced_by_sm_graph() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "constant", "rank": 0, "op": "FW_constant", "ins": [], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "constant", "rank": 0, "op": "FW_constant", "ins": [], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 2,
                "pm_tids": [{"rank": 0, "tid": 12}],
                "relation": {"kind": "equal"},
                "provenance": {"kind": "authority_input", "source": "forged"},
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_constant", "lean_definition": "TrainVerify.Denote.fw_constant"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "sm_tid": 2,
            "producer_logical_id": "constant",
            "reason": "input_relation_seed_must_reference_graph_input",
        },
    }


def test_invalid_rule_output_relation_is_certificate_bug() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [
            {
                "name": "bad_rule",
                "sm_op": "FW_identity",
                "pm_op": "FW_identity",
                "input_relations": [{"kind": "equal"}],
                "output_relations": [{"relation": {"kind": "banana"}}],
                "lean_theorem": "TrainVerify.Denote.bad",
            }
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "library_validation",
            "rule": "bad_rule",
            "output_index": 0,
            "reason": "invalid_rule_output_relation",
            "detail": "unknown relation kind: banana",
        },
    }


def test_duplicate_denotation_is_certificate_bug() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.other_identity"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "library_validation",
            "operator": "FW_identity",
            "definitions": [
                "TrainVerify.Denote.fw_identity",
                "TrainVerify.Denote.other_identity",
            ],
            "reason": "duplicate_faithful_denotation",
        },
    }


def test_duplicate_rule_name_is_certificate_bug() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }
    base_rule = {
        "name": "duplicate",
        "sm_op": "FW_a",
        "pm_op": "FW_a",
        "input_relations": [],
        "output_relations": [],
        "lean_theorem": "TrainVerify.Denote.a",
    }
    library = {
        "denotations": [],
        "rules": [base_rule, {**base_rule, "sm_op": "FW_b", "pm_op": "FW_b"}],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "library_validation",
            "rule": "duplicate",
            "reason": "duplicate_rule_name",
        },
    }


def test_invalid_rule_input_relation_is_certificate_bug() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }
    library = {
        "denotations": [],
        "rules": [
            {
                "name": "bad_input",
                "sm_op": "FW_a",
                "pm_op": "FW_a",
                "input_relations": [{"kind": "banana"}],
                "output_relations": [],
                "lean_theorem": "TrainVerify.Denote.a",
            }
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "library_validation",
            "rule": "bad_input",
            "input_index": 0,
            "reason": "invalid_rule_input_relation",
            "detail": "unknown relation kind: banana",
        },
    }


def test_unsupported_job_schema_version_is_structured_failure() -> None:
    job = {
        "schema_version": 2,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "schema_validation",
            "field": "schema_version",
            "expected": 1,
            "actual": 2,
            "reason": "unsupported_job_schema_version",
        },
    }


def test_pm_input_arity_mismatch_is_structured_failure() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "logical_id": "identity",
            "rank": 0,
            "expected_input_arity": 1,
            "actual_input_arity": 0,
            "reason": "sm_pm_node_input_arity_mismatch",
        },
    }


def test_pm_output_arity_mismatch_is_structured_failure() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": []},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "logical_id": "identity",
            "rank": 0,
            "expected_output_arity": 1,
            "actual_output_arity": 0,
            "reason": "sm_pm_node_output_arity_mismatch",
        },
    }


def test_rule_output_arity_mismatch_is_certificate_bug() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [1], "outs": [2]},
        ],
        "pm_nodes": [
            {"logical_id": "identity", "rank": 0, "op": "FW_identity", "ins": [11], "outs": [12]},
        ],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "equal"},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }
    library = {
        "denotations": [
            {"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"},
        ],
        "rules": [
            {
                "name": "bad_arity",
                "sm_op": "FW_identity",
                "pm_op": "FW_identity",
                "input_relations": [{"kind": "equal"}],
                "output_relations": [],
                "lean_theorem": "TrainVerify.Denote.bad",
            }
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "rule_selection",
            "logical_id": "identity",
            "rule": "bad_arity",
            "expected_output_arity": 1,
            "actual_output_arity": 0,
            "reason": "rule_output_arity_mismatch",
        },
    }


def test_unknown_observable_tensor_is_structured_failure() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [
            {"sm_tid": 404, "pm_tids": [{"rank": 0, "tid": 405}]},
        ],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "goal_validation",
            "sm_tid": 404,
            "pm_tids": [{"rank": 0, "tid": 405}],
            "reason": "observable_tensor_relation_not_inferred",
        },
    }


def test_cli_invalid_json_is_structured_failure(tmp_path: Path) -> None:
    job_path = tmp_path / "job.json"
    library_path = tmp_path / "library.json"
    job_path.write_text("{not-json", encoding="utf-8")
    library_path.write_text("{}", encoding="utf-8")
    root = Path(__file__).resolve().parents[2]

    result = subprocess.run(
        [
            sys.executable,
            str(root / "trainverify/scripts/proof_compile.py"),
            "--job",
            str(job_path),
            "--library",
            str(library_path),
        ],
        cwd=root,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 2
    assert result.stderr == ""
    assert json.loads(result.stdout) == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "schema_validation",
            "source": "job",
            "reason": "invalid_json",
        },
    }


def test_rule_output_transfer_index_is_validated() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }
    library = {
        "denotations": [],
        "rules": [
            {
                "name": "bad_transfer",
                "sm_op": "FW_a",
                "pm_op": "FW_a",
                "input_relations": [{"kind": "equal"}],
                "output_relations": [{"from_input": 3}],
                "lean_theorem": "TrainVerify.Denote.a",
            }
        ],
    }

    result = compile_job(job, library)

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "certificate_bug",
            "stage": "library_validation",
            "rule": "bad_transfer",
            "output_index": 0,
            "reason": "invalid_rule_output_transfer",
            "detail": "from_input must index an input relation",
        },
    }


def test_num_ranks_must_be_positive() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 0,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "schema_validation",
            "field": "num_ranks",
            "actual": 0,
            "reason": "num_ranks_must_be_positive_integer",
        },
    }


def test_missing_required_job_collection_is_structured_failure() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "schema_validation",
            "field": "sm_nodes",
            "reason": "required_job_field_must_be_list",
        },
    }


def test_certificate_dag_validator_rejects_dangling_premise() -> None:
    failure = validate_certificate_dag(
        [{"id": "rel:2", "premises": ["rel:1"]}],
        [{"certificate": "rel:2"}],
    )

    assert failure == {
        "category": "certificate_bug",
        "stage": "certificate_validation",
        "certificate": "rel:2",
        "dangling_reference": "rel:1",
        "reason": "certificate_dag_reference_not_found",
    }


def test_sharded_seed_cardinality_must_match_parts() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [
            {
                "sm_tid": 1,
                "pm_tids": [{"rank": 0, "tid": 11}],
                "relation": {"kind": "contiguous_shard", "dim": 0, "parts": 2},
                "provenance": authority_input_provenance(),
            }
        ],
        "observables": [],
    }

    result = compile_job(job, {"denotations": [], "rules": []})

    assert result == {
        "schema_version": 1,
        "status": "failure",
        "failure": {
            "category": "ambiguous_authority",
            "stage": "authority_validation",
            "sm_tid": 1,
            "expected_parts": 2,
            "actual_parts": 1,
            "reason": "relation_tensor_cardinality_mismatch",
        },
    }


def _empty_job(**overrides: object) -> dict:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [],
        "pm_nodes": [],
        "input_relations": [],
        "observables": [],
    }
    job.update(overrides)
    return job


def test_missing_library_collections_are_structured_failure() -> None:
    result = compile_job(_empty_job(), {})
    assert result["status"] == "failure"
    assert result["failure"] == {
        "category": "certificate_bug",
        "stage": "schema_validation",
        "source": "library",
        "path": "rules",
        "reason": "required_field_must_be_list",
    }


def test_malformed_node_is_structured_failure() -> None:
    result = compile_job(_empty_job(sm_nodes=[{}]), {"denotations": [], "rules": []})
    assert result["status"] == "failure"
    assert result["failure"]["stage"] == "schema_validation"
    assert result["failure"]["path"] == "sm_nodes[0]"


def test_observable_relation_uses_closed_schema() -> None:
    job = _empty_job(
        input_relations=[{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
            "relation": {"kind": "equal"},
            "provenance": authority_input_provenance(),
        }],
        observables=[{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
            "relation": {"kind": "banana"},
        }],
    )
    result = compile_job(job, {"denotations": [], "rules": []})
    assert result["status"] == "failure"
    assert result["failure"]["stage"] == "schema_validation"
    assert result["failure"]["path"] == "observables[0].relation"


def test_json_booleans_are_not_integers() -> None:
    result = compile_job(_empty_job(num_ranks=True), {"denotations": [], "rules": []})
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "num_ranks_must_be_positive_integer"


def test_boolean_rule_transfer_index_is_rejected() -> None:
    library = {
        "denotations": [],
        "rules": [{
            "name": "bad_bool",
            "sm_op": "FW_a",
            "pm_op": "FW_a",
            "input_relations": [{"kind": "equal"}],
            "output_relations": [{"from_input": True}],
            "lean_theorem": "TrainVerify.Denote.a",
        }],
    }
    result = compile_job(_empty_job(), library)
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "invalid_rule_output_transfer"


def test_seed_must_be_an_actual_graph_input() -> None:
    job = _empty_job(input_relations=[{
        "sm_tid": 999,
        "pm_tids": [{"rank": 0, "tid": 1999}],
        "relation": {"kind": "equal"},
        "provenance": authority_input_provenance(
            sm_tid=999, pm_tids=[{"rank": 0, "tid": 1999}]
        ),
    }])
    result = compile_job(job, {"denotations": [], "rules": []})
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "input_relation_seed_must_reference_graph_input"


def test_certificate_dag_validator_rejects_cycle() -> None:
    failure = validate_certificate_dag(
        [
            {"id": "a", "premises": ["b"]},
            {"id": "b", "premises": ["a"]},
        ],
        [],
    )
    assert failure is not None
    assert failure["reason"] == "certificate_dag_must_be_topologically_ordered"


def test_null_lean_symbols_are_rejected() -> None:
    library = {
        "denotations": [{"op": "FW_a", "lean_definition": None}],
        "rules": [],
    }
    result = compile_job(_empty_job(), library)
    assert result["status"] == "failure"
    assert result["failure"]["path"] == "denotations[0].lean_definition"


def test_empty_proof_goal_is_rejected() -> None:
    result = compile_job(_empty_job(), {"denotations": [], "rules": []})
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "proof_job_requires_nonempty_observables"


def test_semantic_operator_attrs_participate_in_rule_selection() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [{
            "logical_id": "scale", "rank": 0, "op": "FW_scale",
            "ins": [1], "outs": [2], "attrs": {"factor": 1},
        }],
        "pm_nodes": [{
            "logical_id": "scale", "rank": 0, "op": "FW_scale",
            "ins": [11], "outs": [12], "attrs": {"factor": True},
        }],
        "input_relations": [{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
            "relation": {"kind": "equal"},
            "provenance": authority_input_provenance(),
        }],
        "observables": [{"sm_tid": 2, "pm_tids": [{"rank": 0, "tid": 12}]}],
    }
    library = {
        "denotations": [{
            "op": "FW_scale", "lean_definition": "TrainVerify.Denote.fw_scale",
        }],
        "rules": [{
            "name": "scale_two", "sm_op": "FW_scale", "pm_op": "FW_scale",
            "sm_attrs": {"factor": 1}, "pm_attrs": {"factor": 1},
            "input_relations": [{"kind": "equal"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.scale_two",
        }],
    }
    result = compile_job(job, library)
    assert result["status"] == "failure"
    assert result["failure"]["category"] == "missing_relation_rule"


def test_rule_output_relation_cardinality_is_validated() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "sm_nodes": [{
            "logical_id": "split", "rank": 0, "op": "FW_split",
            "ins": [1], "outs": [2],
        }],
        "pm_nodes": [
            {"logical_id": "split", "rank": 0, "op": "FW_split", "ins": [11], "outs": [12]},
            {"logical_id": "split", "rank": 1, "op": "FW_split", "ins": [21], "outs": [22]},
        ],
        "input_relations": [{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
            "relation": {"kind": "replicated"},
            "provenance": replicated_provenance(),
        }],
        "observables": [{
            "sm_tid": 2,
            "pm_tids": [{"rank": 0, "tid": 12}, {"rank": 1, "tid": 22}],
        }],
    }
    library = {
        "denotations": [{"op": "FW_split", "lean_definition": "TrainVerify.Denote.fw_split"}],
        "rules": [{
            "name": "bad_split", "sm_op": "FW_split", "pm_op": "FW_split",
            "input_relations": [{"kind": "replicated"}],
            "output_relations": [{
                "relation": {"kind": "contiguous_shard", "dim": 0, "parts": 1},
            }],
            "lean_theorem": "TrainVerify.Denote.bad_split",
        }],
    }
    result = compile_job(job, library)
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "relation_tensor_cardinality_mismatch"


def test_success_requires_authority_bound_target_manifest() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [{
            "logical_id": "identity", "rank": 0, "op": "FW_identity",
            "ins": [1], "outs": [2],
        }],
        "pm_nodes": [{
            "logical_id": "identity", "rank": 0, "op": "FW_identity",
            "ins": [11], "outs": [12],
        }],
        "input_relations": [{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
            "relation": {"kind": "equal"},
            "provenance": authority_input_provenance(),
        }],
        "observables": [{"sm_tid": 2, "pm_tids": [{"rank": 0, "tid": 12}]}],
    }
    library = {
        "denotations": [{
            "op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity",
        }],
        "rules": [{
            "name": "identity", "sm_op": "FW_identity", "pm_op": "FW_identity",
            "input_relations": [{"kind": "equal"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.identity",
        }],
    }

    result = compile_job(job, library)

    assert result["status"] == "failure"
    assert result["failure"] == {
        "category": "missing_input_contract",
        "stage": "goal_validation",
        "reason": "proof_job_requires_target_manifest_sha256",
    }

    job["target_manifest_sha256"] = "b" * 64
    mismatch = compile_job(job, library)
    assert mismatch["status"] == "failure"
    assert mismatch["failure"]["reason"] == "target_manifest_digest_mismatch"


def test_certificate_dag_validator_rejects_malformed_node() -> None:
    failure = validate_certificate_dag([{"id": "rel:1", "premises": []}], [])
    assert failure is not None
    assert failure["reason"] == "invalid_certificate_node_schema"


def test_certificate_dag_validator_checks_observable_payload() -> None:
    node = {
        "id": "rel:1",
        "kind": "seed_relation",
        "sm_tid": 1,
        "pm_tids": [{"rank": 0, "tid": 11}],
        "relation": {"kind": "equal"},
        "provenance": authority_input_provenance(),
        "premises": [],
    }
    observable = {
        "sm_tid": 1,
        "pm_tids": [{"rank": 0, "tid": 11}],
        "relation": {"kind": "replicated"},
        "certificate": "rel:1",
    }
    failure = validate_certificate_dag([node], [observable])
    assert failure is not None
    assert failure["reason"] == "observable_certificate_payload_mismatch"


def test_cli_json_valid_schema_invalid_has_no_traceback(tmp_path: Path) -> None:
    job_path = tmp_path / "job.json"
    library_path = tmp_path / "library.json"
    job_path.write_text(json.dumps(_empty_job(sm_nodes=[{}])), encoding="utf-8")
    library_path.write_text(json.dumps({"denotations": [], "rules": []}), encoding="utf-8")
    root = Path(__file__).resolve().parents[2]

    result = subprocess.run(
        [
            sys.executable,
            str(root / "trainverify/scripts/proof_compile.py"),
            "--job", str(job_path),
            "--library", str(library_path),
        ],
        cwd=root,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 2
    assert result.stderr == ""
    payload = json.loads(result.stdout)
    assert payload["status"] == "failure"
    assert payload["failure"]["stage"] == "schema_validation"


def test_unhashable_relation_operator_is_structured_failure() -> None:
    job = _empty_job(input_relations=[{
        "sm_tid": 1,
        "pm_tids": [{"rank": 0, "tid": 11}],
        "relation": {"kind": "partial_reduction", "op": [], "parts": 1},
        "provenance": {},
    }])
    result = compile_job(job, {"denotations": [], "rules": []})
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "invalid_relation"


def test_unhashable_replication_provenance_kind_is_structured_failure() -> None:
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "sm_nodes": [{
            "logical_id": "id", "rank": 0, "op": "FW_identity",
            "ins": [1], "outs": [2],
        }],
        "pm_nodes": [{
            "logical_id": "id", "rank": 0, "op": "FW_identity",
            "ins": [11], "outs": [12],
        }],
        "input_relations": [{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
            "relation": {"kind": "replicated"},
            "provenance": {"kind": []},
        }],
        "observables": [],
    }
    library = {
        "denotations": [{"op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity"}],
        "rules": [],
    }
    result = compile_job(job, library)
    assert result["status"] == "failure"
    assert result["failure"]["stage"] == "authority_validation"


def test_dag_validator_rechecks_replication_mapping_and_witness() -> None:
    seed = {
        "id": "rel:1", "kind": "seed_relation", "sm_tid": 1,
        "pm_tids": [{"rank": 0, "tid": 11}],
        "relation": {"kind": "replicated"},
        "provenance": {}, "premises": [],
    }
    observable = {
        "sm_tid": 1, "pm_tids": seed["pm_tids"],
        "relation": seed["relation"], "certificate": "rel:1",
    }
    failure = validate_certificate_dag([seed], [observable])
    assert failure is not None
    assert failure["reason"] == "invalid_replication_provenance"


def test_dag_validator_rechecks_rule_payload_coherence() -> None:
    seed = {
        "id": "rel:1", "kind": "seed_relation", "sm_tid": 1,
        "pm_tids": [{"rank": 0, "tid": 11}],
        "relation": {"kind": "equal"},
        "provenance": authority_input_provenance(),
        "premises": [],
    }
    bad_rule = {
        "id": "rel:2", "kind": "rule_application", "logical_id": "wrong",
        "output_index": 99, "rule": "bad", "lean_theorem": "unqualified",
        "sm_node": {
            "logical_id": "id", "rank": 0, "op": "FW_identity",
            "ins": [1], "outs": [2],
        },
        "pm_nodes": [], "premises": ["rel:1"], "sm_tid": 2,
        "pm_tids": [{"rank": 0, "tid": 12}], "relation": {"kind": "equal"},
    }
    failure = validate_certificate_dag([seed, bad_rule], [])
    assert failure is not None
    assert failure["reason"] == "incoherent_rule_application_payload"


def _identity_fixture(provenance: dict) -> tuple[dict, dict]:
    observables = [{"sm_tid": 2, "pm_tids": [{"rank": 0, "tid": 12}]}]
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "target_manifest_sha256": target_manifest_sha256(observables),
        "sm_nodes": [{
            "logical_id": "id", "rank": 0, "op": "FW_identity",
            "ins": [1], "outs": [2],
        }],
        "pm_nodes": [{
            "logical_id": "id", "rank": 0, "op": "FW_identity",
            "ins": [11], "outs": [12],
        }],
        "input_relations": [{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
            "relation": {"kind": "equal"},
            "provenance": provenance,
        }],
        "observables": observables,
    }
    library = {
        "denotations": [{
            "op": "FW_identity", "lean_definition": "TrainVerify.Denote.fw_identity",
        }],
        "rules": [{
            "name": "identity", "sm_op": "FW_identity", "pm_op": "FW_identity",
            "input_relations": [{"kind": "equal"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.identity",
        }],
    }
    return job, library


def test_nonreplicated_seed_requires_closed_provenance() -> None:
    job, library = _identity_fixture({})
    result = compile_job(job, library)
    assert result["status"] == "failure"
    assert result["failure"]["reason"] == "input_relation_seed_requires_authority_provenance"


def test_dag_validator_resolves_rule_against_semantic_library() -> None:
    provenance = {
        "kind": "authority_input",
        "source": "fixture",
        "authority_sha256": "a" * 64,
        "value_witness": {
            "kind": "authority_tensor_mapping",
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}],
        },
        "ownership_witness": {"kind": "exact_rank_set", "ranks": [0]},
    }
    job, library = _identity_fixture(provenance)
    result = compile_job(job, library)
    assert result["status"] == "certificate"
    forged_variants = []
    for mutation in ("theorem", "rule", "sm_op", "pm_op"):
        forged = json.loads(json.dumps(result["certificate_dag"]))
        if mutation == "theorem":
            forged[1]["lean_theorem"] = "Attacker.Forged.theorem"
        elif mutation == "rule":
            forged[1]["rule"] = "forged_rule"
        elif mutation == "sm_op":
            forged[1]["sm_node"]["op"] = "FW_forged"
        else:
            forged[1]["pm_nodes"][0]["op"] = "FW_forged"
        forged_variants.append(forged)
    for forged in forged_variants:
        failure = validate_certificate_dag(forged, result["observables"], library)
        assert failure is not None
        assert failure["reason"] == "rule_application_not_in_semantic_library"


def test_cli_rejects_duplicate_keys_and_nonfinite_numbers(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[2]
    library_path = tmp_path / "library.json"
    library_path.write_text(json.dumps({"denotations": [], "rules": []}), encoding="utf-8")
    cases = [
        '{"schema_version":1,"num_ranks":999,"num_ranks":1,"sm_nodes":[],"pm_nodes":[],"input_relations":[],"observables":[]}',
        '{"schema_version":1,"num_ranks":1,"sm_nodes":[],"pm_nodes":[],"input_relations":[],"observables":[],"extra":NaN}',
    ]
    for index, payload in enumerate(cases):
        job_path = tmp_path / f"job-{index}.json"
        job_path.write_text(payload, encoding="utf-8")
        result = subprocess.run(
            [sys.executable, str(root / "trainverify/scripts/proof_compile.py"),
             "--job", str(job_path), "--library", str(library_path)],
            cwd=root, text=True, capture_output=True,
        )
        assert result.returncode == 2
        assert result.stderr == ""
        assert json.loads(result.stdout)["failure"]["reason"] == "invalid_json"


def test_dag_validator_requires_and_checks_authority_context() -> None:
    observables = [{
        "sm_tid": 2,
        "pm_tids": [{"rank": 0, "tid": 12}, {"rank": 1, "tid": 22}],
    }]
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "target_manifest_sha256": target_manifest_sha256(observables),
        "sm_nodes": [{
            "logical_id": "id", "rank": 0, "op": "FW_id",
            "ins": [1], "outs": [2],
        }],
        "pm_nodes": [
            {"logical_id": "id", "rank": 0, "op": "FW_id", "ins": [11], "outs": [12]},
            {"logical_id": "id", "rank": 1, "op": "FW_id", "ins": [21], "outs": [22]},
        ],
        "input_relations": [{
            "sm_tid": 1,
            "pm_tids": [{"rank": 0, "tid": 11}, {"rank": 1, "tid": 21}],
            "relation": {"kind": "replicated"},
            "provenance": replicated_provenance(),
        }],
        "observables": observables,
    }
    library = {
        "denotations": [{"op": "FW_id", "lean_definition": "TV.D.id"}],
        "rules": [{
            "name": "id", "sm_op": "FW_id", "pm_op": "FW_id",
            "input_relations": [{"kind": "replicated"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TV.T.id",
        }],
    }
    result = compile_job(job, library)
    assert result["status"] == "certificate"

    missing_context = validate_certificate_dag(
        result["certificate_dag"], result["observables"], library
    )
    assert missing_context is not None
    assert missing_context["reason"] == "certificate_authority_context_required"

    target_shrink = validate_certificate_dag(
        result["certificate_dag"], [], library,
        num_ranks=2,
        target_manifest_sha256=job["target_manifest_sha256"],
        target_observables=job["observables"],
    )
    assert target_shrink is not None
    assert target_shrink["reason"] == "certificate_observables_do_not_match_target_manifest"

    shrunk_dag = json.loads(json.dumps(result["certificate_dag"]))
    shrunk_observables = json.loads(json.dumps(result["observables"]))
    for node in shrunk_dag:
        node["pm_tids"] = node["pm_tids"][:1]
        if node["kind"] == "seed_relation":
            node["provenance"]["ownership_witness"]["ranks"] = [0]
        else:
            node["pm_nodes"] = node["pm_nodes"][:1]
    for observable in shrunk_observables:
        observable["pm_tids"] = observable["pm_tids"][:1]
    rank_shrink = validate_certificate_dag(
        shrunk_dag, shrunk_observables, library,
        num_ranks=2,
        target_manifest_sha256=job["target_manifest_sha256"],
        target_observables=job["observables"],
    )
    assert rank_shrink is not None
    assert rank_shrink["reason"] in {
        "invalid_relation_mapping", "incoherent_rule_application_payload"
    }
