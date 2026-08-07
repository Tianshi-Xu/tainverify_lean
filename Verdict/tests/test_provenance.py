import json
from pathlib import Path

import pytest

from Verdict.provenance import (
    ProvenanceError,
    build_manifest,
    deterministic_json_bytes,
    normalize_command,
    sha256_file,
)


def _inputs(tmp_path: Path):
    sm = tmp_path / "sm.pkl"
    pm = tmp_path / "pm.pkl"
    meta = tmp_path / "gen_args.json"
    lean = tmp_path / "Generated.lean"
    emitter = tmp_path / "graph_to_lean.py"
    for path, data in ((sm, b"sm"), (pm, b"pm"), (meta, b"{}\n"), (lean, b"def x := 1\n"), (emitter, b"# emitter\n")):
        path.write_bytes(data)
    return sm, pm, meta, lean, emitter


def test_manifest_rejects_missing_authority_revision(tmp_path):
    sm, pm, meta, lean, emitter = _inputs(tmp_path)
    with pytest.raises(ProvenanceError, match="llm_train_commit"):
        build_manifest(
            model="YOCO-MoE-A0.4B",
            sm_pkl=sm,
            pm_pkl=pm,
            metadata_files=[meta],
            llm_train_commit="",
            nnscaler_commit="1" * 40,
            emitter=emitter,
            generated_lean=lean,
            command=["graph_to_lean", "--sm-pkl", str(sm)],
            packages={},
            deduplicated_intermediate_tids=[4680],
            final_goal_tids=[1, 2, 3, 4, 4680],
            intermediate_goal_tids=[10],
        )


def test_manifest_rejects_mismatched_declared_hash(tmp_path):
    sm, pm, meta, lean, emitter = _inputs(tmp_path)
    with pytest.raises(ProvenanceError, match="sm_pkl_sha256"):
        build_manifest(
            model="YOCO-MoE-A0.4B", sm_pkl=sm, pm_pkl=pm,
            metadata_files=[meta], llm_train_commit="1" * 40,
            nnscaler_commit="2" * 40, emitter=emitter, generated_lean=lean,
            command=["graph_to_lean"], packages={},
            expected_hashes={"sm_pkl_sha256": "0" * 64},
            deduplicated_intermediate_tids=[], final_goal_tids=[], intermediate_goal_tids=[],
        )


def test_manifest_json_is_sorted_stable_and_path_independent(tmp_path):
    sm, pm, meta, lean, emitter = _inputs(tmp_path)
    kwargs = dict(
        model="YOCO-MoE-A0.4B", sm_pkl=sm, pm_pkl=pm,
        metadata_files=[meta], llm_train_commit="1" * 40,
        nnscaler_commit="2" * 40, emitter=emitter, generated_lean=lean,
        command=["graph_to_lean", "--sm-pkl", str(sm), "--pm-pkl", str(pm)],
        packages={"torch": "2", "dill": "1"},
        deduplicated_intermediate_tids=[4680],
        final_goal_tids=[5, 4, 3, 2, 1], intermediate_goal_tids=[11, 10],
    )
    manifest = build_manifest(**kwargs)
    encoded = deterministic_json_bytes(manifest)
    assert encoded.endswith(b"\n")
    assert encoded == deterministic_json_bytes(json.loads(encoded))
    assert list(json.loads(encoded)) == sorted(json.loads(encoded))
    assert str(tmp_path).encode() not in encoded
    assert manifest["sm_pkl_sha256"] == sha256_file(sm)
    assert manifest["command"] == [
        "graph_to_lean", "--sm-pkl", "$AUTHORITY_DIR/sm.pkl",
        "--pm-pkl", "$AUTHORITY_DIR/pm.pkl",
    ]
    assert manifest["final_goal_tids"] == [1, 2, 3, 4, 5]
    assert manifest["schema_version"] == 3


def test_manifest_rehashes_binary_artifacts_and_rejects_unconsumed_hashes(tmp_path):
    sm, pm, meta, lean, emitter = _inputs(tmp_path)
    binary = tmp_path / "solver.so"
    binary.write_bytes(b"\x7fELFsolver")
    def make_manifest(*, artifact_files=None, expected_hashes=None):
        return build_manifest(
            model="YOCO-MoE-A0.4B", sm_pkl=sm, pm_pkl=pm,
            metadata_files=[meta], llm_train_commit="1" * 40,
            nnscaler_commit="2" * 40, emitter=emitter, generated_lean=lean,
            command=["graph_to_lean"], packages={},
            deduplicated_intermediate_tids=[], final_goal_tids=[],
            intermediate_goal_tids=[], artifact_files=artifact_files,
            expected_hashes=expected_hashes,
        )
    digest = sha256_file(binary)
    manifest = make_manifest(
        artifact_files={"solver.so": binary},
        expected_hashes={"artifact_sha256.solver.so": digest},
    )
    assert manifest["artifact_sha256"] == {"solver.so": digest}
    with pytest.raises(ProvenanceError, match="missing expected artifact hash"):
        make_manifest(artifact_files={"solver.so": binary})
    binary.write_bytes(b"\x7fELFchanged")
    with pytest.raises(ProvenanceError, match="artifact_sha256.solver.so mismatch"):
        make_manifest(
            artifact_files={"solver.so": binary},
            expected_hashes={"artifact_sha256.solver.so": digest},
        )
    with pytest.raises(ProvenanceError, match="unconsumed expected hashes"):
        make_manifest(
            expected_hashes={"artifact_sha256.unbound.so": "0" * 64},
        )


def test_artifact_file_command_path_is_stable_across_random_stages():
    first = normalize_command([
        "graph_to_lean", "--artifact-file",
        "nnscaler_dp_solver.so=/first/.stage/authority/nnscaler_dp_solver.so",
    ])
    second = normalize_command([
        "graph_to_lean", "--artifact-file",
        "nnscaler_dp_solver.so=/second/.stage/authority/nnscaler_dp_solver.so",
    ])
    assert first == second == [
        "graph_to_lean", "--artifact-file",
        "nnscaler_dp_solver.so=$AUTHORITY_DIR/nnscaler_dp_solver.so",
    ]
    with pytest.raises(ProvenanceError, match="NAME=PATH"):
        normalize_command(["graph_to_lean", "--artifact-file", "missing-separator"])


def test_snapshot_ledger_hashes_relative_lean_paths_and_rejects_aliases(tmp_path):
    sm, pm, meta, lean, emitter = _inputs(tmp_path)
    goal = tmp_path / "Goal_1.lean"
    goal.write_text("def goal := True\n", encoding="utf-8")
    kwargs = dict(
        model="YOCO-MoE-A0.4B", sm_pkl=sm, pm_pkl=pm,
        metadata_files=[meta], llm_train_commit="1" * 40,
        nnscaler_commit="2" * 40, emitter=emitter, generated_lean=lean,
        command=[
            "graph_to_lean", "--verifier-cache-dir",
            str(tmp_path / ".random-stage" / "verifier-cache"),
        ],
        packages={}, deduplicated_intermediate_tids=[], final_goal_tids=[],
        intermediate_goal_tids=[],
    )
    manifest = build_manifest(
        **kwargs,
        snapshot_files={"Generated.lean": lean, "yoco_goals/Goal_1.lean": goal},
    )
    assert manifest["snapshot_sha256"] == {
        "Generated.lean": sha256_file(lean),
        "yoco_goals/Goal_1.lean": sha256_file(goal),
    }
    assert manifest["command"][-1] == "$OUTPUT_DIR/verifier-cache"
    for invalid in ("/absolute.lean", "../escape.lean", "a/../alias.lean", "bad.json"):
        with pytest.raises(ProvenanceError, match="invalid snapshot path"):
            build_manifest(**kwargs, snapshot_files={invalid: goal})
