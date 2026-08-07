import json
from pathlib import Path

import pytest

from scripts.check_yoco_a04b_regen import compare_snapshots, extract_snapshot


ROOT = Path(__file__).resolve().parents[2]


LEAN = """/- Auto-generated -/
def sm : GraphDecl := by
  exact [
    { rank := 0, op := \"OpName.FW_x\", ins := [1], outs := [2] },
  ]
def pm : GraphDecl := by
  exact [
    { rank := 0, op := \"OpName.FW_x\", ins := [10], outs := [20] },
  ]
def smInitShapes : List (Nat × List Nat) := [(1, [4])]
def pmInitShapes : List (Nat × List Nat) := [(10, [4])]
def smInputValueClasses : List InputValueClass := [
  { source := \"getitem:root=4188:key=cu_seqlens_q\", tids := [5337, 5345] },
]
def pmInputValueClasses : List InputValueClass := [
  { source := \"getitem:root=4188:key=cu_seqlens_q\", tids := [5337, 5345] },
]
def initGoal_1 : LineageGoal :=
  { ts := 1, tsShape := [4], tps := [{ rank := 0, tid := 10 }], tpShapes := [[4]] }
def obsTids : List Nat := [2]
def goal_1 : LineageGoal :=
  { ts := 2, tsShape := [4], tps := [{ rank := 0, tid := 20 }], tpShapes := [[4]] }
def intermediateGoal_3 : LineageGoal :=
  { ts := 3, tsShape := [4], tps := [{ rank := 0, tid := 30 }], tpShapes := [[4]] }
"""


def test_snapshot_extractor_covers_all_structural_sets():
    snapshot = extract_snapshot(LEAN.encode())
    assert snapshot["ordered_nodes"]["sm"]
    assert snapshot["ordered_nodes"]["pm"]
    assert snapshot["shapes"]["sm"] == [[1, [4]]]
    assert snapshot["init_lineages"] == {"1": [[0, 10]]}
    assert snapshot["input_value_classes"]["sm"] == [
        ["getitem:root=4188:key=cu_seqlens_q", [5337, 5345]]
    ]
    assert snapshot["input_value_classes"]["pm"] == snapshot["input_value_classes"]["sm"]
    assert snapshot["final_goal_tids"] == [2]
    assert snapshot["intermediate_goal_tids"] == [3]


def test_checked_in_yoco_a04b_goal_policy_and_lineage():
    """Pins the goal policy after the CP-zigzag ownership gate.

    `goal_3` (4675) and `goal_4` (4676) stack 24 per-layer routing tensors, 12
    of which are produced after the CP2 `FW_maybe_shuffle` and are therefore
    zigzag-owned. A zigzag shard and a contiguous shard have identical shapes,
    so the emitter used to state these as ordinary dim-1 gathers — which is
    false, not merely hard. `ZigzagGoalRefutation.gatheredZigzag_ne_full`
    machine-checks the disagreement (flat index 2: 6 versus 2).

    They are now omitted from the ordinary goal set and re-emitted as
    `ZigzagLineageGoal`s where a two-shard form exists. Counting them as
    covered would overstate coverage, so they are absent here on purpose.
    """
    snapshot = extract_snapshot(
        (ROOT / "trainverify/denote/GeneratedYOCOMoE.lean").read_bytes()
    )
    assert snapshot["init_lineages"]["4691"] == [[0, 4691]]
    assert snapshot["final_goal_tids"] == [4673, 4674, 4680]
    assert 4675 not in snapshot["final_goal_tids"], "goal_3 is zigzag-owned"
    assert 4676 not in snapshot["final_goal_tids"], "goal_4 is zigzag-owned"
    # 1151 before the gate; the 505 zigzag-owned intermediates are now stated
    # as ZigzagLineageGoals instead of false ordinary gathers.
    assert len(snapshot["intermediate_goal_tids"]) == 646
    assert 4680 not in snapshot["intermediate_goal_tids"]


def test_checker_detects_byte_mutation_even_when_structure_matches(tmp_path: Path):
    manifest = {
        "schema_version": 3,
        "artifact_sha256": {
            "nnscaler_dp_solver.so": "a" * 64,
            "comp_profile.json": "b" * 64,
        },
        "generated_lean_sha256": "unused",
    }
    expected = tmp_path / "expected.lean"
    actual = tmp_path / "actual.lean"
    expected_manifest = tmp_path / "expected.json"
    actual_manifest = tmp_path / "actual.json"
    expected.write_bytes(LEAN.encode())
    actual.write_bytes((LEAN + "\n").encode())
    expected_manifest.write_text(json.dumps(manifest), encoding="utf-8")
    actual_manifest.write_text(json.dumps(manifest), encoding="utf-8")
    with pytest.raises(RuntimeError, match="Lean bytes"):
        compare_snapshots(expected, actual, expected_manifest, actual_manifest)
