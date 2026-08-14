import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from trainverify.bridge_emitter.parser import (
    GoalIR,
    LineageGoal,
    Node,
    parse_full_init_goal_ids,
    parse_lineage,
    parse_lineage_block,
    parse_nodes,
)
from trainverify.bridge_emitter.proof_compiler import (
    DiagnosticCode,
    RelationKind,
    RelationEffect,
    RuleKind,
    ProofPlanningError,
    build_default_registry,
    compile_proof_plan,
    require_supported_plan,
)
from trainverify.bridge_emitter.composer import CompositionCode, compose_full_topology
import trainverify.bridge_emitter.emit2 as emit2_module
from trainverify.bridge_emitter.emit2 import _publish_composed_source


def _goal_ir(*, sm_nodes, pm_nodes, ts=30, tps=None, replicated=False, gather_dim=0):
    tps = [(0, 40), (1, 41)] if tps is None else tps
    target_shape = [8, 4] if replicated else [4 * len(tps), 4]
    return GoalIR(
        n=7,
        sm_nodes=sm_nodes,
        pm_nodes=pm_nodes,
        sm_shapes=[(1, target_shape)],
        pm_shapes=[
            (10, target_shape if replicated else [4, 4]),
            (11, target_shape if replicated else [4, 4]),
        ],
        lineage=LineageGoal(
            ts=ts,
            tsShape=target_shape,
            tps=tps,
            tpShapes=[([8, 4] if replicated else [4, 4]) for _ in tps],
            gatherDim=gather_dim,
            replicated=replicated,
        ),
        prereqs=[],
        sm_num_ranks=1,
        pm_num_ranks=max((node.rank for node in pm_nodes), default=0) + 1,
    )


def _hidden_embedding_alltoall_ir():
    return GoalIR(
        n=7,
        sm_nodes=[Node(0, "FW_embedding", [100, 101], [102])],
        pm_nodes=[
            Node(0, "FW_embedding", [100, 201], [301]),
            Node(1, "FW_embedding", [100, 202], [302]),
            Node(0, "AllToAllPrim", [301, 302], [401], [1, 0]),
            Node(1, "AllToAllPrim", [301, 302], [402], [1, 0]),
        ],
        sm_shapes=[(100, [8]), (101, [16, 4])],
        pm_shapes=[(100, [8]), (201, [16, 2]), (202, [16, 2])],
        lineage=LineageGoal(
            ts=102,
            tsShape=[8, 4],
            tps=[(0, 401), (1, 402)],
            tpShapes=[[4, 4], [4, 4]],
            gatherDim=0,
            replicated=False,
        ),
        prereqs=[],
        sm_num_ranks=1,
        pm_num_ranks=2,
        init_lineages={
            100: LineageGoal(
                ts=100,
                tsShape=[8],
                tps=[(0, 100)],
                tpShapes=[[8]],
            ),
            101: LineageGoal(
                ts=101,
                tsShape=[16, 4],
                tps=[(0, 201), (1, 202)],
                tpShapes=[[16, 2], [16, 2]],
                gatherDim=1,
            ),
        },
        full_init_goal_ids=(100, 101),
    )


def test_parse_lineage_preserves_replicated_relation_flag():
    generated = """
def goal_7 : LineageGoal :=
  { ts := 30, tsShape := [8, 4],
    tps := [{ rank := 0, tid := 40 }, { rank := 1, tid := 41 }],
    tpShapes := [[8, 4], [8, 4]], gatherDim := 1, replicated := true }
"""
    goal = parse_lineage(generated, 7)
    assert goal.gatherDim == 1
    assert goal.replicated is True


def test_parser_preserves_full_init_membership_and_piece_order():
    goal_text = """
def goal_7_full_initGoals : List LineageGoal := initGoals
def after : Nat := 0
"""
    generated = """
def initGoal_10 : LineageGoal :=
  { ts := 10, tsShape := [8, 4],
    tps := [{ rank := 1, tid := 21 }, { rank := 0, tid := 20 }],
    tpShapes := [[8, 2], [8, 2]], gatherDim := 1 }
def initGoals : List LineageGoal := [initGoal_10]
def after : Nat := 0
"""
    assert parse_full_init_goal_ids(goal_text, generated, 7) == (10,)
    parsed = parse_lineage_block(
        generated.split("def initGoals", 1)[0], "initGoal_10"
    )
    assert parsed.tps == [(1, 21), (0, 20)]
    assert parsed.gatherDim == 1


def test_parser_consumes_reordered_node_records_fail_closed():
    block = """
def graph : GraphDecl := by
  refine { numRanks := 1, nodes := ?_, replicaGroups := [] }
  exact [
      { rank := 0, op := "OpName.FW_gelu", outs := [99], ins := [10] }
  ]
"""
    nodes = parse_nodes(block)
    assert nodes == [Node(0, "FW_gelu", [10], [99])]

    malformed = block.replace("outs := [99]", "outs := [99], mystery := 7")
    with pytest.raises(ValueError, match="unknown graph node field"):
        parse_nodes(malformed)


def test_default_registry_exposes_typed_existing_rules():
    registry = build_default_registry()
    pointwise = registry.require("FW_gelu")
    collective = registry.require("AllGatherPrim")
    multi = registry.require("BW_linear")

    assert pointwise.kind is RuleKind.POINTWISE
    assert pointwise.denote_fn == "fw_gelu"
    assert pointwise.apply_lemmas == ("applyNode_fw_gelu_out",)
    assert collective.kind is RuleKind.COLLECTIVE
    assert collective.denote_fn == "allGatherPrimDimN"
    assert multi.kind is RuleKind.MULTI_OUTPUT
    assert multi.output_count == 2
    assert multi.output_projections == (".1", ".2")


def test_compile_proof_plan_builds_graph_wide_dependency_dag():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [20]),
            Node(1, "FW_gelu", [11], [21]),
            Node(0, "AllGatherPrim", [20, 21], [40], [0]),
            Node(1, "AllGatherPrim", [20, 21], [41], [0]),
        ],
        replicated=True,
    )
    ir.pm_shapes = [(10, [4, 4]), (11, [4, 4])]

    plan = compile_proof_plan(ir, build_default_registry())

    assert plan.supported is True
    assert plan.relation.kind is RelationKind.REPLICATED
    assert plan.relation.gather_dim is None
    assert [step.step_id for step in plan.steps] == [
        "sm:0:0",
        "pm:0:0",
        "pm:1:0",
        "pm:2:0",
        "pm:3:0",
    ]
    assert plan.steps[-1].dependencies == ("pm:0:0", "pm:1:0")
    assert plan.steps[0].relation_effect is RelationEffect.PRESERVE
    assert plan.steps[-1].relation_effect is RelationEffect.COLLECTIVE
    assert plan.steps[0].rank == 0
    assert plan.steps[0].input_tids == (1,)
    assert plan.steps[0].parameters == ()
    assert plan.steps[0].denote_fn == "fw_gelu"
    assert plan.steps[0].apply_lemmas == ("applyNode_fw_gelu_out",)
    assert plan.target_steps == ("sm:0:0", "pm:2:0", "pm:3:0")


def test_compile_proof_plan_uses_replicated_relation_when_declared():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [11], [41]),
        ],
        replicated=True,
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True
    assert plan.relation.kind is RelationKind.REPLICATED


def test_compile_proof_plan_accepts_in_place_collective_over_external_input():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "AllReducePrim", [10], [10])],
        tps=[(0, 10)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True
    assert plan.target_steps == ("sm:0:0", "pm:0:0")
    assert plan.steps[-1].external_inputs == (10,)


def test_compile_proof_plan_reports_first_unsupported_node_structurally():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "FW_not_registered", [10], [40])],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    issue = plan.diagnostics[0]
    assert issue.code is DiagnosticCode.UNSUPPORTED_OPERATOR
    assert issue.side == "pm"
    assert issue.node_index == 0
    assert issue.op == "FW_not_registered"
    assert issue.output_tid == 40


def test_compile_proof_plan_reports_unsupported_before_duplicate_structure():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_not_registered", [10], [40]),
            Node(1, "FW_not_registered", [10], [40]),
        ],
        tps=[(0, 40), (1, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.diagnostics[0].code is DiagnosticCode.UNSUPPORTED_OPERATOR
    assert plan.diagnostics[0].node_index == 0


def test_compile_proof_plan_allows_equivalent_rank_insensitive_rewrite():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [10], [40]),
            Node(0, "FW_gelu", [40], [50]),
            Node(1, "FW_gelu", [40], [51]),
        ],
        tps=[(0, 50), (1, 51)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True
    assert plan.target_steps == ("sm:0:0", "pm:2:0", "pm:3:0")


def test_compile_proof_plan_binds_lineage_to_final_writer_rank():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [40], [41]),
        ],
        tps=[(0, 40), (1, 41)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_LINEAGE


def test_compile_proof_plan_rejects_duplicate_producers_fail_closed():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(0, "FW_gelu", [11], [40]),
        ],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.DUPLICATE_PRODUCER


def test_compile_proof_plan_rejects_aliasing_pointwise_rewrite():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [10]),
            Node(1, "FW_gelu", [10], [10]),
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [10], [41]),
        ],
        tps=[(0, 40), (1, 41)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.DUPLICATE_PRODUCER


def test_compile_proof_plan_rejects_cycles_fail_closed():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [41], [40]),
            Node(0, "FW_gelu", [40], [41]),
        ],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.CYCLE


def test_compile_proof_plan_rejects_future_producer_without_reordering():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [41], [40]),
            Node(0, "FW_gelu", [10], [41]),
        ],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.MISSING_PRODUCER
    assert plan.diagnostics[0].node_index == 0
    assert "no earlier producer" in plan.diagnostics[0].message


def test_compile_proof_plan_accepts_ordered_consumer_before_in_place_rewrite():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [20]),
            Node(1, "FW_gelu", [20], [21]),
            Node(0, "AllReducePrim", [20, 21], [20]),
        ],
        tps=[(0, 20), (1, 21)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True
    assert plan.steps[-1].dependencies == ("pm:0:0", "pm:1:0")


def test_compile_proof_plan_rejects_parameters_for_parameter_free_rule():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30], [99])],
        pm_nodes=[Node(0, "FW_gelu", [10], [40])],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE


@pytest.mark.parametrize(
    "bad_node",
    [
        Node(0, "BW_linear", [10, 11, 12], [40, 40]),
        Node(0, "AllToAllPrim", [10], [40], [1, 0]),
        Node(0, "AllGatherPrim", [10, 11], [40], [9]),
        Node(0, "FW_multiref", [10], [40, 42], [1]),
    ],
)
def test_compile_proof_plan_rejects_closed_signature_violations(bad_node):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[bad_node, Node(1, "FW_gelu", [11], [41])],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE


def test_compile_proof_plan_rejects_allgather_shape_mismatch():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "AllGatherPrim", [10, 11], [40], [1]),
            Node(1, "FW_gelu", [11], [41]),
        ],
        tps=[(0, 40), (1, 41)],
    )
    ir.pm_shapes = [(10, [2, 4]), (11, [3, 4])]
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert "input shapes differ" in plan.diagnostics[0].message


def test_compile_proof_plan_binds_inferred_shapes_to_lineage_declarations():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [11], [41]),
        ],
    )
    ir.pm_shapes = [(10, [3, 4]), (11, [3, 4])]
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_LINEAGE
    assert "differs from lineage declaration" in plan.diagnostics[0].message


def test_compile_proof_plan_uses_sound_sum_and_add_shapes():
    summed = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "FW_sum", [10], [40])],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(summed, build_default_registry())
    assert plan.supported is False
    assert "[1]" in plan.diagnostics[0].message

    added = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "FW_add", [10, 11], [40])],
        tps=[(0, 40)],
    )
    added.pm_shapes = [(10, [2, 1]), (11, [2, 3])]
    added.sm_shapes = [(1, [2, 1])]
    added.lineage.tsShape = [2, 1]
    added.lineage.tpShapes = [[2, 1]]
    plan = compile_proof_plan(added, build_default_registry())
    assert plan.supported is False
    assert "[2, 3]" in plan.diagnostics[0].message

    added.pm_shapes = [(10, [2, 2]), (11, [2, 3])]
    plan = compile_proof_plan(added, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert "not broadcast-compatible" in plan.diagnostics[0].message


@pytest.mark.parametrize(
    "bad_node, shapes, expected",
    [
        (Node(0, "FW_view", [10], [40], [2, 2]), None, "element count"),
        (Node(0, "FW_transpose", [10], [40], [0, 9]), None, "outside input rank"),
        (
            Node(0, "FW_linear", [10, 11], [40]),
            [(10, [2, 3]), (11, [4, 4])],
            "inner dimensions differ",
        ),
        (
            Node(0, "AllReducePrim", [10, 11], [40]),
            [(10, [2, 4]), (11, [3, 4])],
            "input shapes differ",
        ),
    ],
)
def test_compile_proof_plan_rejects_unsound_operator_shape_contracts(
    bad_node, shapes, expected
):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[bad_node],
        tps=[(0, 40)],
    )
    ir.pm_num_ranks = 2
    if shapes is not None:
        ir.pm_shapes = shapes
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert expected in plan.diagnostics[0].message


def test_compile_proof_plan_rejects_unmodelled_shape_and_offset_embedding():
    unknown = _goal_ir(
        sm_nodes=[Node(0, "FW_sum", [1], [30])],
        pm_nodes=[
            Node(0, "BW_sum", [10, 11], [20]),
            Node(0, "FW_sum", [20], [40]),
        ],
        tps=[(0, 40)],
        replicated=True,
    )
    unknown.lineage.tsShape = [1]
    unknown.lineage.tpShapes = [[1]]
    plan = compile_proof_plan(unknown, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].op == "BW_sum"
    assert "no registered shape inference" in plan.diagnostics[0].message

    offset = _goal_ir(
        sm_nodes=[Node(0, "FW_embedding", [1, 2], [30], [7])],
        pm_nodes=[Node(0, "FW_embedding", [10, 11], [40], [7])],
        tps=[(0, 40)],
        replicated=True,
    )
    offset.sm_shapes = [(1, [2]), (2, [4, 3])]
    offset.pm_shapes = [(10, [2]), (11, [4, 3])]
    offset.lineage.tsShape = [2, 3]
    offset.lineage.tpShapes = [[2, 3]]
    plan = compile_proof_plan(offset, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert "expected 0 parameters" in plan.diagnostics[0].message

    rank4 = _goal_ir(
        sm_nodes=[Node(0, "FW_linear", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_linear", [10, 11], [40])],
        tps=[(0, 40)],
        replicated=True,
    )
    rank4.sm_shapes = [(1, [2, 2, 2, 2]), (2, [3, 2])]
    rank4.pm_shapes = [(10, [2, 2, 2, 2]), (11, [3, 2])]
    rank4.lineage.tsShape = []
    rank4.lineage.tpShapes = [[]]
    plan = compile_proof_plan(rank4, build_default_registry())
    assert plan.supported is False
    assert "unsupported input/weight rank" in plan.diagnostics[0].message


@pytest.mark.parametrize(
    "mutate",
    [
        lambda ir: setattr(ir, "sm_num_ranks", 0),
        lambda ir: setattr(ir.sm_nodes[0], "rank", 9),
        lambda ir: setattr(ir.pm_nodes[0], "rank", 7),
        lambda ir: setattr(ir.lineage, "tps", [(0, 40), (0, 41)]),
        lambda ir: setattr(ir.lineage, "tps", [(0, 40), (2, 41)]),
        lambda ir: setattr(ir.lineage, "tps", [(1, 40), (0, 41)]),
        lambda ir: setattr(ir.lineage, "gatherDim", 9),
        lambda ir: setattr(ir.lineage, "tpShapes", [[3, 4], [4, 4]]),
    ],
)
def test_compile_proof_plan_rejects_invalid_rank_and_shape_contracts(mutate):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [11], [41]),
        ],
    )
    mutate(ir)
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False


def test_compile_proof_plan_rejects_duplicate_lineage_ranks_independently():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(0, "FW_gelu", [11], [41]),
        ],
        tps=[(0, 40), (0, 41)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_LINEAGE
    assert "strictly increasing" in plan.diagnostics[0].message

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [11], [41]),
        ],
        tps=[(1, 41), (0, 40)],
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert "strictly increasing" in plan.diagnostics[0].message

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_gelu", [10], [40]),
            Node(1, "FW_gelu", [11], [41]),
        ],
        tps=[(0, 40)],
        replicated=True,
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True


def test_proof_plan_json_is_byte_deterministic():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "FW_gelu", [10], [40])],
        tps=[(0, 40)],
    )
    first = compile_proof_plan(ir, build_default_registry()).to_json()
    second = compile_proof_plan(ir, build_default_registry()).to_json()
    assert first == second
    decoded = json.loads(first)
    assert decoded["schema_version"] == 1
    assert decoded["status"] == "supported"


def test_require_supported_plan_retains_structured_diagnostic():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "FW_not_registered", [10], [40])],
        tps=[(0, 40)],
    )
    with pytest.raises(ProofPlanningError) as caught:
        require_supported_plan(ir, build_default_registry())
    assert caught.value.plan.diagnostics[0].code is DiagnosticCode.UNSUPPORTED_OPERATOR
    assert "proof.unsupported-operator" in str(caught.value)


def test_generic_composer_matches_hidden_embedding_alltoall_without_fixed_tids():
    result = compose_full_topology(_hidden_embedding_alltoall_ir(), "denote.fixture")
    assert result.supported is True
    assert result.rule_id == "embedding-hidden-alltoall-two"
    assert "theorem compiled_prove_goal_7 : goal_7_stmt_full" in result.lean_source
    assert "import denote.fixture.Goal_7" in result.lean_source
    for tid in (100, 101, 102, 201, 202, 301, 302, 401, 402):
        assert str(tid) in result.lean_source
    assert result.lean_source == compose_full_topology(
        _hidden_embedding_alltoall_ir(), "denote.fixture"
    ).lean_source


def test_generic_composer_rejects_wrong_alltoall_dims_at_first_node():
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_nodes[2].params = [0, 1]
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert result.diagnostics[0].code is CompositionCode.TOPOLOGY_MISMATCH
    assert result.diagnostics[0].node_index == 2


def test_generic_composer_rejects_parameterized_sm_embedding():
    ir = _hidden_embedding_alltoall_ir()
    ir.sm_nodes[0].params = [17]
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert result.diagnostics[0].code is CompositionCode.TOPOLOGY_MISMATCH
    assert result.diagnostics[0].node_index == 0


def test_generic_composer_rejects_wrong_graph_rank_headers_and_sm_rank():
    ir = _hidden_embedding_alltoall_ir()
    ir.sm_nodes[0].rank = 9
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert result.diagnostics[0].node_index == 0

    ir = _hidden_embedding_alltoall_ir()
    ir.pm_num_ranks = 3
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert result.diagnostics[0].code is CompositionCode.TOPOLOGY_MISMATCH


def test_generic_composer_rejects_tensor_role_aliasing():
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_nodes[0].outs = [201]
    ir.pm_nodes[2].ins = [201, 302]
    ir.pm_nodes[3].ins = [201, 302]
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert "distinct tids" in result.diagnostics[0].message


def test_planner_and_composer_reject_duplicate_shape_tids():
    ir = _hidden_embedding_alltoall_ir()
    ir.sm_shapes.insert(0, (100, [999]))
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_GRAPH
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert "duplicate shape" in result.diagnostics[0].message


def test_generic_composer_rejects_nonpositive_theorem_dimensions():
    ir = _hidden_embedding_alltoall_ir()
    ir.sm_shapes[0] = (100, [0])
    ir.pm_shapes[0] = (100, [0])
    ir.lineage.tsShape = [0, 4]
    ir.lineage.tpShapes = [[0, 4], [0, 4]]
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert "positive" in result.diagnostics[0].message


def test_generic_composer_rejects_unmatched_input_init_lineage():
    ir = _hidden_embedding_alltoall_ir()
    ir.init_lineages[101].tps = [(1, 202), (0, 201)]
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert "weight InitGoal" in result.diagnostics[0].message

    ir = _hidden_embedding_alltoall_ir()
    ir.init_lineages[100].gatherDim = 9
    result = compose_full_topology(ir, "denote.fixture")
    assert result.supported is False
    assert "token InitGoal" in result.diagnostics[0].message


def test_composed_source_is_checked_before_atomic_publication(tmp_path, monkeypatch):
    output = tmp_path / "Compiled.lean"
    output.write_text("old")
    real_flock = emit2_module.fcntl.flock
    flock_operations = []

    def recording_flock(fd, operation):
        flock_operations.append(operation)
        return real_flock(fd, operation)

    monkeypatch.setattr(emit2_module.fcntl, "flock", recording_flock)

    def rejecting_checker(stage, candidate_fd):
        assert stage.read_text() == "new"
        assert output.read_text() == "old"
        raise RuntimeError("Lean rejected candidate")

    with pytest.raises(RuntimeError, match="Lean rejected"):
        _publish_composed_source("new", output, rejecting_checker)
    assert output.read_text() == "old"
    assert not list(tmp_path.glob(".proof-compiler-*"))

    def immutable_checker(stage, candidate_fd):
        assert stage.read_text() == "new"
        with pytest.raises(OSError):
            stage.unlink()
        with pytest.raises(OSError):
            stage.write_text("different-but-checkable")
        with pytest.raises(OSError):
            os.pwrite(candidate_fd, b"unchecked", 0)

    _publish_composed_source("new", output, immutable_checker)
    assert output.read_text() == "new"
    assert not list(tmp_path.glob(".proof-compiler-*"))

    output.chmod(0o600)
    output.write_text("old")

    def accepting_checker(stage, candidate_fd):
        assert stage.read_text() == "new"
        assert output.read_text() == "old"

    _publish_composed_source("new", output, accepting_checker)
    assert output.read_text() == "new"

    output.chmod(0o600)
    output.write_text("old")

    def forbidden_path_replace(*args, **kwargs):
        raise AssertionError("publication must use held-dirfd renameat2")

    monkeypatch.setattr(os, "replace", forbidden_path_replace)
    _publish_composed_source("new", output, accepting_checker)
    assert output.read_text() == "new"

    output.chmod(0o600)
    output.write_text("old")
    real_renameat2 = emit2_module._renameat2
    attacker_names = []

    def replace_anchor_then_rename(
        source_fd, source_name, target_fd, target_name, expected_identity
    ):
        os.unlink(source_name, dir_fd=source_fd)
        attacker_fd = os.open(
            source_name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL,
            0o600,
            dir_fd=source_fd,
        )
        try:
            os.write(attacker_fd, b"attacker")
        finally:
            os.close(attacker_fd)
        attacker_names.append(source_name)
        return real_renameat2(
            source_fd, source_name, target_fd, target_name, expected_identity
        )

    monkeypatch.setattr(emit2_module, "_renameat2", replace_anchor_then_rename)
    with pytest.raises(RuntimeError, match="identity changed before renameat2"):
        _publish_composed_source("new", output, accepting_checker)
    assert output.read_text() == "old"
    attacker = tmp_path / attacker_names[0]
    assert attacker.read_text() == "attacker"
    attacker.unlink()

    residue_names = []

    def rename_then_create_unrelated(
        source_fd, source_name, target_fd, target_name, expected_identity
    ):
        real_renameat2(
            source_fd, source_name, target_fd, target_name, expected_identity
        )
        residue_fd = os.open(
            source_name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL,
            0o600,
            dir_fd=source_fd,
        )
        try:
            os.write(residue_fd, b"unrelated")
        finally:
            os.close(residue_fd)
        residue_names.append(source_name)

    monkeypatch.setattr(emit2_module, "_renameat2", rename_then_create_unrelated)
    _publish_composed_source("new", output, accepting_checker)
    assert output.read_text() == "new"
    residue = tmp_path / residue_names[0]
    assert residue.read_text() == "unrelated"
    residue.unlink()
    assert flock_operations and all(
        operation == emit2_module.fcntl.LOCK_EX for operation in flock_operations
    )


def test_composed_source_replaces_final_symlink_without_following_it(tmp_path):
    victim = tmp_path / "victim.lean"
    victim.write_text("victim")
    requested = tmp_path / "requested.lean"
    requested.symlink_to(victim)

    def accepting_checker(stage, candidate_fd):
        assert stage.read_text() == "new"

    _publish_composed_source("new", requested, accepting_checker)
    assert requested.is_symlink() is False
    assert requested.read_text() == "new"
    assert victim.read_text() == "victim"


def _yoco_plan_env():
    env = os.environ.copy()
    env.update(
        BRIDGE_DENOTE_DIR="denote/yoco_goals",
        BRIDGE_GEN_FILE="GeneratedYOCOMoE.lean",
        BRIDGE_GEN_DIR="trainverify/denote",
    )
    return env


def test_plan_cli_emits_supported_goal5_json_without_writes():
    root = Path(__file__).resolve().parents[2]
    before = subprocess.run(
        ["git", "status", "--porcelain=v1"],
        cwd=root,
        check=True,
        text=True,
        capture_output=True,
    ).stdout
    result = subprocess.run(
        [
            sys.executable,
            str(root / "trainverify/bridge_emitter/plan.py"),
            "5",
            "--root",
            str(root),
            "--json",
        ],
        cwd=root,
        env=_yoco_plan_env(),
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)
    assert payload["status"] == "composable"
    assert payload["certificate_source_complete"] is True
    assert payload["kernel_checked"] is False
    assert payload["proof_complete"] is False
    assert payload["composition"]["rule_id"] == "embedding-hidden-alltoall-two"
    assert payload["goal_id"] == 5
    assert payload["steps"]
    after = subprocess.run(
        ["git", "status", "--porcelain=v1"],
        cwd=root,
        check=True,
        text=True,
        capture_output=True,
    ).stdout
    assert after == before


def test_emit2_goal5_uses_generic_composer_without_pattern_proof(tmp_path):
    root = Path(__file__).resolve().parents[2]
    output = tmp_path / "Goal5Compiled.lean"
    env = _yoco_plan_env()
    env.update(
        BRIDGE_NAMESPACE="GeneratedCompiled",
        BRIDGE_EXTRA_OPENS="TrainVerify.Denote.GeneratedGoals",
        BRIDGE_PROVE_GOAL_FMT="prove_goal_{n}",
        BRIDGE_EXTRA_IMPORTS="denote.yoco_goals.Pattern_5",
    )
    result = subprocess.run(
        [
            sys.executable,
            str(root / "trainverify/bridge_emitter/emit2.py"),
            "5",
            "--no-compile",
            "--quiet",
            "--out",
            str(output),
        ],
        cwd=root,
        env=env,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    source = output.read_text()
    assert "rule: embedding-hidden-alltoall-two" in source
    assert "theorem compiled_prove_goal_5 : goal_5_stmt_full" in source
    assert "prove_goal_5" not in source.replace("compiled_prove_goal_5", "")
    assert not (root / "trainverify/denote/yoco_goals/ProbeAuto.lean").exists()


def test_plan_cli_runtime_failure_is_json_and_exit2():
    root = Path(__file__).resolve().parents[2]
    result = subprocess.run(
        [
            sys.executable,
            str(root / "trainverify/bridge_emitter/plan.py"),
            "999999999",
            "--root",
            str(root),
            "--json",
        ],
        cwd=root,
        env=_yoco_plan_env(),
        text=True,
        capture_output=True,
    )
    assert result.returncode == 2
    payload = json.loads(result.stdout)
    assert payload["status"] == "error"
    assert payload["diagnostics"][0]["code"] == "cli.runtime"


def test_plan_cli_usage_failure_is_json_and_exit2():
    root = Path(__file__).resolve().parents[2]
    result = subprocess.run(
        [
            sys.executable,
            str(root / "trainverify/bridge_emitter/plan.py"),
            "5",
            "--json",
            "--not-an-option",
        ],
        cwd=root,
        env=_yoco_plan_env(),
        text=True,
        capture_output=True,
    )
    assert result.returncode == 2
    assert result.stderr == ""
    payload = json.loads(result.stdout)
    assert payload["status"] == "error"
    assert payload["diagnostics"][0]["code"] == "cli.usage"
