import json
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

import trainverify.bridge_emitter.composer as composer_module
import trainverify.bridge_emitter.emit2 as emit2_module
import trainverify.bridge_emitter.parser as parser_module
from trainverify.bridge_emitter.composer import (
    CompositionCode,
    compose_closed_dependent_chain,
    compose_full_topology,
    render_closed_attention_segment,
    render_closed_binary_segment,
    render_closed_float_segment,
    render_closed_full_producer_to_segment,
    render_closed_initial_component,
    render_closed_linear_segment,
    render_closed_mixed_moe_segment,
    render_closed_multiref_segment,
    render_closed_relation_declarations,
    render_closed_rms_norm_segment,
    render_closed_rms_shuffle_segment,
    render_closed_rotary_segment,
    render_closed_segment,
    render_closed_unary_segment,
)
from trainverify.bridge_emitter.emit2 import _publish_composed_source
from trainverify.bridge_emitter.parser import (
    GoalIR,
    LineageGoal,
    Node,
    load_goal_ir,
    parse_full_init_goal_ids,
    parse_lineage,
    parse_lineage_block,
    parse_nodes,
)
from trainverify.bridge_emitter.proof_compiler import (
    DiagnosticCode,
    ProofPlanningError,
    RelationEffect,
    RelationKind,
    RuleKind,
    build_default_registry,
    compile_proof_plan,
    require_supported_plan,
)
from trainverify.bridge_emitter.relation_compiler import (
    FrontierOrdinaryMoECertificate,
    FrontierZigzagFullMoECertificate,
    RelationCompositionError,
    RelationFactSpec,
    advance_flatten_3d_relation_frontiers,
    advance_float_relation_frontiers,
    advance_identity_view_relation_frontiers,
    advance_linear_relation_frontiers,
    advance_per_head_linear_relation_frontiers,
    advance_rms_norm_relation_frontiers,
    advance_to_relation_frontiers,
    build_add_relations,
    build_atomic_schedule,
    build_attention_output_unary_relations,
    build_attention_relations,
    build_certificate_transition_specs,
    build_chunk_reconstruction_relations,
    build_closed_dependent_chain_plan,
    build_exact_node_coverage_plan,
    build_indexed_stack_layer_relations,
    build_ordinary_attention_v_relations,
    build_ordinary_rotary_relations,
    build_rms_norm_relations,
    build_router_input_checkpoints,
    build_synchronized_transition_specs,
    build_transition_dependency_plan,
    build_zigzag_attention_kv_relations,
    build_zigzag_attention_q_relations,
    compile_relation_plan,
    deduplicate_relation_frontiers,
    expand_add_relation_frontiers,
    expand_attention_relation_frontiers,
    expand_mul_relation_frontiers,
    expand_ordinary_moe_relation_frontiers,
    expand_pointwise_relation_frontiers,
    expand_rotary_relation_frontiers,
    expand_topk_routing_relation_frontiers,
    match_indexed_stack_gather_two_rank,
    match_inner_chunk_ce_projection_gather_two_rank,
    materialize_closed_relation_facts,
    normalize_relation_frontiers,
    peel_multiref_relation_frontiers,
    resolve_zigzag_metadata_regions,
)


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


def test_fw_float_has_typed_identity_and_shape_preserving_certificate():
    registry = build_default_registry()
    rule = registry.require("FW_float")
    assert rule.kind is RuleKind.POINTWISE
    assert rule.input_count == 1
    assert rule.parameter_count == 0
    assert rule.denote_fn == "id"
    assert rule.apply_lemmas == ("applyNode_fw_float_out",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_float", [1], [30])],
        pm_nodes=[Node(0, "FW_float", [10], [40])],
        tps=[(0, 40)],
    )
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True
    assert [step.op for step in plan.steps] == ["FW_float", "FW_float"]
    assert all(step.denote_fn == "id" for step in plan.steps)


def test_fw_rms_norm_has_typed_rule_and_validates_weight_shape():
    registry = build_default_registry()
    rule = registry.require("FW_rms_norm")
    assert rule.input_count == 2
    assert rule.parameter_count == 0
    assert rule.denote_fn == "fw_rms_norm"
    assert rule.apply_lemmas == ("applyNode_fw_rms_norm_out_1p",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_rms_norm", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_rms_norm", [10, 11], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [8])]
    ir.pm_shapes = [(10, [4, 8]), (11, [8])]
    ir.lineage.tsShape = [4, 8]
    ir.lineage.tpShapes = [[4, 8]]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True

    ir.pm_shapes = [(10, [4, 8]), (11, [7])]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert "RMSNorm weight shape" in plan.diagnostics[0].message


def test_per_head_linear_has_typed_rule_and_exact_shape_contract():
    registry = build_default_registry()
    rule = registry.require("FW_per_head_mix_precision_linear")
    assert rule.input_count == 2
    assert rule.denote_fn == "fw_per_head_linear"
    assert rule.apply_lemmas == ("applyNode_fw_per_head_mix_precision_linear_out",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_per_head_mix_precision_linear", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_per_head_mix_precision_linear", [10, 11], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [2, 3, 8])]
    ir.pm_shapes = [(10, [4, 8]), (11, [2, 3, 8])]
    ir.lineage.tsShape = [4, 2, 3]
    ir.lineage.tpShapes = [[4, 2, 3]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_shapes = [(10, [4, 8]), (11, [2, 3, 7])]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "per-head linear inner dimensions differ" in plan.diagnostics[0].message


def test_rotary_embedding_tracks_distinct_output_shapes_and_typed_projections():
    registry = build_default_registry()
    rule = registry.require("FW_rotary_embedding")
    assert rule.kind is RuleKind.MULTI_OUTPUT
    assert rule.input_count == 4
    assert rule.output_count == 2
    assert rule.parameter_count == 2
    assert rule.output_projections == (".1", ".2")

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_rotary_embedding", [1, 2, 3, 4], [30, 31], [16, 4])],
        pm_nodes=[Node(0, "FW_rotary_embedding", [10, 11, 12, 13], [40, 41], [16, 4])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4096, 64]), (2, [4]), (3, [4, 16, 64]), (4, [4, 4, 64])]
    ir.pm_shapes = [(10, [4096, 64]), (11, [4]), (12, [4, 16, 64]), (13, [4, 4, 64])]
    ir.lineage.tsShape = [4, 16, 64]
    ir.lineage.tpShapes = [[4, 16, 64]]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True
    sm_steps = [step for step in plan.steps if step.side == "sm"]
    assert [step.output_projection for step in sm_steps] == [".1"]

    ir.pm_nodes[0].params = [0, 4]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "positive head counts" in plan.diagnostics[0].message


def test_sliding_window_attention_tracks_only_semantically_written_output():
    registry = build_default_registry()
    rule = registry.require("FW_attn_sliding_window")
    assert rule.input_count == 5
    assert rule.parameter_count == 6
    assert rule.produced_output_indices == (0,)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_attn_sliding_window", [1, 2, 3, 4, 5], [30, 31], [16, 4, 64, 64, 1, 512])],
        pm_nodes=[Node(0, "FW_attn_sliding_window", [10, 11, 12, 13, 14], [40, 41], [16, 4, 64, 64, 1, 512])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 16, 64]), (2, [4, 4, 64]), (3, [4, 4, 64]), (4, [5]), (5, [5])]
    ir.pm_shapes = [(10, [4, 16, 64]), (11, [4, 4, 64]), (12, [4, 4, 64]), (13, [5]), (14, [5])]
    ir.lineage.tsShape = [4, 16, 64]
    ir.lineage.tpShapes = [[4, 16, 64]]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True
    assert all(step.output_index == 0 for step in plan.steps)

    ir.lineage.ts = 31
    ir.lineage.tps = [(0, 41)]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert plan.diagnostics[0].code in {DiagnosticCode.MISSING_PRODUCER, DiagnosticCode.INVALID_LINEAGE}


def test_fw_reshape_uses_params_aware_view_contract():
    registry = build_default_registry()
    rule = registry.require("FW_reshape")
    assert rule.input_count == 1
    assert rule.min_parameter_count == 1
    assert rule.denote_fn == "fw_view"
    assert rule.apply_lemmas == ("applyNode_fw_reshape_out",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_reshape", [1], [30], [2, 8])],
        pm_nodes=[Node(0, "FW_reshape", [10], [40], [2, 8])],
        tps=[(0, 40)],
    )
    ir.lineage.tsShape = [2, 8]
    ir.lineage.tpShapes = [[2, 8]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_nodes[0].params = [3, 8]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "reshape changes element count" in plan.diagnostics[0].message


def test_mix_precision_linear_is_typed_as_linear_with_exact_shape():
    registry = build_default_registry()
    rule = registry.require("FW_mix_precision_linear")
    assert rule.input_count == 2
    assert rule.denote_fn == "fw_linear"
    assert rule.apply_lemmas == ("applyNode_fw_mix_precision_linear_out_1p",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_mix_precision_linear", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_mix_precision_linear", [10, 11], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [6, 8])]
    ir.pm_shapes = [(10, [4, 8]), (11, [6, 8])]
    ir.lineage.tsShape = [4, 6]
    ir.lineage.tpShapes = [[4, 6]]
    assert compile_proof_plan(ir, registry).supported is True


def test_norm_linear_has_distinct_typed_identity_and_linear_shape():
    registry = build_default_registry()
    rule = registry.require("FW_norm_linear")
    assert rule.denote_fn == "fw_norm_linear"
    assert rule.apply_lemmas == ("applyNode_fw_norm_linear_out",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_norm_linear", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_norm_linear", [10, 11], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [6, 8])]
    ir.pm_shapes = [(10, [4, 8]), (11, [6, 8])]
    ir.lineage.tsShape = [4, 6]
    ir.lineage.tpShapes = [[4, 6]]
    assert compile_proof_plan(ir, registry).supported is True


def test_topk_routing_uses_logits_shape_for_all_three_outputs():
    registry = build_default_registry()
    rule = registry.require("FW_topk_routing")
    assert rule.output_count == 3
    assert rule.allowed_parameter_counts == (1, 2)
    assert rule.output_projections == (".1", ".2.1", ".2.2")

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_topk_routing", [1], [30, 31, 32], [8])],
        pm_nodes=[Node(0, "FW_topk_routing", [10], [40, 41, 42], [8, 1])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 64])]
    ir.pm_shapes = [(10, [4, 64])]
    ir.lineage.tsShape = [4, 64]
    ir.lineage.tpShapes = [[4, 64]]
    assert compile_proof_plan(ir, registry).supported is True


def test_all2all_moe_gmm_uses_input_hidden_shape_not_w2_last_dim():
    registry = build_default_registry()
    rule = registry.require("FW_all2all_moe_gmm")
    assert rule.input_count == 5
    assert rule.allowed_parameter_counts == (4, 5)
    assert rule.denote_fn == "fw_all2all_moe_gmm"

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_all2all_moe_gmm", [1, 2, 3, 4, 5], [30], [64, 0, 64, 8])],
        pm_nodes=[Node(0, "FW_all2all_moe_gmm", [10, 11, 12, 13, 14], [40], [64, 0, 64, 8])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [4, 64]), (3, [4, 64]), (4, [64, 12, 8]), (5, [64, 8, 6])]
    ir.pm_shapes = [(10, [4, 8]), (11, [4, 64]), (12, [4, 64]), (13, [64, 12, 8]), (14, [64, 8, 6])]
    ir.lineage.tsShape = [4, 8]
    ir.lineage.tpShapes = [[4, 8]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_shapes[1] = (11, [4, 32])
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "routing shapes" in plan.diagnostics[0].message


def test_sigmoid_has_typed_shape_preserving_rule():
    registry = build_default_registry()
    rule = registry.require("FW_sigmoid")
    assert rule.input_count == 1
    assert rule.denote_fn == "fw_sigmoid"
    assert rule.apply_lemmas == ("applyNode_fw_sigmoid_out_1p",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_sigmoid", [1], [30])],
        pm_nodes=[Node(0, "FW_sigmoid", [10], [40])],
        tps=[(0, 40)],
    )
    assert compile_proof_plan(ir, registry).supported is True


def test_swiglu_requires_equal_gate_and_up_shapes():
    registry = build_default_registry()
    rule = registry.require("FW_swiglu")
    assert rule.input_count == 2
    assert rule.denote_fn == "fw_swiglu"

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_swiglu", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_swiglu", [10, 11], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [4, 8])]
    ir.pm_shapes = [(10, [4, 8]), (11, [4, 8])]
    ir.lineage.tsShape = [4, 8]
    ir.lineage.tpShapes = [[4, 8]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_shapes[1] = (11, [4, 7])
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "gate/up shapes differ" in plan.diagnostics[0].message


def test_fw_mul_uses_broadcast_shape_and_distinct_semantic_identity():
    registry = build_default_registry()
    rule = registry.require("FW_mul")
    assert rule.input_count == 2
    assert rule.denote_fn == "elemwiseMul"

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_mul", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_mul", [10, 11], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 1]), (2, [4, 8])]
    ir.pm_shapes = [(10, [4, 1]), (11, [4, 8])]
    ir.lineage.tsShape = [4, 8]
    ir.lineage.tpShapes = [[4, 8]]
    assert compile_proof_plan(ir, registry).supported is True


def test_faithful_shuffle_emits_parameter_resolved_relation_effects():
    registry = build_default_registry()
    rule = registry.require("FW_maybe_shuffle")
    assert rule.input_count == 2
    assert rule.parameter_count == 2
    assert rule.denote_fn == "applyNodeFaithfulShuffleValue"

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_maybe_shuffle", [1, 2], [30], [1, 0])],
        pm_nodes=[Node(0, "FW_maybe_shuffle", [10, 11], [40], [2, 0])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 4]), (2, [2])]
    ir.pm_shapes = [(10, [4, 4]), (11, [2])]
    ir.pm_num_ranks = 2
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True
    effects = {(step.side, step.op): step.relation_effect for step in plan.steps}
    assert effects[("sm", "FW_maybe_shuffle")] is RelationEffect.PRESERVE
    assert effects[("pm", "FW_maybe_shuffle")] is RelationEffect.ORDINARY_TO_ZIGZAG

    ir.pm_nodes[0].params = [2, 2]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "cpRank" in plan.diagnostics[0].message


def test_fw_to_has_typed_identity_shape_preserving_rule():
    registry = build_default_registry()
    rule = registry.require("FW_to")
    assert rule.input_count == 1
    assert rule.denote_fn == "id"
    assert rule.apply_lemmas == ("applyNode_fw_to_out",)

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_to", [1], [30])],
        pm_nodes=[Node(0, "FW_to", [10], [40])],
        tps=[(0, 40)],
    )
    assert compile_proof_plan(ir, registry).supported is True


def test_faithful_zigzag_attention_preserves_zigzag_q_layout_and_ignores_aux_out():
    registry = build_default_registry()
    rule = registry.require("FW_attn_zigzag")
    assert rule.allowed_output_counts == (1, 2)
    assert rule.produced_output_indices == (0,)
    assert rule.denote_fn == "applyNodeFaithfulZigzagAttnValue"

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_attn_zigzag", [1, 2, 3, 4, 5], [30, 31], [16, 4, 64, 64, 1, 0])],
        pm_nodes=[Node(0, "FW_attn_zigzag", [10, 11, 12, 13, 14], [40], [16, 4, 64, 64, 1, 0])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [4, 16, 64]), (2, [4, 4, 64]), (3, [4, 4, 64]), (4, [2]), (5, [2])]
    ir.pm_shapes = [(10, [4, 16, 64]), (11, [4, 4, 64]), (12, [4, 4, 64]), (13, [2]), (14, [2])]
    ir.lineage.tsShape = [4, 16, 64]
    ir.lineage.tpShapes = [[4, 16, 64]]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True
    assert all(step.relation_effect is RelationEffect.ZIGZAG_PRESERVE for step in plan.steps)

    ir.lineage.ts = 31
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.MISSING_PRODUCER


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


def test_duplicate_writer_accepts_only_structurally_equal_ancestry():
    registry = build_default_registry()
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "FW_multiref", [10], [20], [1]),
            Node(1, "FW_multiref", [10], [21], [1]),
            Node(0, "FW_gelu", [20], [40]),
            Node(1, "FW_gelu", [21], [40]),
        ],
        tps=[(1, 40)],
    )
    ir.pm_num_ranks = 2
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_shapes.append((12, [4, 4]))
    ir.pm_nodes[1].ins = [12]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.DUPLICATE_PRODUCER


def test_real_goals_compile_fail_closed_relation_plans(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    registry = build_default_registry()
    for goal_id in (1, 2, 3, 4):
        ir = load_goal_ir(goal_id, str(root))
        proof = compile_proof_plan(ir, registry)
        relation = compile_relation_plan(ir, proof)
        assert relation.family == ("ce-projection-gather" if goal_id in (1, 2) else "indexed-stack-gather")
        assert relation.complete is False
        assert relation.schema_version == 6
        assert relation.coverage_plan is not None
        assert relation.coverage_plan.complete is True
        assert relation.dependency_plan is not None
        assert relation.dependency_plan.order
        assert relation.atomic_schedule is not None
        assert relation.atomic_schedule.complete is True
        assert relation.dependent_chain_plan is not None
        assert relation.dependent_chain_plan.complete is True
        assert relation.graph_coverage_complete is False
        assert relation.composer_registered is False
        assert relation.unresolved_frontiers == ()
        assert relation.unresolved_layouts == ()
        assert relation.unresolved_side_conditions == ()



def test_ce_terminal_relation_plan_normalizes_the_backbone(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    by_id = {step.step_id: step for step in proof.steps}
    assert len(relation.certificates) > 1
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_rms_norm" for binding in frontier)
        for frontier in relation.unresolved_frontiers
    )


def test_ce_terminal_unshuffle_discharges_cu_obligation_from_public_contract(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    cert = next(item for item in relation.certificates if getattr(item, "rule_id", "") == "zigzag-to-ordinary-unshuffle-two-rank")
    assert cert.metadata_binding == "init:6252"
    assert cert.lean_theorem == "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.to_gather2_unshuffle"
    assert relation.unresolved_side_conditions == ()
    contract = next(item for item in relation.certificates if getattr(item, "rule_id", "") == "packed-cu-contract-decode-single")
    assert (contract.side, contract.tid, contract.total_tokens, contract.num_ranks) == ("pm", 6252, 4096, 2)
    assert contract.lean_theorem == "TrainVerify.Denote.PackedCuSeqlensWF.decoded_single"
    assert relation.unresolved_frontiers == ()
    assert relation.unresolved_layouts == ()
    assert len(relation.zigzag_regions) == 1

def test_real_loss_goals_share_generic_ce_projection_gather_terminal(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    registry = build_default_registry()
    certificates = []
    for goal_id in (1, 2):
        ir = load_goal_ir(goal_id, str(root))
        plan = compile_proof_plan(ir, registry)
        certificates.append(match_inner_chunk_ce_projection_gather_two_rank(ir, plan))
    assert [item.output_projection for item in certificates] == [".fst", ".snd"]
    assert all(item.rule_id == "inner-chunk-ce-projection-gather-two-rank" for item in certificates)
    assert all((item.full_rows, item.shard_rows) == (4096, 2048) for item in certificates)
    assert "fst_allGather0" in certificates[0].lean_theorem
    assert "snd_allGatherDim0" in certificates[1].lean_theorem
    assert certificates[1].label_independence_theorem is not None


def test_ce_projection_gather_terminal_rejects_mixed_projection(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    steps = list(plan.steps)
    pm_piece = next(i for i, step in enumerate(steps) if step.step_id == "pm:2021:0")
    steps[pm_piece] = replace(steps[pm_piece], output_projection=".snd")
    with pytest.raises(RelationCompositionError, match="projection"):
        match_inner_chunk_ce_projection_gather_two_rank(ir, replace(plan, steps=tuple(steps)))


def test_generic_linear_frontier_pass_checks_replicated_weight_and_layout(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=('alias', 'rms_norm', 'float', 'identity_view', 'add'),
    )
    certs, frontiers = advance_linear_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 552
    assert sum(item.relation_kind == "ordinary" for item in certs) == 420
    assert sum(item.relation_kind == "zigzag" for item in certs) == 132
    assert all(item.input_features == item.weight_input_features for item in certs)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_mix_precision_linear" for binding in frontier)
        for frontier in frontiers
    )


def test_ordinary_moe_uses_full_expert_semantics_without_disjoint_assumptions(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "to", "per_head_linear", "mul", "pointwise", "add"),
        deduplicate_each_round=True,
    )
    all_certs, conditions, frontiers, layouts = expand_ordinary_moe_relation_frontiers(
        proof, staged_frontiers, staged_layouts, ir
    )
    certs = [item for item in all_certs if item.relation_kind == "ordinary"]
    zigzag_certs = [item for item in all_certs if item.relation_kind == "zigzag"]
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 12
    assert conditions == ()
    assert all(item.relation_kind == "ordinary" for item in certs)
    assert all(
        item.lean_theorem == "TrainVerify.Denote.GeneratedPatterns.fw_all2all_moe_gmm_full_split_commute_2"
        for item in certs
    )
    assert len(zigzag_certs) == 11
    assert all(
        item.lean_theorem
        == "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.all2all_moe_gmm_full_1x2"
        for item in zigzag_certs
    )
    assert len(frontiers) == len(staged_frontiers) + 2 * len(all_certs)
    assert len(layouts) == len(frontiers)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_all2all_moe_gmm" for binding in frontier)
        and layout == "ordinary"
        for frontier, layout in zip(frontiers, layouts)
    )
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_all2all_moe_gmm" for binding in frontier)
        for frontier in frontiers
    )


def test_generic_pointwise_sigmoid_and_swiglu_are_layout_typed(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "to", "per_head_linear", "mul", "add"),
        deduplicate_each_round=True,
    )
    certs, frontiers, layouts = expand_pointwise_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 46
    assert sum(item.operator == "FW_sigmoid" for item in certs) == 23
    assert sum(item.operator == "FW_swiglu" for item in certs) == 23
    assert sum(len(item.input_step_triples) for item in certs) == 69
    assert len(layouts) == len(frontiers)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op in {"FW_sigmoid", "FW_swiglu"} for binding in frontier)
        for frontier in frontiers
    )


def test_generic_broadcast_mul_expands_two_layout_typed_inputs(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "to", "per_head_linear", "add"),
        deduplicate_each_round=True,
    )
    certs, frontiers, layouts = expand_mul_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 23
    assert sum(item.relation_kind == "ordinary" for item in certs) == 12
    assert sum(item.relation_kind == "zigzag" for item in certs) == 11
    assert len(frontiers) == len(staged_frontiers) + len(certs)
    assert len(layouts) == len(frontiers)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_mul" for binding in frontier)
        for frontier in frontiers
    )


def test_generic_to_and_per_head_linear_frontier_rules_are_shape_checked(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "add"),
    )
    staged_frontiers, staged_layouts = deduplicate_relation_frontiers(
        staged_frontiers, staged_layouts
    )
    to_certs, frontiers = advance_to_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    linear_certs, frontiers = advance_per_head_linear_relation_frontiers(
        proof, frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(to_certs) == 22
    assert len(linear_certs) == 24
    assert all(item.input_shape == item.output_shape for item in to_certs)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op in {"FW_to", "FW_per_head_mix_precision_linear"} for binding in frontier)
        for frontier in frontiers
    )


def test_generic_rotary_frontier_pass_groups_both_semantic_outputs(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "add"),
    )
    staged_frontiers, staged_layouts = deduplicate_relation_frontiers(
        staged_frontiers, staged_layouts
    )
    certs, frontiers, layouts = expand_rotary_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 12
    assert len(frontiers) == len(staged_frontiers) + 12
    assert len(layouts) == len(frontiers)
    assert all(item.output_step_triples[0] != item.output_step_triples[1] for item in certs)
    assert all(len(item.input_relation_step_triples) == 3 for item in certs)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_rotary_embedding" for binding in frontier)
        for frontier in frontiers
    )



def test_generic_topk_routing_groups_scores_and_map_outputs(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "to", "per_head_linear", "mul", "pointwise", "ordinary_moe", "unshuffle", "add"),
        deduplicate_each_round=True,
        goal_ir=ir,
    )
    certs, frontiers, layouts = expand_topk_routing_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    assert len(certs) == 24
    assert all(item.output_projections == (".1", ".2.1") for item in certs)
    ordinary = [item for item in certs if item.relation_kind == "ordinary"]
    zigzag = [item for item in certs if item.relation_kind == "zigzag"]
    assert len(ordinary) == len(zigzag) == 12
    assert all(
        item.lean_theorem
        == "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.topk_routing_all"
        for item in ordinary
    )
    assert all(
        item.lean_theorem
        == "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.topk_routing_all"
        for item in zigzag
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_topk_routing" for binding in frontier)
        for frontier in frontiers
    )
    assert len(frontiers) == len(staged_frontiers) - 24
    assert len(layouts) == len(frontiers)


def test_zigzag_full_expert_moe_closes_with_two_weight_lineages(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    assert relation.unresolved_frontiers == ()
    assert relation.unresolved_side_conditions == ()
    certs = [
        cert for cert in relation.certificates
        if getattr(cert, "rule_id", "") == "zigzag-full-moe-expert-split-two-rank"
    ]
    assert len(certs) == 11
    cert = certs[0]
    assert cert.relation_kind == "zigzag"
    assert len(cert.input_step_triples) == 3
    assert cert.weight_lineage_theorem == "TrainVerify.Denote.InitGoalHolds.gather2_dim0"
    assert cert.lean_theorem == "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.all2all_moe_gmm_full_1x2"
    for binding, lineage in zip(cert.full_weight_bindings, cert.weight_lineage_rank_tids):
        full_tid = int(binding.split(":", 1)[1])
        parsed = ir.init_lineages[full_tid]
        assert lineage == tuple((int(rank), int(tid)) for rank, tid in parsed.tps)


def test_zigzag_full_producer_chunks_preserve_input_relation_and_weight_lineage(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    by_id = {step.step_id: step for step in proof.steps}
    assert all(
        by_id[frontier[0]].op != "FW_per_head_mix_precision_linear"
        for frontier in relation.unresolved_frontiers
    )
    certs = [
        cert for cert in relation.certificates
        if getattr(cert, "rule_id", "") == "FW_per_head_mix_precision_linear-full-producer-chunks-zigzag-two-rank"
    ]
    assert len(certs) == 12
    cert = certs[0]
    assert cert.relation_kind == "zigzag"
    assert cert.output_step_triple == (
        cert.sm_operator_step, cert.pm_chunk_steps[0], cert.pm_chunk_steps[1]
    )
    weight_tid = int(cert.replicated_weight_binding.split(":", 1)[1])
    assert cert.weight_init_lineage_rank_tids == ((0, weight_tid),)
    assert cert.result_relation_theorem == "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks"


def test_zigzag_certificate_dag_resolves_aliases_to_public_metadata_region(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    regions, authority_by_frontier = resolve_zigzag_metadata_regions(
        ir, relation.certificates, relation.unresolved_frontiers, relation.unresolved_layouts
    )
    assert len(regions) == 1
    region = regions[0]
    assert region.metadata_source == "getitem:root=4441:key=cu_seqlens_q"
    assert region.contract_metadata_tid == 6252
    assert 5602 in region.alias_tids
    for frontier, layout in zip(relation.unresolved_frontiers, relation.unresolved_layouts):
        if layout == "zigzag":
            assert authority_by_frontier[frontier].metadata_source == region.metadata_source


def test_hidden_sharded_embedding_alltoall_closes_from_explicit_init_lineage(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    certs = [item for item in relation.certificates if getattr(item, "rule_id", "") == "hidden-sharded-embedding-alltoall-ordinary-two-rank"]
    frontiers = relation.unresolved_frontiers
    layouts = relation.unresolved_layouts
    assert len(certs) == 1
    cert = certs[0]
    assert cert.full_weight_tid == 4932
    assert cert.shard_weight_rank_tids == ((0, 7746), (1, 7747))
    assert cert.weight_gather_dim == 1
    assert cert.alltoall_steps == ("pm:28:0", "pm:29:0")
    assert cert.lean_theorem == "TrainVerify.Denote.fw_embedding_hidden_shards_allToAll_two"
    by_id = {step.step_id: step for step in proof.steps}
    assert not any(
        not frontier[0].startswith("init:") and by_id[frontier[0]].op == "FW_embedding"
        for frontier in frontiers
    )
    assert len(frontiers) == len(layouts)


def test_faithful_shuffle_certificate_uses_public_metadata_alias_authority(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    certs = [item for item in relation.certificates if getattr(item, "rule_id", "") == "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank"]
    frontiers = relation.unresolved_frontiers
    layouts = relation.unresolved_layouts
    assert len(certs) == 1
    cert = certs[0]
    assert cert.node_metadata_tid == 5602
    assert cert.contract_metadata_tid == 6252
    assert cert.metadata_source == "getitem:root=4441:key=cu_seqlens_q"
    assert cert.metadata_init_lineage_rank_tids == ((0, 5602),)
    assert cert.metadata_cross_store_theorem == "TrainVerify.Denote.InitGoalHolds.singleton_value_eq"
    assert cert.pre_layout == "ordinary"
    assert cert.post_layout == "zigzag"
    assert cert.pm_replica_members == ((0, 9750), (1, 9751))
    by_id = {step.step_id: step for step in proof.steps}
    assert not any(
        not frontier[0].startswith("init:") and by_id[frontier[0]].op == "FW_maybe_shuffle"
        for frontier in frontiers
    )
    assert all(layout in {"ordinary", "zigzag"} for layout in layouts)


def test_ordinary_full_producer_chunks_reduce_to_true_allgather_sources(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    certs = [
        item for item in relation.certificates
        if getattr(item, "rule_id", "").endswith("full-producer-chunks-ordinary-two-rank")
    ]
    assert len(certs) == 24
    assert sum(item.operator == "FW_norm_linear" for item in certs) == 12
    assert sum(item.operator == "FW_per_head_mix_precision_linear" for item in certs) == 12
    assert all(item.pre_layout == "ordinary" and item.post_layout == "ordinary" for item in certs)
    by_id = {step.step_id: step for step in proof.steps}
    assert all(by_id[item.pm_allgather_step].op == "AllGatherPrim" for item in certs)
    assert all(by_id[item.input_step_triple[1]].rank == 0 and by_id[item.input_step_triple[2]].rank == 1 for item in certs)
    zigzag_certs = [
        item for item in relation.certificates
        if getattr(item, "rule_id", "").endswith("full-producer-chunks-zigzag-two-rank")
    ]
    assert zigzag_certs
    assert all(item.pre_layout == "zigzag" and item.post_layout == "zigzag" for item in zigzag_certs)


def test_init_full_tensor_chunk_boundaries_close_from_explicit_lineage(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    certs = [item for item in relation.certificates if getattr(item, "rule_id", "") == "init-lineage-full-to-two-chunks"]
    assert len(certs) == 12
    assert all(item.lineage_pm_rank_tids == ((0, item.sm_tid),) for item in certs)
    by_id = {step.step_id: step for step in proof.steps}
    assert not any(
        frontier[0].startswith("init:")
        and all(not binding.startswith("init:") and by_id[binding].op == "ChunkPrim" for binding in frontier[1:])
        for frontier in relation.unresolved_frontiers
    )


def test_public_generated_init_lineages_are_resolved_for_goals3_and4(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal_id in (3, 4):
        ir = load_goal_ir(goal_id, str(root))
        lineage = ir.init_lineages[4943]
        assert lineage.ts == 4943
        assert lineage.tps == [(0, 4943)]
        assert lineage.tsShape == [4096]

def test_relation_plan_retains_deterministic_frontier_certificates(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    first = compile_relation_plan(ir, proof)
    second = compile_relation_plan(ir, proof)
    assert first.certificates
    assert first.certificates == second.certificates
    assert len(first.certificates) == len(set(first.certificates))
    assert first.unresolved_side_conditions == ()
    assert first.unresolved_side_conditions == second.unresolved_side_conditions
    rule_ids = {certificate.rule_id for certificate in first.certificates}
    assert {
        "attention-ordinary-qkv-two-rank",
        "rotary-embedding-two-output-ordinary-two-rank",
        "broadcast-mul-zigzag-two-rank",
        "swiglu-zigzag-two-rank",
    } <= rule_ids


def test_relation_frontiers_are_stably_deduplicated_as_a_dag():
    first = ("sm:1:0", "pm:1:0", "pm:2:0")
    second = ("sm:2:0", "pm:3:0", "pm:4:0")
    raw_frontiers = (first, first, second, first)
    raw_layouts = ("ordinary", "ordinary", "zigzag", "ordinary")
    frontiers, layouts = deduplicate_relation_frontiers(raw_frontiers, raw_layouts)
    assert frontiers == (first, second)
    assert layouts == ("ordinary", "zigzag")
    assert list(zip(layouts, frontiers)) == list(dict.fromkeys(zip(raw_layouts, raw_frontiers)))
    assert deduplicate_relation_frontiers(frontiers, layouts) == (frontiers, layouts)

def test_generic_attention_frontier_pass_expands_layout_typed_qkv(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "add"),
    )
    certs, frontiers, layouts = expand_attention_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 552
    assert sum(item.relation_kind == "ordinary" for item in certs) == 420
    assert sum(item.relation_kind == "zigzag" for item in certs) == 132
    assert len(frontiers) == len(staged_frontiers) + 2 * len(certs)
    assert len(layouts) == len(frontiers)
    assert not any(
        all(
            not binding.startswith("init:")
            and by_id[binding].op in {"FW_attn_sliding_window", "FW_attn_zigzag"}
            for binding in frontier
        )
        for frontier in frontiers
    )
    for cert in certs:
        expected = ("ordinary", "ordinary", "ordinary") if cert.relation_kind == "ordinary" else ("zigzag", "ordinary", "ordinary")
        assert cert.input_relation_kinds == expected


def test_generic_flatten_3d_frontier_pass_checks_shape_product(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(
        ir, proof, peel_aliases=False, deduplicate_frontiers=False
    )
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "identity_view", "linear", "add"),
    )
    certs, frontiers = advance_flatten_3d_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 552
    assert all(item.input_shape[1] * item.input_shape[2] == item.output_shape[1] for item in certs)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_reshape" for binding in frontier)
        for frontier in frontiers
    )


def test_generic_identity_reshape_uses_same_shape_gated_rule(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=("alias", "rms_norm", "float", "add"),
    )
    _view_certs, staged_frontiers = advance_identity_view_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    _linear_certs, staged_frontiers = advance_linear_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    certs, _frontiers = advance_identity_view_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    assert len(certs) == 552
    assert all(item.operator == "FW_reshape" for item in certs)
    assert all(item.input_shape == item.output_shape for item in certs)


def test_generic_identity_view_frontier_pass_is_shape_gated(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=('alias', 'rms_norm', 'float', 'add'),
    )
    certs, frontiers = advance_identity_view_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 552
    assert all(item.input_shape == item.output_shape == (4096, 1024) for item in certs)
    assert not any(
        all(
            not binding.startswith("init:")
            and by_id[binding].op == "FW_view"
            and by_id[binding].input_shapes[0] == by_id[binding].output_shape
            for binding in frontier
        )
        for frontier in frontiers
    )


def test_generic_float_frontier_pass_preserves_explicit_layout(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=('alias', 'rms_norm', 'add'),
    )
    certs, frontiers = advance_float_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 1152
    assert sum(item.relation_kind == "ordinary" for item in certs) == 888
    assert sum(item.relation_kind == "zigzag" for item in certs) == 264
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_float" for binding in frontier)
        for frontier in frontiers
    )


def test_generic_add_frontier_pass_expands_binary_relation_dag(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=('alias', 'rms_norm'),
    )
    certs, frontiers, layouts = expand_add_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 68
    assert sum(item.relation_kind == "ordinary" for item in certs) == 46
    assert sum(item.relation_kind == "zigzag" for item in certs) == 22
    assert len(frontiers) == len(staged_frontiers) + len(certs)
    assert len(layouts) == len(frontiers)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_add" for binding in frontier)
        for frontier in frontiers
    )


def test_generic_rms_norm_frontier_pass_preserves_explicit_layout(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    staged_frontiers, staged_layouts = normalize_relation_frontiers(
        proof,
        relation.unresolved_frontiers,
        relation.unresolved_layouts,
        rules=('alias',),
    )
    certs, frontiers = advance_rms_norm_relation_frontiers(
        proof, staged_frontiers, staged_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(certs) == 48
    assert sum(item.relation_kind == "ordinary" for item in certs) == 36
    assert sum(item.relation_kind == "zigzag" for item in certs) == 12
    assert all(item.lean_theorem.endswith(
        "fw_rms_norm_allGather0_commute_2_core" if item.relation_kind == "ordinary" else "Zigzag2Rel.rms_norm"
    ) for item in certs)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_rms_norm" for binding in frontier)
        for frontier in frontiers
    )


def test_generic_multiref_frontier_pass_peels_all_aliases(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof, peel_aliases=False, deduplicate_frontiers=False)
    aliases, frontiers = peel_multiref_relation_frontiers(
        proof, relation.unresolved_frontiers, relation.unresolved_layouts
    )
    by_id = {step.step_id: step for step in proof.steps}
    assert len(aliases) == 60
    assert len(frontiers) == len(relation.unresolved_frontiers)
    assert all(0 <= item.output_index < item.arity for item in aliases)
    assert not any(
        all(not binding.startswith("init:") and by_id[binding].op == "FW_multiref" for binding in frontier)
        for frontier in frontiers
    )


def test_zigzag_attention_q_reduces_gather_linear_chunk_to_zigzag_input(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, proof)
    layers = build_indexed_stack_layer_relations(proof, terminal)
    chunks = build_chunk_reconstruction_relations(proof, terminal, layers)
    checkpoints = build_router_input_checkpoints(proof, chunks)
    adds = build_add_relations(proof, build_rms_norm_relations(proof, checkpoints))
    unary = build_attention_output_unary_relations(ir, proof, adds)
    attention = build_attention_relations(proof, unary)
    q = build_zigzag_attention_q_relations(proof, attention)
    assert len(q) == 12
    assert all(item.rule_id == "zigzag-q-gather-linear-chunk-two-rank" for item in q)
    assert all(item.input_relation_kind == "zigzag" for item in q)
    assert all(item.input_step_triple for item in q)
    assert all(item.lean_theorems[0].endswith("Zigzag2Rel.per_head_linear") for item in q)
    assert all("allGather0_commute" in item.lean_theorems[1] for item in q)


def test_zigzag_attention_kv_remains_ordinary_through_to_alias_and_linear(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, proof)
    layers = build_indexed_stack_layer_relations(proof, terminal)
    chunks = build_chunk_reconstruction_relations(proof, terminal, layers)
    checkpoints = build_router_input_checkpoints(proof, chunks)
    adds = build_add_relations(proof, build_rms_norm_relations(proof, checkpoints))
    unary = build_attention_output_unary_relations(ir, proof, adds)
    attention = build_attention_relations(proof, unary)
    kv = build_zigzag_attention_kv_relations(proof, attention)
    assert len(kv) == 24
    assert [item.role for item in kv] == [role for _ in range(12) for role in ("k", "v")]
    assert all(item.relation_kind == "ordinary" for item in kv)
    assert all([step.rule_id for step in item.steps] == [
        "to-identity",
        "multiref-alias",
        "per-head-mix-precision-linear-ordinary",
    ] for item in kv)
    assert all(item.steps[-1].lean_theorem.endswith("fw_per_head_mix_precision_linear_allGather0_commute_2") for item in kv)


def test_ordinary_attention_qkv_builds_joint_rotary_and_v_linear_certificates(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, proof)
    layers = build_indexed_stack_layer_relations(proof, terminal)
    chunks = build_chunk_reconstruction_relations(proof, terminal, layers)
    checkpoints = build_router_input_checkpoints(proof, chunks)
    adds = build_add_relations(proof, build_rms_norm_relations(proof, checkpoints))
    unary = build_attention_output_unary_relations(ir, proof, adds)
    attention = build_attention_relations(proof, unary)
    rotary = build_ordinary_rotary_relations(proof, attention)
    value = build_ordinary_attention_v_relations(proof, attention)
    assert len(rotary) == 12
    assert all(item.output_projections == (".1", ".2") for item in rotary)
    assert all(item.input_roles == ("position", "q", "k") for item in rotary)
    assert all(len(item.input_relation_step_triples) == 3 for item in rotary)
    assert all(item.replicated_cos_sin_tid == 4944 for item in rotary)
    assert rotary[0].lean_theorem.endswith("fw_rotary_embedding_allGather0_commute_2")
    assert len(value) == 12
    assert all(item.input_role == "v-hidden" for item in value)
    assert value[0].lean_theorem.endswith("fw_per_head_mix_precision_linear_allGather0_commute_2")


def test_attention_frontiers_build_layout_specific_qkv_certificates(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, proof)
    layers = build_indexed_stack_layer_relations(proof, terminal)
    chunks = build_chunk_reconstruction_relations(proof, terminal, layers)
    checkpoints = build_router_input_checkpoints(proof, chunks)
    rms = build_rms_norm_relations(proof, checkpoints)
    adds = build_add_relations(proof, rms)
    unary = build_attention_output_unary_relations(ir, proof, adds)
    attention = build_attention_relations(proof, unary)
    assert len(attention) == 24
    assert [item.input_relation_kind for item in attention] == ["ordinary"] * 12 + ["zigzag"] * 12
    assert all(item.input_roles == ("q", "k", "v") for item in attention)
    assert all(len(item.input_relation_step_triples) == 3 for item in attention)
    assert attention[0].rule_id == "sliding-window-attention-ordinary-two-rank"
    assert attention[0].lean_theorem.endswith("applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair")
    assert attention[12].rule_id == "zigzag-attention-sharded-kv-two-rank"
    assert attention[12].lean_theorem.endswith("Zigzag2Rel.attn_zigzag_sharded_kv")
    assert all(len(item.metadata_tids) == 2 for item in attention)


def test_relation_plan_advances_right_frontiers_to_attention_nodes(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    assert relation.unresolved_frontiers == ()
    assert relation.unresolved_layouts == ()
    attention = [
        item for item in relation.certificates
        if getattr(item, "rule_id", "") in {
            "sliding-window-attention-ordinary-two-rank",
            "zigzag-attention-sharded-kv-two-rank",
        }
    ]
    assert len(attention) == 24


def test_add_right_branches_build_shape_checked_attention_output_unary_chains(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    layers = build_indexed_stack_layer_relations(plan, terminal)
    chunks = build_chunk_reconstruction_relations(plan, terminal, layers)
    checkpoints = build_router_input_checkpoints(plan, chunks)
    rms = build_rms_norm_relations(plan, checkpoints)
    adds = build_add_relations(plan, rms)
    chains = build_attention_output_unary_relations(ir, plan, adds)
    assert len(chains) == 24
    assert [chain.input_relation_kind for chain in chains] == ["ordinary"] * 12 + ["zigzag"] * 12
    assert all(len(chain.steps) == 5 for chain in chains)
    assert [step.rule_id for step in chains[0].steps] == [
        "float-identity",
        "view-2d-identity",
        "mix-precision-linear-2d",
        "reshape-2d-identity",
        "reshape-3d-to-2d",
    ]
    assert chains[0].steps[-1].lean_theorem.endswith("fw_view_allGather0_commute_cp2")
    assert chains[12].steps[-1].lean_theorem.endswith("Zigzag2Rel.view_3d_to_2d")
    assert all(chain.input_step_triple for chain in chains)


def test_rms_frontiers_build_binary_add_relation_obligations(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    layers = build_indexed_stack_layer_relations(plan, terminal)
    chunks = build_chunk_reconstruction_relations(plan, terminal, layers)
    checkpoints = build_router_input_checkpoints(plan, chunks)
    rms = build_rms_norm_relations(plan, checkpoints)
    adds = build_add_relations(plan, rms)
    assert len(adds) == 24
    assert all(len(item.input_relation_step_triples) == 2 for item in adds)
    assert [item.input_relation_kind for item in adds] == ["ordinary"] * 12 + ["zigzag"] * 12
    assert "allGather0" in adds[0].lean_theorem
    assert adds[12].lean_theorem.endswith("Zigzag2Rel.add")


def test_router_checkpoints_build_synchronized_rms_norm_relations(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    layers = build_indexed_stack_layer_relations(plan, terminal)
    chunks = build_chunk_reconstruction_relations(plan, terminal, layers)
    checkpoints = build_router_input_checkpoints(plan, chunks)
    rms = build_rms_norm_relations(plan, checkpoints)
    assert len(rms) == 24
    assert [item.input_relation_kind for item in rms] == ["ordinary"] * 12 + ["zigzag"] * 12
    assert all(item.shared_weight_tid for item in rms)
    assert all(item.input_step_triple for item in rms)
    assert "allGather0" in rms[0].lean_theorem
    assert rms[12].lean_theorem.endswith("Zigzag2Rel.rms_norm")


def test_router_frontiers_preserve_ordinary_vs_zigzag_relation_kind(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    layers = build_indexed_stack_layer_relations(plan, terminal)
    chunks = build_chunk_reconstruction_relations(plan, terminal, layers)
    checkpoints = build_router_input_checkpoints(plan, chunks)
    assert len(checkpoints) == 24
    assert all(item.wrapper_ops == ("FW_norm_linear", "FW_float") for item in checkpoints)
    assert all(len(item.previous_relation_step_triple) == 3 for item in checkpoints)
    assert [item.rule_id for item in checkpoints].count("router-input-from-ordinary-gather") == 12
    assert [item.rule_id for item in checkpoints].count("router-input-from-zigzag-gather") == 12
    assert [item.input_relation_kind for item in checkpoints] == ["ordinary"] * 12 + ["zigzag"] * 12


def test_routing_frontiers_reduce_to_full_value_equalities_via_chunks(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    layers = build_indexed_stack_layer_relations(plan, terminal)
    chunks = build_chunk_reconstruction_relations(plan, terminal, layers)
    assert len(chunks) == 24
    assert all(item.rule_id == "chunk-reconstruct-dim0-two-rank" for item in chunks)
    assert all((item.shard_rows, item.width) == (2048, 64) for item in chunks)
    assert all(item.pm_full_source_step for item in chunks)
    assert all(item.lean_theorem.endswith("allGather0_reconstruct_chunks_2d") for item in chunks)


def test_chunk_reconstruction_rejects_distinct_pm_sources(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    layers = build_indexed_stack_layer_relations(plan, terminal)
    steps = list(plan.steps)
    first_rank1_chunk = layers[0].input_step_triple[2]
    index = next(i for i, step in enumerate(steps) if step.step_id == first_rank1_chunk)
    steps[index] = replace(steps[index], input_tids=(999999,), dependencies=("pm:0:0",))
    with pytest.raises(RelationCompositionError, match="same PM full source"):
        build_chunk_reconstruction_relations(replace(plan, steps=tuple(steps)), terminal, layers)


def test_routing_terminal_builds_synchronized_relation_steps(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    registry = build_default_registry()
    for goal_id, projection in ((3, ".2.1"), (4, ".2.2")):
        ir = load_goal_ir(goal_id, str(root))
        plan = compile_proof_plan(ir, registry)
        terminal = match_indexed_stack_gather_two_rank(ir, plan)
        relations = build_indexed_stack_layer_relations(plan, terminal)
        assert len(relations) == 24
        assert [step.rule_id for step in relations].count("ordinary-topk-projection-two-rank") == 12
        assert [step.rule_id for step in relations].count("zigzag-topk-unshuffle-two-rank") == 12
        assert all(step.output_projection == projection for step in relations)
        assert all(len(step.input_step_triple) == 3 for step in relations)


def test_zigzag_layer_relation_rejects_wrong_cp_rank(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    terminal = match_indexed_stack_gather_two_rank(ir, plan)
    steps = list(plan.steps)
    index = next(i for i, step in enumerate(steps) if step.step_id == terminal.layer_step_triples[12][2])
    steps[index] = replace(steps[index], parameters=(2, 0))
    with pytest.raises(RelationCompositionError, match="rank parameters"):
        build_indexed_stack_layer_relations(replace(plan, steps=tuple(steps)), terminal)


def test_real_routing_goals_share_generic_indexed_stack_gather_terminal(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    registry = build_default_registry()
    for goal_id in (3, 4):
        ir = load_goal_ir(goal_id, str(root))
        plan = compile_proof_plan(ir, registry)
        certificate = match_indexed_stack_gather_two_rank(ir, plan)
        assert certificate.rule_id == "indexed-stack-gather-two-rank"
        assert (certificate.length, certificate.shard_rows, certificate.width) == (24, 2048, 64)
        assert len(certificate.layer_step_triples) == 24
        assert certificate.lean_theorem.endswith("fw_stack_allGather0_dim1_commute_2d_element")


def test_indexed_stack_gather_terminal_rejects_wrong_rank_order(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    plan = compile_proof_plan(ir, build_default_registry())
    steps = list(plan.steps)
    terminal = next(i for i, step in enumerate(steps) if step.step_id == plan.target_steps[1])
    gather = steps[terminal]
    steps[terminal] = replace(gather, input_tids=tuple(reversed(gather.input_tids)))
    mutated = replace(plan, steps=tuple(steps))
    with pytest.raises(RelationCompositionError, match="rank-ordered"):
        match_indexed_stack_gather_two_rank(ir, mutated)


def test_parse_nodes_expands_closed_list_range_map_inputs():
    block = """def g : GraphDecl := by
      refine { numRanks := 1, nodes := ?_ }
      exact [{ rank := 0, op := "OpName.FW_attn_zigzag",
        ins := ((List.range 5).map (fun r => 5607 + r)), outs := [5612, 5613],
        params := [16, 4, 64, 64, 1, 0] }]
    """
    nodes = parse_nodes(block)
    assert nodes[0].ins == [5607, 5608, 5609, 5610, 5611]


def test_load_goal3_resolves_the_public_full_statement_graph_scope(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    assert ir.lineage.ts == 4928
    assert any(4928 in node.outs for node in ir.sm_nodes)
    assert any(4928 in node.outs for node in ir.pm_nodes)
    assert len(ir.sm_nodes) > 900
    assert len(ir.pm_nodes) > 1800



def test_public_graph_replica_groups_preserve_declared_moe_buddy_order(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    sm_group = next(group for group in ir.sm_replica_groups if group.members[0].primary_out_tid == 4968)
    pm_group = next(group for group in ir.pm_replica_groups if group.members[0].primary_out_tid == 7852)
    assert [(item.rank, item.primary_out_tid) for item in sm_group.members] == [(0, 4968)]
    assert [(item.rank, item.primary_out_tid) for item in pm_group.members] == [(0, 7852), (1, 7853)]
    assert sm_group.irname == pm_group.irname == "nnscaler_all2all_moe_gmm"



def test_explicit_full_statement_parser_extracts_packed_cu_contract(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    assert [(fact.side, fact.tid, fact.total_tokens, fact.num_ranks) for fact in ir.packed_cu_contracts] == [
        ("pm", 6248, 4096, 2)
    ]


def test_public_input_value_classes_preserve_metadata_alias_authority(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    sm = {item.source: item.tids for item in ir.sm_input_value_classes}
    pm = {item.source: item.tids for item in ir.pm_input_value_classes}
    key = "getitem:root=4441:key=cu_seqlens_q"
    assert sm == pm
    assert 5602 in sm[key]
    assert 6252 in sm[key]
    assert sm[key].index(5602) < sm[key].index(6252)


def test_public_contract_parser_extracts_packed_cu_wellformedness(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    assert [(item.side, item.tid, item.total_tokens, item.num_ranks) for item in ir.packed_cu_contracts] == [
        ("pm", 6252, 4096, 2)
    ]

def test_faithful_moe_certificate_uses_buddy_expanded_full_semantics(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    sm = next(step for step in proof.steps if step.side == "sm" and step.op == "FW_all2all_moe_gmm")
    pm = [step for step in proof.steps if step.side == "pm" and step.op == "FW_all2all_moe_gmm"][:2]
    assert sm.declared_input_tids == (7780, 4963, 4964, 4966, 4967)
    assert sm.semantic_input_tids == sm.declared_input_tids
    assert sm.denote_fn == "fw_all2all_moe_gmm_full"
    assert sm.parameters == (64, 8, 10)
    assert all(step.denote_fn == "fw_all2all_moe_gmm_full" for step in pm)
    assert all(step.parameters == (64, 8, 10) for step in pm)
    assert pm[0].declared_input_tids[-2:] == (7848, 7850)
    assert pm[1].declared_input_tids[-2:] == (7849, 7851)
    assert pm[0].semantic_input_tids[-4:] == pm[1].semantic_input_tids[-4:] == (7848, 7849, 7850, 7851)
    assert pm[0].semantic_input_bindings[-4:] == pm[1].semantic_input_bindings[-4:] == (
        "init:7848", "init:7849", "init:7850", "init:7851"
    )
    assert pm[0].apply_lemmas == pm[1].apply_lemmas == ("applyNodeDistributed_moe_out",)

def test_all2all_moe_gmm_full_binds_input_arity_to_num_ranks():
    registry = build_default_registry()
    rule = registry.require("FW_all2all_moe_gmm_full")
    assert rule.parameter_count == 3
    assert rule.denote_fn == "fw_all2all_moe_gmm_full"

    ins_sm = [1, 2, 3, 4, 5, 6, 7]
    ins_pm = [10, 11, 12, 13, 14, 15, 16]
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_all2all_moe_gmm_full", ins_sm, [30], [64, 8, 10])],
        pm_nodes=[Node(0, "FW_all2all_moe_gmm_full", ins_pm, [40], [64, 8, 10])],
        tps=[(0, 40)],
    )
    ir.sm_num_ranks = 2
    ir.pm_num_ranks = 2
    ir.sm_shapes = [(1, [4, 8]), (2, [4, 64]), (3, [4, 64]), (4, [32, 12, 8]), (5, [32, 12, 8]), (6, [32, 8, 6]), (7, [32, 8, 6])]
    ir.pm_shapes = [(10, [4, 8]), (11, [4, 64]), (12, [4, 64]), (13, [32, 12, 8]), (14, [32, 12, 8]), (15, [32, 8, 6]), (16, [32, 8, 6])]
    ir.lineage.tsShape = [4, 8]
    ir.lineage.tpShapes = [[4, 8]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_nodes[0].ins.pop()
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "3 + 2*numRanks" in plan.diagnostics[0].message


def test_fw_stack_prepends_input_count_and_requires_equal_shapes():
    registry = build_default_registry()
    rule = registry.require("FW_stack")
    assert rule.input_count is None
    assert rule.min_inputs == 1
    assert rule.relation_effect is RelationEffect.STACK

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_stack", [1, 2, 3], [30])],
        pm_nodes=[Node(0, "FW_stack", [10, 11, 12], [40])],
        tps=[(0, 40)],
    )
    ir.sm_shapes = [(1, [2, 4]), (2, [2, 4]), (3, [2, 4])]
    ir.pm_shapes = [(10, [2, 4]), (11, [2, 4]), (12, [2, 4])]
    ir.lineage.tsShape = [3, 2, 4]
    ir.lineage.tpShapes = [[3, 2, 4]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_shapes[2] = (12, [2, 5])
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "stack input shapes differ" in plan.diagnostics[0].message


def test_inner_chunk_ce_infers_both_loss_shapes_and_validates_inputs():
    registry = build_default_registry()
    rule = registry.require("FW_inner_chunk_ce")
    assert rule.output_count == 2
    assert rule.output_projections == (".fst", ".snd")

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_inner_chunk_ce", [1, 2, 3], [30, 31], [1024, 0])],
        pm_nodes=[Node(0, "FW_inner_chunk_ce", [10, 11, 12], [40, 41], [1024])],
        tps=[(0, 41)],
    )
    ir.sm_shapes = [(1, [4, 8]), (2, [64, 8]), (3, [4])]
    ir.pm_shapes = [(10, [4, 8]), (11, [64, 8]), (12, [4])]
    ir.lineage.ts = 31
    ir.lineage.tsShape = [4]
    ir.lineage.tpShapes = [[4]]
    assert compile_proof_plan(ir, registry).supported is True

    ir.pm_shapes[2] = (12, [5])
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert "label shape" in plan.diagnostics[0].message


def test_multiref_propagates_input_shape_to_every_output():
    registry = build_default_registry()
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_multiref", [1], [30, 31], [2])],
        pm_nodes=[Node(0, "FW_multiref", [10], [40, 41], [2])],
        tps=[(0, 41)],
    )
    ir.lineage.ts = 31
    assert compile_proof_plan(ir, registry).supported is True


def test_faithful_unshuffle_emits_zigzag_to_ordinary_effect():
    registry = build_default_registry()
    rule = registry.require("FW_maybe_unshuffle")
    assert rule.denote_fn == "applyNodeFaithfulUnshuffleValue"

    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_maybe_unshuffle", [1, 2], [30], [1, 0])],
        pm_nodes=[Node(1, "FW_maybe_unshuffle", [10, 11], [40], [2, 1])],
        tps=[(1, 40)],
    )
    ir.sm_shapes = [(1, [4, 4]), (2, [2])]
    ir.pm_shapes = [(10, [4, 4]), (11, [2])]
    ir.pm_num_ranks = 2
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is True
    effects = {(step.side, step.op): step.relation_effect for step in plan.steps}
    assert effects[("sm", "FW_maybe_unshuffle")] is RelationEffect.PRESERVE
    assert effects[("pm", "FW_maybe_unshuffle")] is RelationEffect.ZIGZAG_TO_ORDINARY


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
    assert decoded["schema_version"] == 4
    assert decoded["steps"][0]["declared_input_tids"] == decoded["steps"][0]["semantic_input_tids"]
    assert decoded["steps"][0]["input_bindings"] == decoded["steps"][0]["semantic_input_bindings"]
    assert decoded["status"] == "supported"
    assert decoded["steps"][0]["input_shapes"]
    assert decoded["steps"][0]["output_shape"]
    assert decoded["steps"][0]["input_bindings"] == ["init:1"]


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
        check=False,
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
        check=False,
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
        check=False,
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
        check=False,
    )
    assert result.returncode == 2
    assert result.stderr == ""
    payload = json.loads(result.stdout)
    assert payload["status"] == "error"
    assert payload["diagnostics"][0]["code"] == "cli.usage"


def test_certificate_transition_adapters_are_closed_and_extract_exact_node_footprints(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    transitions = build_certificate_transition_specs(proof, relation.certificates)
    assert transitions
    assert len({item.transition_id for item in transitions}) == len(transitions)
    assert all(tuple(sorted(set(item.sm_node_indices))) == item.sm_node_indices for item in transitions)
    assert all(tuple(sorted(set(item.pm_node_indices))) == item.pm_node_indices for item in transitions)
    assert all(0 <= index < len(ir.sm_nodes) for item in transitions for index in item.sm_node_indices)
    assert all(0 <= index < len(ir.pm_nodes) for item in transitions for index in item.pm_node_indices)
    assert any(item.pre_facts and item.post_facts for item in transitions)
    assert any(not item.sm_node_indices for item in transitions)
    with pytest.raises(RelationCompositionError, match="no explicit transition adapter"):
        build_certificate_transition_specs(proof, (object(),))


def test_exact_node_coverage_plan_accounts_for_every_authority_node_once(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    transitions = build_certificate_transition_specs(proof, relation.certificates)
    coverage = build_exact_node_coverage_plan(ir, transitions)
    assert tuple(item.node_index for item in coverage.sm_nodes) == tuple(range(len(ir.sm_nodes)))
    assert tuple(item.node_index for item in coverage.pm_nodes) == tuple(range(len(ir.pm_nodes)))
    assert any(item.kind == "frame" for item in coverage.sm_nodes)
    assert any(item.kind == "frame" for item in coverage.pm_nodes)
    by_id = {item.transition_id: item for item in transitions}
    for item in coverage.sm_nodes:
        assert all(item.node_index in by_id[owner].sm_node_indices for owner in item.transition_ids)
    for item in coverage.pm_nodes:
        assert all(item.node_index in by_id[owner].pm_node_indices for owner in item.transition_ids)
    bad = replace(transitions[0], sm_node_indices=(len(ir.sm_nodes),))
    with pytest.raises(RelationCompositionError, match="outside authority graph"):
        build_exact_node_coverage_plan(ir, (bad, *transitions[1:]))


def test_indexed_terminal_chunks_use_layout_typed_full_producer_certificates(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    mixed = {
        item.output_step_triple: item for item in relation.certificates
        if getattr(item, "rule_id", "").endswith("full-producer-chunks-zigzag-two-rank")
    }
    zigzag_layers = [
        item for item in relation.synchronized_steps
        if item.rule_id == "zigzag-topk-unshuffle-two-rank"
    ]
    assert len(zigzag_layers) == 12
    for layer in zigzag_layers:
        cert = mixed[layer.input_step_triple]
        assert cert.result_relation_theorem.endswith("Zigzag2Rel.norm_linear_fullProducer_chunks")
        assert cert.pre_layout == cert.post_layout == "zigzag"


def test_transition_dependency_plan_is_forward_unique_and_cycle_free(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal_id in (1, 3):
        ir = load_goal_ir(goal_id, str(root))
        proof = compile_proof_plan(ir, build_default_registry())
        relation = compile_relation_plan(ir, proof)
        transitions = (
            build_certificate_transition_specs(proof, relation.certificates)
            + build_synchronized_transition_specs(relation.synchronized_steps)
        )
        dependencies = build_transition_dependency_plan(transitions)
        assert len(dependencies.order) == len(transitions)
        position = {transition_id: index for index, transition_id in enumerate(dependencies.order)}
        assert len(position) == len(transitions)
        assert all(
            position[producer] < position[consumer]
            for consumer, producers in dependencies.dependencies
            for producer in producers
        )
    duplicate = replace(transitions[-1], post_facts=transitions[0].post_facts)
    with pytest.raises(RelationCompositionError, match="multiple producers"):
        build_transition_dependency_plan((*transitions[:-1], duplicate))
    dangling_fact = replace(transitions[-1].pre_facts[0], step_triple=("init:1", "init:2", "init:3"))
    dangling = replace(transitions[-1], pre_facts=(dangling_fact,))
    with pytest.raises(RelationCompositionError, match="has no producer"):
        build_transition_dependency_plan((*transitions[:-1], dangling))


def test_atomic_schedule_freezes_shared_owners_and_is_deterministic(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal_id in (1, 3):
        ir = load_goal_ir(goal_id, str(root))
        proof = compile_proof_plan(ir, build_default_registry())
        relation = compile_relation_plan(ir, proof)
        transitions = (
            build_certificate_transition_specs(proof, relation.certificates)
            + build_synchronized_transition_specs(relation.synchronized_steps)
        )
        schedule = build_atomic_schedule(ir, transitions)
        rerun = build_atomic_schedule(ir, tuple(reversed(transitions)))
        assert schedule.complete is True
        assert schedule.digest == rerun.digest
        assert schedule.order == rerun.order
        assert len(schedule.sm_node_components) == len(ir.sm_nodes)
        assert len(schedule.pm_node_components) == len(ir.pm_nodes)
        assert set(schedule.transition_components) == {item.transition_id for item in transitions}
        assert all(component.transition_ids for component in schedule.components)
        assert all(component.sm_range[1] >= component.sm_range[0] for component in schedule.components)
        changed_rule = replace(transitions[0], rule_id=transitions[0].rule_id + "-mutated")
        mutated = build_atomic_schedule(ir, (changed_rule, *transitions[1:]))
        assert mutated.transition_digest != schedule.transition_digest
        assert mutated.digest != schedule.digest
        assert all(component.pm_range[1] >= component.pm_range[0] for component in schedule.components)
        for transition in transitions:
            component_id = schedule.transition_components[transition.transition_id]
            assert all(schedule.sm_node_components[index] == component_id for index in transition.sm_node_indices)
            assert all(schedule.pm_node_components[index] == component_id for index in transition.pm_node_indices)
    broken = replace(transitions[-1], pm_node_indices=(len(ir.pm_nodes),))
    with pytest.raises(RelationCompositionError, match="out of bounds"):
        build_atomic_schedule(ir, (*transitions[:-1], broken))


def test_closed_relation_facts_materialize_exact_tids_shapes_and_metadata(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal_id in (1, 3):
        ir = load_goal_ir(goal_id, str(root))
        proof = compile_proof_plan(ir, build_default_registry())
        relation = compile_relation_plan(ir, proof)
        facts = materialize_closed_relation_facts(ir, proof, relation)
        specs = {
            fact
            for transition in relation.transition_specs
            for fact in (*transition.pre_facts, *transition.post_facts)
        }
        assert {fact.source for fact in facts} == specs
        assert len({fact.fact_id for fact in facts}) == len(facts)
        zigzag_metadata = {fact.metadata_tid for fact in facts if fact.kind == "zigzag"}
        shuffle_outputs = {
            cert.output_step_triple: cert.node_metadata_tid
            for cert in relation.certificates
            if type(cert).__name__ == "FaithfulShuffleCertificate"
        }
        if zigzag_metadata:
            assert zigzag_metadata == set(shuffle_outputs.values())
            assert zigzag_metadata != {region.contract_metadata_tid for region in relation.zigzag_regions}
        for fact in facts:
            assert fact.full_shape
            assert fact.shard_shape
            if fact.source.step_triple in shuffle_outputs:
                assert fact.metadata_tid == shuffle_outputs[fact.source.step_triple]
            assert fact.sm_tid >= 0 and fact.pm_rank0_tid >= 0 and fact.pm_rank1_tid >= 0
            if fact.kind == "zigzag":
                assert fact.metadata_tid is not None
                assert fact.metadata_region_id is not None
            else:
                assert fact.metadata_tid is None
                assert fact.metadata_region_id is None


def test_closed_dependent_chain_plan_has_live_nonempty_states_and_exact_ranges(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal_id in (1, 3):
        ir = load_goal_ir(goal_id, str(root))
        proof = compile_proof_plan(ir, build_default_registry())
        relation = compile_relation_plan(ir, proof)
        chain = build_closed_dependent_chain_plan(ir, proof, relation)
        assert chain.complete is True
        assert len(chain.segments) == len(relation.atomic_schedule.components)
        assert len(chain.states) == len(chain.segments) + 1
        assert chain.terminal_target_fact_id in chain.states[-1].fact_ids
        assert all(state.fact_ids for state in chain.states)
        authority_ids = {fact.fact_id for fact in chain.authority_facts}
        assert authority_ids
        assert {fact.kind for fact in chain.authority_facts} == {
            "tensor_eq", "tensor_shape", "gather", "packed_cu"
        }
        assert authority_ids <= set(chain.states[0].fact_ids)
        assert all(any(fact_id in state.fact_ids for state in chain.states) for fact_id in authority_ids)
        assert not authority_ids <= set(chain.states[-1].fact_ids)
        for index, segment in enumerate(chain.segments):
            assert segment.pre_state_id == chain.states[index].state_id
            assert segment.post_state_id == chain.states[index + 1].state_id
        for side, count in (("sm", len(ir.sm_nodes)), ("pm", len(ir.pm_nodes))):
            cursor = 0
            for segment in chain.segments:
                begin, end = segment.sm_range if side == "sm" else segment.pm_range
                if begin == end:
                    continue
                assert begin == cursor
                cursor = end
            assert cursor == count


def test_closed_relation_declarations_are_deterministic_and_closed(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    chain = relation.dependent_chain_plan
    source = render_closed_relation_declarations(chain, "GeneratedClosedStateFixture")
    assert source == render_closed_relation_declarations(chain, "GeneratedClosedStateFixture")
    assert "def fact_000000 : RelationFact" in source
    assert "def state_000000 : RelationState" in source
    assert ".ordinary" in source and ".zigzag" in source
    assert ".packedCu" in source and ".tensorEq" in source
    assert "nonempty := by decide" in source
    assert source.rstrip().endswith("end\nend TrainVerify.Denote.GeneratedClosedStateFixture")
    assert "True" not in source and "False.elim" not in source and "sorry" not in source


def test_closed_float_segment_renderer_is_graph_derived(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    chain = relation.dependent_chain_plan
    segment = next(
        item for item in chain.segments
        if len(item.transition_ids) == 1
        and relation.transition_specs[
            next(i for i, transition in enumerate(relation.transition_specs)
                 if transition.transition_id == item.transition_ids[0])
        ].lean_theorem == "TrainVerify.Denote.fw_float_allGather0_commute_2"
    )
    source = render_closed_float_segment(ir, relation, segment.segment_id)
    assert "ClosedDepSegmentCertificate" in source
    assert "applyNode_fw_float_out" in source
    assert "RelationState.Holds.fold_frame" in source
    assert "4934" in source and "7754" in source and "7755" in source
    assert "sorry" not in source and "False.elim" not in source


def test_closed_multiref_segment_renderer_is_graph_derived(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    by_id = {item.transition_id: item for item in relation.transition_specs}
    segment = next(
        item for item in relation.dependent_chain_plan.segments
        if item.transition_ids
        and all(
            by_id[tid].lean_theorem
            == "TrainVerify.Denote.fw_multiref_allGather0_commute_2"
            for tid in item.transition_ids
        )
    )
    source = render_closed_multiref_segment(ir, relation, segment.segment_id)
    assert f"private def {segment.segment_id}" in source
    assert "foldl_faithful_multiref_middle_writer" in source
    assert "RelationState.Holds.fold_frame" in source
    assert "native_decide" in source


def test_closed_rms_norm_segment_renderer_is_graph_derived(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    by_id = {item.transition_id: item for item in relation.transition_specs}
    segment = next(item for item in relation.dependent_chain_plan.segments
        if len(item.transition_ids) == 1 and by_id[item.transition_ids[0]].lean_theorem.endswith("fw_rms_norm_allGather0_commute_2_core"))
    source = render_closed_rms_norm_segment(ir, relation, segment.segment_id)
    assert "Ordinary2Rel.rms_norm_2d" in source
    assert "authority_replicated_eq_" in source
    assert "applyNode_fw_rms_norm_out_1p" in source


@pytest.mark.parametrize("goal", [1, 3])
def test_closed_rms_norm_renderer_covers_all_zigzag_singletons(monkeypatch, goal):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(goal, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    by_id = {item.transition_id: item for item in relation.transition_specs}
    segments = [
        item for item in relation.dependent_chain_plan.segments
        if len(item.transition_ids) == 1
        and by_id[item.transition_ids[0]].rule_id == "rms-norm-zigzag-two-rank"
    ]
    assert len(segments) == 23
    facts = {fact.source: fact for fact in relation.dependent_chain_plan.relation_facts}
    for segment in segments:
        transition = by_id[segment.transition_ids[0]]
        post = facts[transition.post_facts[0]]
        source = render_closed_rms_norm_segment(ir, relation, segment.segment_id)
        assert "GeneratedPatterns.Zigzag2Rel.rms_norm" in source
        assert f"pmFinal {post.metadata_tid}" in source
        assert f"pmStore {post.metadata_tid}" in source
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1


def test_closed_atomic_rms_shuffle_renderer_is_single_fold_and_dispatched(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(
        ir, compile_proof_plan(ir, build_default_registry())
    )

    segment = relation.dependent_chain_plan.segments[255]
    source = render_closed_rms_shuffle_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (471, 473)
    assert segment.pm_range == (1042, 1046)
    assert "RelationCompiler.Ordinary2Rel.to_zigzag_shuffle" in source
    assert "GeneratedPatterns.Ordinary2Rel.rms_norm_2d" in source
    assert "ZigzagCollective.PackedCuSeqlensWF" in source
    assert "authority_replicated_eq_5596" in source
    assert "authority_packed_cu_000000" in source
    assert "authority_pm_metadata_eq_000000_5602" in source
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert render_closed_segment(ir, relation, segment.segment_id) == source


def test_closed_atomic_rms_shuffle_renderer_rejects_bad_shuffle_params(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(
        ir, compile_proof_plan(ir, build_default_registry())
    )
    segment = relation.dependent_chain_plan.segments[255]
    ir.sm_nodes[segment.sm_range[0] + 1].params = [2, 0]

    with pytest.raises(ValueError, match="shuffle signature/params"):
        render_closed_rms_shuffle_segment(ir, relation, segment.segment_id)


def test_closed_multiref_renderer_handles_mixed_atomic_groups(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = relation.dependent_chain_plan.segments[256]
    source = render_closed_multiref_segment(ir, relation, segment.segment_id)
    assert segment.sm_range == (473, 475) and segment.pm_range == (1046, 1050)
    assert source.count("foldl_faithful_multiref_middle_writer") == 12
    assert "hmeta_" in source
    assert "smNodes := [" in source and "pmNodes := [" in source


def test_closed_initial_component_renderer_uses_exact_public_graphs(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_initial_component(ir, relation, "segment_000000")
    assert ir.sm_graph_ref in source and ir.pm_graph_ref in source
    assert "foldl_faithful_binary_middle_writer" in source
    assert source.count("foldl_faithful_chunk_middle_writer") == 24
    assert "embedding_hidden_shards_allToAll_two" in source
    assert "smGraph pmGraph" not in source


def test_full_producer_certificates_use_registered_relation_compiler_theorems(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    forbidden = {
        "TrainVerify.Denote.Gather2Rel.norm_linear",
        "TrainVerify.Denote.Gather2Rel.per_head_mix_precision_linear",
        "TrainVerify.Denote.RelationCompiler.gather2Rel_of_full_eq_and_chunks",
    }
    theorem_keys = {t.lean_theorem for t in relation.transition_specs}
    assert not forbidden.intersection(theorem_keys)
    assert "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.per_head_linear_fullProducer_chunks" in theorem_keys
    assert "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.norm_linear_fullProducer_chunks" in theorem_keys


def test_full_producer_weight_authority_is_live_in_atomic_pre_state(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    chain = relation.dependent_chain_plan
    transitions = {t.transition_id: t for t in relation.transition_specs}
    segment = next(s for s in chain.segments if any(
        transitions[t].rule_id == "FW_per_head_mix_precision_linear-full-producer-chunks-ordinary-two-rank"
        for t in s.transition_ids
    ))
    pre = next(s for s in chain.states if s.state_id == segment.pre_state_id)
    authority = {a.fact_id: a for a in chain.authority_facts}
    live = [authority[f] for f in pre.fact_ids if f in authority]
    assert any(a.kind == "tensor_eq" and a.left_tid == 4937 and a.right_tid == 4937 for a in live)
    assert any(a.kind == "tensor_shape" and a.side == "pm" and a.tid == 4937 and a.shape == (16, 64, 1024) for a in live)


def test_closed_linear_renderer_covers_mixed_full_producer_and_local_component(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_linear_segment(ir, relation, "segment_000005")
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert "Ordinary2Rel.per_head_linear_fullProducer_chunks" in source
    assert source.count("Ordinary2Rel.per_head_linear") >= 2
    assert "foldl_faithful_chunk_writer" in source
    assert "authority_replicated_eq_4937" in source
    assert "authority_replicated_shape_pm_4937" in source


def test_closed_linear_renderer_supports_ordinary_mix_precision_singleton(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_linear_segment(ir, relation, "segment_000010")
    assert "Ordinary2Rel.mix_precision_linear" in source
    assert "authority_replicated_eq_4953" in source
    assert source.count("let smFinal :=") == 1 and source.count("let pmFinal :=") == 1


def test_closed_linear_renderer_preserves_zigzag_metadata(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_linear_segment(ir, relation, "segment_000263")
    assert "Zigzag2Rel.mix_precision_linear" in source
    assert "5602" in source
    assert "Ordinary2Rel.mix_precision_linear" not in source


def test_closed_full_producer_to_renderer_is_atomic_generic_and_single_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    segment = relation.dependent_chain_plan.segments[259]

    source = render_closed_full_producer_to_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (480, 505) and segment.pm_range == (1060, 1113)
    assert len(segment.transition_ids) == 25
    assert "GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks" in source
    assert source.count("fw_to_allGather0_commute_2") == 24
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert f"private def {segment.segment_id}_sm_nodes" in source
    assert f"private def {segment.segment_id}_pm_nodes" in source
    assert "smNodes.take" in source and "pmNodes.take" in source
    assert render_closed_segment(ir, relation, segment.segment_id) == source


def test_closed_full_producer_to_renderer_recovers_to_roles_from_node_tids(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    segment = relation.dependent_chain_plan.segments[259]
    transition_id = segment.transition_ids[1]
    reordered = tuple(
        replace(item, pre_facts=tuple(reversed(item.pre_facts)))
        if item.transition_id == transition_id else item
        for item in relation.transition_specs
    )

    baseline = render_closed_full_producer_to_segment(ir, relation, segment.segment_id)
    assert render_closed_full_producer_to_segment(
        ir, replace(relation, transition_specs=reordered), segment.segment_id
    ) == baseline


def test_identity_view_rules_use_identity_relation_theorem(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    identity = [t for t in relation.transition_specs if t.rule_id in (
        "identity-view-ordinary-two-rank", "identity-reshape-ordinary-two-rank"
    )]
    assert identity
    assert {t.lean_theorem for t in identity} == {
        "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id"
    }


def test_closed_unary_renderer_covers_identity_view_and_reshape(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    ordinary = render_closed_unary_segment(ir, relation, "segment_000009")
    zigzag = render_closed_unary_segment(ir, relation, "segment_000264")
    assert "Ordinary2Rel.view_id" in ordinary
    assert "Zigzag2Rel.view_id" in zigzag and "5602" in zigzag
    for source in (ordinary, zigzag):
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert "RelationState.Holds.mono_insert" in source


@pytest.mark.parametrize("goal_n", [1, 2, 3, 4])
def test_closed_unary_renderer_covers_all_flatten_3d_segments(monkeypatch, goal_n):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(goal_n, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    transitions = {item.transition_id: item for item in relation.transition_specs}
    flatten_segments = [
        segment for segment in relation.dependent_chain_plan.segments
        if len(segment.transition_ids) == 1
        and transitions[segment.transition_ids[0]].rule_id.startswith("flatten-3d-")
    ]
    ordinary = [
        segment for segment in flatten_segments
        if transitions[segment.transition_ids[0]].rule_id == "flatten-3d-ordinary-two-rank"
    ]
    zigzag = [
        segment for segment in flatten_segments
        if transitions[segment.transition_ids[0]].rule_id == "flatten-3d-zigzag-two-rank"
    ]
    assert len(ordinary) == len(zigzag) == 12
    facts = {fact.source: fact for fact in relation.dependent_chain_plan.relation_facts}
    for segment in flatten_segments:
        transition = transitions[segment.transition_ids[0]]
        pre = facts[transition.pre_facts[0]]
        post = facts[transition.post_facts[0]]
        assert pre.full_shape == (pre.shard_shape[0] * 2, *pre.shard_shape[1:])
        assert post.full_shape == (pre.full_shape[0], pre.full_shape[1] * pre.full_shape[2])
        assert post.shard_shape == (pre.shard_shape[0], pre.shard_shape[1] * pre.shard_shape[2])
        if pre.kind == "zigzag":
            assert (post.metadata_tid, post.metadata_region_id) == (
                pre.metadata_tid, pre.metadata_region_id
            )
        source = render_closed_unary_segment(ir, relation, segment.segment_id)
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert "Ordinary2Rel.view_id" not in source
        assert "Zigzag2Rel.view_id" not in source
        if pre.kind == "ordinary":
            assert "fw_view_allGather0_commute_cp2" in source
        else:
            assert "Zigzag2Rel.view_3d_to_2d" in source
            assert str(pre.metadata_tid) in source


def test_closed_unary_renderer_covers_float_both_layouts(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    ordinary = render_closed_unary_segment(ir, relation, "segment_000001")
    zigzag = render_closed_unary_segment(ir, relation, "segment_000265")
    assert "Ordinary2Rel" in ordinary
    assert "Zigzag2Rel.fw_float" in zigzag and "5602" in zigzag


def test_closed_binary_renderer_covers_add_both_layouts(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    ordinary = render_closed_binary_segment(ir, relation, "segment_000013")
    zigzag = render_closed_binary_segment(ir, relation, "segment_000266")
    assert "Ordinary2Rel.add" in ordinary
    assert "Zigzag2Rel.add" in zigzag and "5602" in zigzag
    for source in (ordinary, zigzag):
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1


@pytest.mark.parametrize("goal", [1, 3])
def test_closed_binary_renderer_covers_broadcast_mul_both_layouts(monkeypatch, goal):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(goal, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    by_id = {item.transition_id: item for item in relation.transition_specs}
    segments = {}
    for item in relation.dependent_chain_plan.segments:
        if len(item.transition_ids) != 1:
            continue
        transition = by_id[item.transition_ids[0]]
        if transition.rule_id.startswith("broadcast-mul-"):
            kind = "zigzag" if "-zigzag-" in transition.rule_id else "ordinary"
            segments.setdefault(kind, item)
    ordinary = render_closed_binary_segment(ir, relation, segments["ordinary"].segment_id)
    zigzag = render_closed_binary_segment(ir, relation, segments["zigzag"].segment_id)
    assert "Ordinary2Rel.mul_broadcast_col1" in ordinary
    assert "Zigzag2Rel.mul_broadcast_col1" in zigzag
    assert "hmeta" in zigzag
    for source in (ordinary, zigzag):
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1


def test_routing_and_moe_transition_theorem_keys_are_real_closed_apis(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    keys = {transition.lean_theorem for transition in relation.transition_specs}
    assert "TrainVerify.Denote.GeneratedPatterns.fw_topk_routing_allGather0_commute_2" not in keys
    assert "TrainVerify.Denote.fw_all2all_moe_gmm_full_split_commute_2" not in keys
    assert "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.topk_routing_all" in keys
    assert "TrainVerify.Denote.GeneratedPatterns.fw_all2all_moe_gmm_full_split_commute_2" in keys


def test_moe_weight_gather_authority_is_live_at_atomic_consumer(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    chain = relation.dependent_chain_plan
    assert chain is not None
    gathers = {
        (fact.sm_tid, fact.pm_rank0_tid, fact.pm_rank1_tid): fact
        for fact in chain.authority_facts if fact.kind == "gather"
    }
    states = {state.state_id: state for state in chain.states}
    transitions = {transition.transition_id: transition for transition in relation.transition_specs}
    moe_types = (FrontierOrdinaryMoECertificate, FrontierZigzagFullMoECertificate)
    for certificate in (item for item in relation.certificates if isinstance(item, moe_types)):
        expected = []
        for full_binding, shard_bindings in zip(
            certificate.full_weight_bindings, certificate.shard_weight_bindings
        ):
            full_tid = int(full_binding.removeprefix("init:"))
            shard_tids = tuple(int(item.removeprefix("init:")) for item in shard_bindings)
            expected.append(gathers[(full_tid, *shard_tids)])
        target = RelationFactSpec(certificate.relation_kind, certificate.output_step_triple)
        segment = next(
            segment for segment in chain.segments
            if any(target in transitions[tid].post_facts for tid in segment.transition_ids)
        )
        pre_ids = set(states[segment.pre_state_id].fact_ids)
        assert {fact.fact_id for fact in expected} <= pre_ids
        assert all(fact.dim == 0 for fact in expected)


def test_ordinary_pointwise_transitions_use_closed_relation_wrappers(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    by_rule = {transition.rule_id: transition.lean_theorem for transition in relation.transition_specs}
    assert by_rule["sigmoid-ordinary-two-rank"] == "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.sigmoid"
    assert by_rule["swiglu-ordinary-two-rank"] == "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.swiglu"
    assert by_rule["attention-ordinary-qkv-two-rank"] == (
        "TrainVerify.Denote.GeneratedPatterns.applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair"
    )
    assert by_rule["broadcast-mul-ordinary-two-rank"] == (
        "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.mul_broadcast_col1"
    )


def test_closed_mixed_moe_renderer_materializes_each_exact_node_list_once(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_mixed_moe_segment(ir, relation, "segment_000017")
    assert source.count("private def segment_000017_sm_nodes") == 1
    assert source.count("private def segment_000017_pm_nodes") == 1
    assert "smNodes := segment_000017_sm_nodes" in source
    assert "pmNodes := segment_000017_pm_nodes" in source
    assert "let smNodes : List NodeDecl := segment_000017_sm_nodes" in source
    assert "let pmNodes : List NodeDecl := segment_000017_pm_nodes" in source
    assert len(source.encode()) < 2_500_000
    assert "[pmFinal 7848, pmFinal 7849]" in source
    assert "[pmFinal 7850, pmFinal 7851]" in source
    assert "[pmStore 7848, pmFinal 7849]" not in source
    assert "[pmFinal 7848, pmStore 7849]" not in source
    assert "_inputs" not in source
    assert "let smFold :=" not in source
    assert "let pmFold :=" not in source
    assert "at hval_" not in source
    assert source.count("private theorem segment_000017_sm_writer_values") == 1
    assert source.count("private theorem segment_000017_pm_writer_values") == 1
    assert source.count("segment_000017_sm_nodes.foldl") == 2
    assert source.count("segment_000017_pm_nodes.foldl") == 2
    sm_helper = source.split("private theorem segment_000017_sm_writer_values", 1)[1].split("private theorem", 1)[0]
    pm_helper = source.split("private theorem segment_000017_pm_writer_values", 1)[1].split("private theorem", 1)[0]
    assert "pmStore" not in sm_helper and "pmFinal" not in sm_helper
    assert "smStore" not in pm_helper and "smFinal" not in pm_helper


def test_closed_mixed_moe_renderer_is_one_exact_fold_for_both_layouts(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    for segment_id, layout in (("segment_000017", "ordinary"), ("segment_000270", "zigzag")):
        source = render_closed_mixed_moe_segment(ir, relation, segment_id)
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count("ClosedDepSegmentCertificate ") == 1
        assert "ClosedDepSegmentCertificateEq" in source
        assert ".toCertificate" in source
        assert "Holds smFinal pmFinal" in source
        assert "change smFinal =" not in source
        assert "change pmFinal =" not in source
        assert "foldl_faithful_middle_writer" in source
        assert "topk_routing_all" in source
        assert "all2all_moe_gmm" in source
        assert "sigmoid" in source and "swiglu" in source
        if layout == "ordinary":
            assert "Ordinary2Rel.toGather2Rel" in source
        assert layout in source

def test_closed_segment_dispatch_is_explicit_and_fail_closed(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    for segment_id in ("segment_000000", "segment_000001", "segment_000002", "segment_000003", "segment_000004", "segment_000005"):
        source = render_closed_segment(ir, relation, segment_id)
        assert segment_id in source
    source = render_closed_segment(ir, relation, "segment_000006")
    assert "Ordinary2Rel.rotary_embedding_1d" in source
    with pytest.raises(ValueError, match="unsupported closed segment family.*attention-ordinary-qkv-two-rank"):
        render_closed_segment(ir, relation, "segment_000007")

def test_closed_atomic_per_head_zigzag_rms_renderer_is_exact_single_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))

    source = render_closed_segment(ir, relation, "segment_000257")

    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("ClosedDepSegmentCertificate ") == 1
    assert source.count("Ordinary2Rel.per_head_linear ") == 2
    assert source.count("GeneratedPatterns.Zigzag2Rel.rms_norm") == 1
    assert "smNodes := [{ rank := 0, op := \"OpName.FW_per_head_mix_precision_linear\", ins := [8376, 5598]" in source
    assert "pmNodes := [{ rank := 0, op := \"OpName.FW_per_head_mix_precision_linear\", ins := [15838, 5598]" in source
    assert "authority_replicated_eq_5598.Holds" in source
    assert "authority_replicated_eq_5600.Holds" in source
    assert "authority_replicated_eq_5604.Holds" in source
    assert "pmFinal 5602 = pmStore 5602" in source
    assert "metadata_region_id" not in source


def test_closed_chain_composer_advances_past_atomic_per_head_zigzag_rms(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    with pytest.raises(ValueError) as exc:
        compose_closed_dependent_chain(ir, relation, "ClosedGoal1")
    assert "segment_000257" not in str(exc.value)
    assert "segment_000265" not in str(exc.value)
    assert "segment_000278" in str(exc.value)

def test_closed_chain_composer_assembles_complete_path_independently_of_renderers(monkeypatch):
    anchor = SimpleNamespace(
        fact_id="anchor_fact", kind="tensor_shape", side="sm", tid=7, shape=(1,)
    )
    states = tuple(
        SimpleNamespace(state_id=f"state_{index:06d}", fact_ids=("anchor_fact",))
        for index in range(3)
    )
    segments = (
        SimpleNamespace(
            segment_id="segment_concrete",
            pre_state_id=states[0].state_id,
            post_state_id=states[1].state_id,
            transition_ids=("transition_concrete",),
        ),
        SimpleNamespace(
            segment_id="segment_parameterized",
            pre_state_id=states[1].state_id,
            post_state_id=states[2].state_id,
            transition_ids=("transition_parameterized",),
        ),
    )
    chain = SimpleNamespace(
        complete=True,
        relation_facts=(),
        authority_facts=(),
        anchor_fact=anchor,
        states=states,
        segments=segments,
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain,
        transition_specs=(
            SimpleNamespace(transition_id="transition_concrete", rule_id="synthetic-concrete"),
            SimpleNamespace(transition_id="transition_parameterized", rule_id="synthetic-parameterized"),
        ),
    )
    ir = SimpleNamespace(
        sm_graph_ref="Synthetic.Graphs.smGraph",
        pm_graph_ref="Synthetic.Graphs.pmGraph",
        public_statement_module="Synthetic.Graphs",
    )

    rendered = {
        "segment_concrete": (
            "private def segment_concrete :\n"
            "    ClosedDepSegmentCertificate Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph "
            "state_000000 state_000001 := by\n"
            "  exact syntheticConcreteCertificate\n"
        ),
        "segment_parameterized": (
            "private def segment_parameterized\n"
            "    (smGraph pmGraph : GraphDecl) :\n"
            "    ClosedDepSegmentCertificate smGraph pmGraph state_000001 state_000002 := by\n"
            "  exact syntheticParameterizedCertificate smGraph pmGraph\n"
        ),
    }
    monkeypatch.setattr(
        composer_module,
        "render_closed_segment",
        lambda _ir, _relation, segment_id: rendered[segment_id],
    )

    source = compose_closed_dependent_chain(ir, relation, "SyntheticClosedChain")

    assert source.startswith(
        "/- AUTO-GENERATED closed relation state universe. -/\n"
        "import denote.RelationCompiler\n"
        "import Synthetic.Graphs\n"
    )
    assert source.count("namespace TrainVerify.Denote.SyntheticClosedChain") == 1
    assert source.rstrip().endswith("end\nend TrainVerify.Denote.SyntheticClosedChain")
    assert source.index("private def segment_concrete") < source.index(
        "end TrainVerify.Denote.SyntheticClosedChain"
    )
    assert "ClosedDepCertificateChain Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph state_000002 state_000002" in source
    assert "ClosedDepCertificateChain Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph state_000001 state_000002" in source
    assert "ClosedDepCertificateChain Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph state_000000 state_000002" in source
    assert "  .cons segment_concrete SyntheticClosedChain_suffix_000001" in source
    assert (
        "  .cons segment_parameterized Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph "
        "SyntheticClosedChain_suffix_000002"
    ) in source
    assert "theorem SyntheticClosedChain_chain_sm_nodes : SyntheticClosedChain_chain.smNodes = Synthetic.Graphs.smGraph.nodes := by\n  native_decide" in source
    assert "theorem SyntheticClosedChain_chain_pm_nodes : SyntheticClosedChain_chain.pmNodes = Synthetic.Graphs.pmGraph.nodes := by\n  native_decide" in source


def test_closed_rotary_renderer_is_two_output_and_uses_1d_generic_theorem(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_rotary_segment(ir, relation, "segment_000006")
    assert "Ordinary2Rel.rotary_embedding_1d" in source
    assert "fw_rotary_embedding_allGather0_commute_2" not in source
    assert "fact_000628.Holds" in source
    assert "fact_000629.Holds" in source
    assert source.count("let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph)") == 1
    assert source.count("let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph)") == 1


def test_closed_ordinary_attention_renderer_uses_exact_buddy_reconstruction(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = render_closed_attention_segment(ir, relation, "segment_000007")
    assert "Ordinary2Rel.sliding_attention" in source
    assert "applyNodeDistributedFaithful_sliding_attn_out" in source
    assert "applyNode_FW_attn" not in source
    assert source.count("let smFinal := smNodes.foldl (applyNodeDistributedFaithful") == 1
    assert source.count("let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful") == 1
    assert ir.sm_graph_ref in source and ir.pm_graph_ref in source
    authority_ids = {item.fact_id for item in relation.dependent_chain_plan.authority_facts}
    assert {"authority_replicated_eq_4947", "authority_replicated_eq_4948"} <= authority_ids


def test_closed_zigzag_attention_renderer_is_faithful_and_generic(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal in (1, 2):
        ir = load_goal_ir(goal, str(root))
        relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
        transitions = {item.transition_id: item for item in relation.transition_specs}
        segment_ids = [
            item.segment_id for item in relation.dependent_chain_plan.segments
            if tuple(transitions[tid].rule_id for tid in item.transition_ids)
            == ("attention-zigzag-qkv-two-rank",)
        ]
        assert len(segment_ids) == 12
        for segment_id in segment_ids:
            source = render_closed_attention_segment(ir, relation, segment_id)
            assert "GeneratedPatterns.Zigzag2Rel.attn_zigzag_sharded_kv" in source
            assert source.count("Ordinary2Rel.toGather2Rel") == 2
            assert source.count("applyNodeDistributedFaithful_zigzag_attn_out") == 3
            assert ".decoded_single" in source
            assert source.count("let smFinal := smNodes.foldl (applyNodeDistributedFaithful") == 1
            assert source.count("let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful") == 1
            assert ir.sm_graph_ref in source and ir.pm_graph_ref in source


def test_closed_zigzag_attention_roles_and_metadata_fail_closed(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    baseline = render_closed_attention_segment(ir, relation, "segment_000260")
    segment = next(item for item in relation.dependent_chain_plan.segments
                   if item.segment_id == "segment_000260")
    transition_id = segment.transition_ids[0]
    reordered = tuple(
        replace(item, pre_facts=tuple(reversed(item.pre_facts)))
        if item.transition_id == transition_id else item
        for item in relation.transition_specs
    )
    assert render_closed_attention_segment(
        ir, replace(relation, transition_specs=reordered), "segment_000260") == baseline

    chain = relation.dependent_chain_plan
    aliasless = tuple(
        item for item in chain.authority_facts
        if item.fact_id != "authority_pm_metadata_eq_000000_5610"
    )
    with pytest.raises(ValueError, match="exact metadata alias"):
        render_closed_attention_segment(
            ir,
            replace(relation, dependent_chain_plan=replace(chain, authority_facts=aliasless)),
            "segment_000260",
        )
    packedless = tuple(item for item in chain.authority_facts if item.kind != "packed_cu")
    with pytest.raises(ValueError, match="PackedCu authority"):
        render_closed_attention_segment(
            ir,
            replace(relation, dependent_chain_plan=replace(chain, authority_facts=packedless)),
            "segment_000260",
        )


def test_mixed_moe_roles_are_tid_driven_and_params_are_not_model_literals(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    baseline = render_closed_mixed_moe_segment(ir, relation, "segment_000017")
    segment = next(item for item in relation.dependent_chain_plan.segments
                   if item.segment_id == "segment_000017")
    moe_tid = segment.transition_ids[11]
    reordered = tuple(
        replace(item, pre_facts=tuple(reversed(item.pre_facts))) if item.transition_id == moe_tid else item
        for item in relation.transition_specs
    )
    assert render_closed_mixed_moe_segment(
        ir, replace(relation, transition_specs=reordered), "segment_000017") == baseline

    transition = next(item for item in relation.transition_specs if item.transition_id == moe_tid)
    sm_nodes, pm_nodes = list(ir.sm_nodes), list(ir.pm_nodes)
    for side, indices, nodes in (("sm", transition.sm_node_indices, sm_nodes),
                                 ("pm", transition.pm_node_indices, pm_nodes)):
        for index in indices:
            node = nodes[index]
            if node.op != "FW_all2all_moe_gmm":
                continue
            params = list(node.params)
            params[0], params[3] = 96, 4
            nodes[index] = replace(node, params=params)
    perturbed = render_closed_mixed_moe_segment(
        replace(ir, sm_nodes=sm_nodes, pm_nodes=pm_nodes), relation, "segment_000017")
    assert "] 96 4 (((10 : Nat) : Scalar))" in perturbed


def test_mixed_zigzag_rejects_metadata_region_alias(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    chain = relation.dependent_chain_plan
    segment = next(item for item in chain.segments if item.segment_id == "segment_000270")
    transitions = {item.transition_id: item for item in relation.transition_specs}
    live_sources = {source for tid in segment.transition_ids
                    for source in (*transitions[tid].pre_facts, *transitions[tid].post_facts)}
    changed = False
    records = []
    for record in chain.relation_facts:
        if (not changed and record.source in live_sources
                and record.kind == "zigzag" and record.metadata_tid == 5602):
            records.append(replace(record, metadata_region_id=record.metadata_region_id + 1))
            changed = True
        else:
            records.append(record)
    assert changed
    bad = replace(relation, dependent_chain_plan=replace(chain, relation_facts=tuple(records)))
    with pytest.raises(ValueError, match="one exact metadata region"):
        render_closed_mixed_moe_segment(ir, bad, "segment_000270")
