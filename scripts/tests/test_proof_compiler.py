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
import trainverify.bridge_emitter.proof_compiler as proof_compiler_module
import trainverify.bridge_emitter.relation_compiler as relation_compiler_module
import trainverify.bridge_emitter.plan as plan_module
from scripts.tests.real_goal_cache import compiled_goal, planned_goal


def _bind_certificate_digest(transition, certificate):
    return replace(
        transition,
        certificate_digest=composer_module._typed_certificate_digest(certificate),
    )


from trainverify.bridge_emitter.composer import (
    CompositionCode,
    compose_closed_dependent_bundle,
    compose_closed_dependent_chain,
    compose_full_topology,
    render_closed_attention_segment,
    render_closed_binary_segment,
    render_closed_ce_fst_segment,
    render_closed_ce_snd_segment,
    render_closed_external_initial_state,
    render_closed_float_segment,
    render_closed_full_producer_to_segment,
    render_closed_indexed_stack_segment,
    render_closed_initial_component,
    render_closed_linear_segment,
    render_closed_mixed_moe_segment,
    render_closed_multiref_segment,
    render_closed_public_theorem,
    render_closed_relation_declarations,
    render_closed_rms_norm_segment,
    render_closed_rms_shuffle_segment,
    render_closed_rotary_segment,
    render_closed_segment,
    render_closed_unary_segment,
    render_closed_unshuffle_segment,
)
from trainverify.bridge_emitter.emit2 import (
    _compile_closed_bundle_sources,
    _publish_closed_bundle,
    _publish_composed_source,
)
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


def test_multirank_backward_attention_ops_have_graph_aware_rules():
    registry = build_default_registry()
    expected = {
        "BW_attn_sliding_window": "applyNodeRingAttn_bw_sliding_window",
        "BW_attn_zigzag": "applyNodeRingAttn_bw_zigzag",
    }
    for op, denote_fn in expected.items():
        assert op not in proof_compiler_module.MULTIRANK_VALUE_LOSSY_OPERATORS
        rule = registry.get(op)
        assert rule is not None
        assert rule.denote_fn == denote_fn
        assert rule.apply_lemmas


@pytest.mark.parametrize("op", ("BW_attn_sliding_window", "BW_attn_zigzag"))
def test_multirank_backward_attention_ops_accept_complete_buddy_authority(op):
    rank1_inputs = [11, 13, 15, 17, 18, 19]
    if op == "BW_attn_zigzag":
        rank1_inputs[2:4] = [14, 16]
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, op, [10, 12, 14, 16, 18, 19], [70, 71, 72], [1, 1, 4, 4, 1, 0]),
            Node(1, op, rank1_inputs, [73, 74, 75], [1, 1, 4, 4, 1, 0]),
        ],
        tps=[(0, 70), (1, 73)],
    )
    ir.pm_shapes.extend((tid, [4, 4]) for tid in range(12, 18))
    ir.pm_shapes.extend(((18, [2]), (19, [2])))
    ir.pm_replica_groups = (
        parser_module.ReplicaGroup(
            cid=2,
            mb=0,
            irname=op,
            members=(
                parser_module.ReplicaNodeRef(0, 70),
                parser_module.ReplicaNodeRef(1, 73),
            ),
        ),
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True, plan.diagnostics


@pytest.mark.parametrize(
    "op",
    (
        "BW_attn_sliding_window",
        "BW_attn_zigzag",
    ),
)
def test_multirank_backward_attention_ops_reject_incomplete_buddy_authority(op):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, op, [10], [40])],
        tps=[(0, 40)],
    )
    ir.pm_num_ranks = 2
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert "complete ordered replica buddies" in plan.diagnostics[0].message


@pytest.mark.parametrize("shared_input", (2, 3, None))
def test_multirank_backward_zigzag_attention_rejects_unauthorized_kv_ownership(shared_input):
    rank0 = [10, 12, 14, 16, 18, 19]
    rank1 = [11, 13, 15, 17, 18, 19]
    if shared_input is not None:
        rank1[shared_input] = rank0[shared_input]
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, "BW_attn_zigzag", rank0, [70, 71, 72], [1, 1, 4, 4, 1, 0]),
            Node(1, "BW_attn_zigzag", rank1, [73, 74, 75], [1, 1, 4, 4, 1, 0]),
        ],
        tps=[(0, 70), (1, 73)],
    )
    ir.pm_shapes.extend((tid, [4, 4]) for tid in range(12, 18))
    ir.pm_shapes.extend(((18, [2]), (19, [2])))
    ir.pm_replica_groups = (
        parser_module.ReplicaGroup(
            cid=3,
            mb=0,
            irname="BW_attn_zigzag",
            members=(
                parser_module.ReplicaNodeRef(0, 70),
                parser_module.ReplicaNodeRef(1, 73),
            ),
        ),
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert "coherent Q/K/V ownership" in plan.diagnostics[0].message


@pytest.mark.parametrize("op", ("BW_maybe_shuffle", "BW_maybe_unshuffle"))
def test_multirank_backward_permutation_ops_use_graph_aware_semantics(op):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, op, [10, 12], [40], [2, 0]),
            Node(1, op, [11, 12], [41], [2, 1]),
        ],
        tps=[(0, 40), (1, 41)],
    )
    ir.pm_shapes.append((12, [2]))
    ir.pm_num_ranks = 2
    ir.pm_replica_groups = (
        parser_module.ReplicaGroup(
            cid=1,
            mb=0,
            irname=op,
            members=(
                parser_module.ReplicaNodeRef(0, 40),
                parser_module.ReplicaNodeRef(1, 41),
            ),
        ),
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is True, plan.diagnostics
    pm_step = next(step for step in plan.steps if step.side == "pm")
    expected_effect = (
        RelationEffect.ZIGZAG_TO_ORDINARY
        if op == "BW_maybe_shuffle"
        else RelationEffect.ORDINARY_TO_ZIGZAG
    )
    assert pm_step.relation_effect is expected_effect


@pytest.mark.parametrize("op", ("BW_maybe_shuffle", "BW_maybe_unshuffle"))
def test_multirank_backward_permutation_ops_reject_incomplete_buddy_authority(op):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, op, [10, 11], [40], [2, 0])],
        tps=[(0, 40)],
    )
    ir.pm_num_ranks = 2
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert "complete ordered replica buddies" in plan.diagnostics[0].message


@pytest.mark.parametrize("op", ("BW_maybe_shuffle", "BW_maybe_unshuffle"))
def test_multirank_backward_permutation_uniform_bad_arity_reaches_signature_diagnostic(op):
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[
            Node(0, op, [10], [40], [2, 0]),
            Node(1, op, [11], [41], [2, 1]),
        ],
        tps=[(0, 40), (1, 41)],
    )
    ir.pm_num_ranks = 2
    ir.pm_replica_groups = (
        parser_module.ReplicaGroup(
            cid=1,
            mb=0,
            irname=op,
            members=(
                parser_module.ReplicaNodeRef(0, 40),
                parser_module.ReplicaNodeRef(1, 41),
            ),
        ),
    )
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_SIGNATURE
    assert plan.diagnostics[0].message == (
        f"operator {op} has no signature variant: expected 2 inputs, got 1"
    )


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

    ir.lineage.tps = [(0, 40)]
    plan = compile_proof_plan(ir, registry)
    assert plan.supported is False
    assert plan.diagnostics[0].code is DiagnosticCode.INVALID_LINEAGE

    ir.lineage.tps = [(1, 40)]
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
        assert relation.schema_version == 7
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


def test_gpt_goal3_matches_dynamic_k_sequence_sharded_embedding(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir, proof = planned_goal(3, str(root))

    cert = relation_compiler_module.match_k_rank_sharded_ids_embedding_terminal(
        ir, proof
    )

    assert cert.rule_id == "embedding-sharded-ids-k-rank"
    assert cert.rank_count == 4
    assert cert.shard_dim == 1
    assert cert.sm_embedding_step == "sm:1:0"
    assert cert.pm_chunk_steps == ("pm:1:0", "pm:3:0", "pm:5:0", "pm:7:0")
    assert cert.pm_embedding_steps == ("pm:8:0", "pm:9:0", "pm:10:0", "pm:12:0")
    assert cert.ids_tid == 716 and cert.weight_tid == 565
    assert cert.output_fact == RelationFactSpec(
        "sharded", tuple(proof.target_steps), gather_dim=1
    )


def test_gpt_goal3_renders_sparse_dynamic_k_sequence_embedding(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = compiled_goal(3, str(root))
    segment = relation.dependent_chain_plan.segments[0]

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (0, 236) and segment.pm_range == (0, 1565)
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("foldl_faithful_middle_writer") == 9
    assert "private theorem segment_000000_hSmEmbedding" in source
    assert "private theorem segment_000000_hChunk0" in source
    assert "private theorem segment_000000_hPmEmbedding3" in source
    assert "ShardedRel.fw_embedding_shared_weight_dim1" in source
    assert "ChunkedRel (smFinal 716) idsShards 1" in source
    assert "hIds.toShardedRel hWeightEq hWeightLast" in source
    assert "allGatherPrimDimN_chunks_ofFn" in source
    assert "rankCount = 4" not in source
    assert "Goal_3" not in source and "sorry" not in source


def test_gpt_goal3_publication_accepts_ordered_sharded_terminal(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = compiled_goal(3, str(root))

    source = render_closed_public_theorem(ir, relation, "ClosedGPT2Goal3")

    assert "htarget.shard_shapes" in source
    assert source.count("have hPmPlain") == 4
    assert "reconstructForGoal_of_not_replicated" in source
    assert "joined terminal" not in source


def test_gpt_goal4_uses_generic_direct_gather_fixed_point(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(4, str(root))
    proof = compile_proof_plan(ir, build_default_registry())

    relation = compile_relation_plan(ir, proof)

    rules = tuple(item.rule_id for item in relation.transition_specs)
    assert relation.family == "direct-gather-k-rank"
    assert relation.unresolved_frontiers == ()
    assert relation.unresolved_layouts == ()
    assert sum(slot.kind == "semantic" for slot in relation.coverage_plan.sm_nodes) == 3
    assert sum(slot.kind == "semantic" for slot in relation.coverage_plan.pm_nodes) == 25
    assert "add-sharded-k-rank" in rules
    assert "embedding-sharded-ids-k-rank" in rules
    assert "embedding-vocab-sharded-reduction-k-rank" in rules
    assert "allreduce-reconstruction-k-rank" in rules
    assert "alltoall-k-rank-layout-transport" in rules
    assert "full-producer-chunks-k-rank" in rules


def test_gpt_goal4_renders_interleaved_initial_embedding_scc(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(4, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)

    source = render_closed_segment(ir, relation, "segment_000000")

    assert "embedding-vocab-sharded-reduction-k-rank" not in source
    assert "segment_000000_sequence_out" in source
    assert "segment_000000_vocab_out" in source
    assert "segment_000000_joined_out" in source
    assert source.count("foldl (applyNodeDistributedFaithful") >= 2
    assert "rankCount = 4" not in source and "Goal_4" not in source


def test_gpt_goal5_renders_sparse_full_frame_layernorm(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(5, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(x for x in relation.dependent_chain_plan.segments
                   if x.segment_id == "segment_000006")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (4, 236) and segment.pm_range == (33, 1565)
    assert source.count("@[irreducible] private def segment_000006_smFinal") == 1
    assert source.count("@[irreducible] private def segment_000006_pmFinal") == 1
    assert "private theorem segment_000006_smWriter" in source
    assert "private theorem segment_000006_pmWriter3" in source
    assert "smNodes.take 0" in source
    assert "pmNodes.take 0" in source
    assert "rankCount = 4" not in source


def test_gpt_goal16_renders_interleaved_local_linear_tuple_once(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(16, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000008")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (6, 8) and segment.pm_range == (41, 50)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert "pmNodes.take 7" in source
    assert "pmNodes.take 8" in source
    assert "hLocalOut0" in source and "hLocalOut1" in source


def test_gpt_goal16_renders_sparse_contraction_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(16, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000019")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (16, 236) and segment.pm_range == (101, 105)
    assert "smNodes.take 0" in source
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1


def test_gpt_goal17_renders_sparse_div_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(17, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000022")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    assert all(f"pmNodes.take {index - segment.pm_range[0]}" in source
               for index in transition.pm_node_indices)


def test_gpt_goal18_renders_sparse_softmax_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(18, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000024")

    source = render_closed_segment(ir, relation, segment.segment_id)

    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert all(f"pmNodes.take {index - segment.pm_range[0]}" in source
               for index in transition.pm_node_indices)


def test_gpt_goal19_renders_sparse_output_axis_matmul_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(19, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000031")

    source = render_closed_segment(ir, relation, segment.segment_id)

    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert all(f"pmNodes.take {index - segment.pm_range[0]}" in source
               for index in transition.pm_node_indices)


def test_gpt_goal21_renders_sparse_contiguous_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(21, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000034")

    source = render_closed_segment(ir, relation, segment.segment_id)

    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert all(f"pmNodes.take {index - segment.pm_range[0]}" in source
               for index in transition.pm_node_indices)


def test_gpt_goal23_splits_large_sparse_output_linear_proof(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(23, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000037")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "@[irreducible] private def segment_000037_smFinal" in source
    assert "@[irreducible] private def segment_000037_pmFinal" in source
    assert "private theorem segment_000037_smWriter" in source
    assert "private theorem segment_000037_pmWriter3" in source
    assert "private theorem segment_000037_out" in source
    assert "private theorem segment_000037_sound" in source


def test_gpt_goal27_renders_sparse_gelu_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(27, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000044")

    source = render_closed_segment(ir, relation, segment.segment_id)

    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    frame_only = next(index for index in range(*segment.pm_range)
                      if index not in transition.pm_node_indices)
    assert composer_module._node_text(ir.pm_nodes[frame_only]) in source
    assert "@[irreducible] private def segment_000044_smFinal" in source
    assert "@[irreducible] private def segment_000044_pmFinal" in source
    assert "private theorem segment_000044_smWriter" in source
    assert "private theorem segment_000044_pmWriter3" in source
    assert "private theorem segment_000044_out" in source
    assert "private theorem segment_000044_sound" in source


def test_gpt_goal28_splits_large_sparse_local_linear_proof(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(28, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000046")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "@[irreducible] private def segment_000046_smFinal" in source
    assert "@[irreducible] private def segment_000046_pmFinal" in source
    assert "private theorem segment_000046_smWriter" in source
    assert "private theorem segment_000046_pmWriter3" in source
    assert "private theorem segment_000046_out" in source
    assert "private theorem segment_000046_sound" in source


def test_gpt_goal31_renders_sparse_reduction_linear_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(31, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000054")

    source = render_closed_segment(ir, relation, segment.segment_id)

    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert all(f"pmNodes.take {index - segment.pm_range[0]}" in source
               for index in transition.pm_node_indices)


def test_gpt_goal41_renders_sparse_mixed_linear_sequence_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(41, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000053")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "@[irreducible] private def segment_000053_smFinal" in source
    assert "@[irreducible] private def segment_000053_pmFinal" in source
    frame_transition_indices = {
        index for tid in segment.transition_ids
        for transition in relation.transition_specs if transition.transition_id == tid
        for index in transition.pm_node_indices
    }
    frame_only = next(index for index in range(*segment.pm_range)
                      if index not in frame_transition_indices)
    assert composer_module._node_text(ir.pm_nodes[frame_only]) in source


def test_gpt_goal41_renders_sparse_head_axis_matmul_full_frame(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(41, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000064")

    source = render_closed_segment(ir, relation, segment.segment_id)

    transition = next(t for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert all(f"pmNodes.take {index - segment.pm_range[0]}" in source
               for index in transition.pm_node_indices)


def test_gpt_goal44_renders_joined_views_and_allreduce_atomically(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(44, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000055")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "@[irreducible] private def segment_000055_smFinal" in source
    assert "@[irreducible] private def segment_000055_pmFinal" in source
    assert "private theorem segment_000055_viewOut0" in source
    assert "private theorem segment_000055_viewOut1" in source
    assert "private theorem segment_000055_allReduceOut" in source
    assert "private theorem segment_000055_publish" in source


def test_gpt_goal44_renders_transpose_tuple_and_chunks_atomically(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(44, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000059")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "@[irreducible] private def segment_000059_smFinal" in source
    assert "@[irreducible] private def segment_000059_pmFinal" in source
    assert "private theorem segment_000059_transposeOut0" in source
    assert "private theorem segment_000059_transposeOut1" in source
    assert "private theorem segment_000059_chunksOut" in source
    assert "show 4 = TrainVerify.Denote.Generated.pm.numRanks by rfl" in source
    assert "private theorem segment_000059_publish" in source


def test_gpt_goal107_mixed_linear_collective_tuple_is_atomic(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(107, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000097")
    transitions = {item.transition_id: item for item in relation.transition_specs}

    assert tuple(transitions[item].rule_id for item in segment.transition_ids) == (
        "linear-sharded-k-rank-dim1",
        "allgather-reconstruction-k-rank",
        "linear-output-sharded-k-rank",
        "allgather-reconstruction-k-rank",
        "linear-output-sharded-k-rank",
    )
    assert segment.sm_range == (62, 65)
    assert segment.pm_range == (400, 414)
    source = render_closed_segment(ir, relation, segment.segment_id)
    assert source.count(
        "@[irreducible] private def segment_000097_smFinal"
    ) == 1
    assert source.count(
        "@[irreducible] private def segment_000097_pmFinal"
    ) == 1
    assert source.count("fw_linear_3d_allGatherPrimDimN_dim1_comm") == 1
    assert source.count("RelationCompiler.ShardedRel.to_joined_allGather") == 2
    assert source.count("fw_linear_3d_weight_allGatherPrimDimN_dim0_comm") == 2
    assert "private theorem segment_000097_publish_state" in source

    bw_sum = next(s for s in relation.dependent_chain_plan.segments
                  if s.segment_id == "segment_000188")
    assert tuple(transitions[item].rule_id for item in bw_sum.transition_ids) == (
        "bw-sum-scalar-broadcast-dim2-k-rank",
    )
    bw_sum_source = render_closed_segment(ir, relation, bw_sum.segment_id)
    assert "private def segment_000188" in bw_sum_source
    assert "bw_sum_allGatherPrimDimN_dim2_rank3" in bw_sum_source
    assert "have hcomm : bw_sum" in bw_sum_source
    assert "simpa only [List.length_cons, List.length_nil, List.map] using" in bw_sum_source

    bw_linear_dx = next(s for s in relation.dependent_chain_plan.segments
                        if s.segment_id == "segment_000189")
    assert tuple(transitions[item].rule_id for item in bw_linear_dx.transition_ids) == (
        "bw-linear-dx-row-reduction-k-rank",
    )
    assert bw_linear_dx.sm_range == (119, 120)
    assert bw_linear_dx.pm_range == (779, 784)
    bw_linear_dx_source = render_closed_segment(ir, relation, bw_linear_dx.segment_id)
    assert "private def segment_000189" in bw_linear_dx_source
    assert "bw_linear_dx_row_reduction_rank3" in bw_linear_dx_source
    assert "bw_linear_dx_tp_split_dim2_4_g134" not in bw_linear_dx_source

    bw_layernorm_dx = next(s for s in relation.dependent_chain_plan.segments
                           if s.segment_id == "segment_000192")
    assert tuple(transitions[item].rule_id for item in bw_layernorm_dx.transition_ids) == (
        "bw-layernorm-dx-dim1-k-rank",
    )
    bw_layernorm_dx_source = render_closed_segment(
        ir, relation, bw_layernorm_dx.segment_id
    )
    assert "private def segment_000192" in bw_layernorm_dx_source
    assert "bw_layernorm_dx_allGatherPrimDimN_dim1_3d" in bw_layernorm_dx_source

    bw_add = next(s for s in relation.dependent_chain_plan.segments
                  if s.segment_id == "segment_000193")
    assert tuple(transitions[item].rule_id for item in bw_add.transition_ids) == (
        "bw-add-identity-sharded-k-rank",
        "bw-add-identity-sharded-k-rank",
    )
    bw_add_source = render_closed_segment(ir, relation, bw_add.segment_id)
    assert "private def segment_000193" in bw_add_source
    assert "bw_add2_fst_same_shape" in bw_add_source
    assert "bw_add2_snd_same_shape" in bw_add_source

    bw_linear_column = next(s for s in relation.dependent_chain_plan.segments
                            if s.segment_id == "segment_000195")
    assert tuple(transitions[item].rule_id for item in bw_linear_column.transition_ids) == (
        "bw-linear-dx-column-sharded-k-rank",
    )
    bw_linear_column_source = render_closed_segment(
        ir, relation, bw_linear_column.segment_id
    )
    assert "private def segment_000195" in bw_linear_column_source
    assert "bw_linear_dx_column_allGather_rank3" in bw_linear_column_source

    bw_gelu = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000197")
    assert tuple(transitions[item].rule_id for item in bw_gelu.transition_ids) == (
        "bw-gelu-pointwise-sharded-k-rank",
    )
    bw_gelu_source = render_closed_segment(ir, relation, bw_gelu.segment_id)
    assert "private def segment_000197" in bw_gelu_source
    assert "bw_gelu_allGatherPrimDimN_eq" in bw_gelu_source

    bw_multiref = next(s for s in relation.dependent_chain_plan.segments
                       if s.segment_id == "segment_000202")
    assert tuple(transitions[item].rule_id for item in bw_multiref.transition_ids) == (
        "bw-multiref-sum-sharded-k-rank",
    )
    bw_multiref_source = render_closed_segment(ir, relation, bw_multiref.segment_id)
    assert "private def segment_000202" in bw_multiref_source
    assert transitions[bw_multiref.transition_ids[0]].lean_theorem in bw_multiref_source

    bw_view = next(s for s in relation.dependent_chain_plan.segments
                   if s.segment_id == "segment_000207")
    assert tuple(transitions[item].rule_id for item in bw_view.transition_ids) == (
        "bw-view-joined",
    )
    bw_view_source = render_closed_segment(ir, relation, bw_view.segment_id)
    assert "private def segment_000207" in bw_view_source
    assert "JoinedRel.fw_view" in bw_view_source

    bw_contiguous = next(s for s in relation.dependent_chain_plan.segments
                         if s.segment_id == "segment_000209")
    assert tuple(transitions[item].rule_id for item in bw_contiguous.transition_ids) == (
        "contiguous-sharded-k-rank",
    )
    bw_contiguous_source = render_closed_segment(
        ir, relation, bw_contiguous.segment_id
    )
    assert "private def segment_000209" in bw_contiguous_source
    assert "applyNode_bw_contiguous_out" in bw_contiguous_source

    bw_transpose = next(s for s in relation.dependent_chain_plan.segments
                        if s.segment_id == "segment_000211")
    assert tuple(transitions[item].rule_id for item in bw_transpose.transition_ids) == (
        "transpose-sharded-k-rank",
    )
    bw_transpose_source = render_closed_segment(
        ir, relation, bw_transpose.segment_id
    )
    assert "private def segment_000211" in bw_transpose_source
    assert "applyNode_bw_transposeAxes_out" in bw_transpose_source

    bw_matmul = next(s for s in relation.dependent_chain_plan.segments
                     if s.segment_id == "segment_000213")
    assert tuple(transitions[item].rule_id for item in bw_matmul.transition_ids) == (
        "bw-matmul-snd-g-sharded-rank4",
        "bw-matmul-fst-contraction-reduction-rank4",
    )
    bw_matmul_source = render_closed_segment(ir, relation, bw_matmul.segment_id)
    assert "private def segment_000213" in bw_matmul_source
    assert all(transitions[item].lean_theorem in bw_matmul_source
               for item in bw_matmul.transition_ids)

    bw_softmax = next(s for s in relation.dependent_chain_plan.segments
                      if s.segment_id == "segment_000217")
    assert tuple(transitions[item].rule_id for item in bw_softmax.transition_ids) == (
        "transpose-sharded-k-rank",
        "bw-softmax-sharded-dim1-rank4",
    )
    bw_softmax_source = render_closed_segment(ir, relation, bw_softmax.segment_id)
    assert "private def segment_000217" in bw_softmax_source

    bw_div = next(s for s in relation.dependent_chain_plan.segments
                  if s.segment_id == "segment_000220")
    assert tuple(transitions[item].rule_id for item in bw_div.transition_ids) == (
        "bw-view-joined",
        "div-sharded-k-rank-dim2",
    )
    bw_div_source = render_closed_segment(ir, relation, bw_div.segment_id)
    assert "private def segment_000220" in bw_div_source

    bw_attention = next(s for s in relation.dependent_chain_plan.segments
                        if s.segment_id == "segment_000223")
    assert tuple(transitions[item].rule_id for item in bw_attention.transition_ids) == (
        "bw-linear-dx-sequence-sharded-k-rank",
        "bw-matmul-batch-sharded-rank4",
        "bw-matmul-batch-sharded-rank4",
    )
    bw_attention_source = render_closed_segment(
        ir, relation, bw_attention.segment_id
    )
    assert "private def segment_000223" in bw_attention_source

    transpose_alltoall = next(s for s in relation.dependent_chain_plan.segments
                              if s.segment_id == "segment_000224")
    assert tuple(transitions[item].rule_id for item in transpose_alltoall.transition_ids) == (
        "transpose-sharded-k-rank",
        "alltoall-k-rank-layout-transport",
        "transpose-sharded-k-rank",
    )
    transpose_alltoall_source = render_closed_segment(
        ir, relation, transpose_alltoall.segment_id
    )
    assert "private def segment_000224" in transpose_alltoall_source

    view_transpose = next(s for s in relation.dependent_chain_plan.segments
                          if s.segment_id == "segment_000227")
    assert tuple(transitions[item].rule_id for item in view_transpose.transition_ids) == (
        "bw-view-joined",
        "transpose-sharded-k-rank",
    )
    view_transpose_source = render_closed_segment(
        ir, relation, view_transpose.segment_id
    )
    assert "private def segment_000227" in view_transpose_source

    mixed_backward = next(s for s in relation.dependent_chain_plan.segments
                          if s.segment_id == "segment_000228")
    assert tuple(transitions[item].rule_id for item in mixed_backward.transition_ids) == (
        "bw-linear-dx-column-sharded-k-rank",
        "allgather-reconstruction-k-rank",
        "bw-view-joined",
        "alltoall-k-rank-layout-transport",
    )
    mixed_backward_source = render_closed_segment(
        ir, relation, mixed_backward.segment_id
    )
    assert "private def segment_000228" in mixed_backward_source
    assert "bw_linear_dx_column_allGather_rank3" in mixed_backward_source
    column_certs = [c for c in relation.certificates
                    if getattr(c, "family", None) == "column-sharded"]
    assert column_certs and all(c.rule_id == "bw-linear-dx-column-sharded-k-rank"
                               for c in column_certs)
    # Exercise the real compound, not only synthetic singleton records.
    from copy import copy
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    linear_transition = transitions[mixed_backward.transition_ids[0]]
    linear_cert = next(c for c in column_certs
                       if c.sm_step_id == f"sm:{linear_transition.sm_node_indices[0]}:0")
    for mutated_cert in (replace(linear_cert, gather_dim=1),
                         replace(linear_cert, pm_step_ids=tuple(reversed(linear_cert.pm_step_ids)))):
        bad_relation = replace(relation,
            certificates=tuple(mutated_cert if c is linear_cert else c
                               for c in relation.certificates),
            transition_specs=tuple(
                replace(t, certificate_digest=_typed_certificate_digest(mutated_cert))
                if t is linear_transition else t for t in relation.transition_specs))
        with pytest.raises(ValueError):
            render_closed_segment(ir, bad_relation, mixed_backward.segment_id)
    for tr_id, changes in (
            (mixed_backward.transition_ids[2], {"input_shape": (9,)}),
            (mixed_backward.transition_ids[2], {"sm_step_id": "sm:0:0"}),
            (mixed_backward.transition_ids[2], {"pm_step_id": "pm:0:0"}),
            (mixed_backward.transition_ids[1], {"gather_dim": -1}),
            (mixed_backward.transition_ids[1], {"full_shape": (9,)}),
            (mixed_backward.transition_ids[1], {"shard_shape": (9,)}),
            (mixed_backward.transition_ids[1], {"pm_allgather_step": "pm:0:0"}),
            (mixed_backward.transition_ids[-1], {"input_gather_dim": 1}),
            (mixed_backward.transition_ids[-1], {"output_gather_dim": 2}),
            (mixed_backward.transition_ids[-1], {"pm_step_ids": ("pm:0:0",)})):
        tr = transitions[tr_id]
        cert = next(c for c in relation.certificates
                    if c.rule_id == tr.rule_id and c.lean_theorem == tr.lean_theorem
                    and _typed_certificate_digest(c) == tr.certificate_digest)
        mutated = replace(cert, **changes)
        bad_relation = replace(relation,
            certificates=tuple(mutated if c is cert else c for c in relation.certificates),
            transition_specs=tuple(replace(t, certificate_digest=_typed_certificate_digest(mutated))
                                   if t is tr else t for t in relation.transition_specs))
        with pytest.raises(ValueError):
            render_closed_segment(ir, bad_relation, mixed_backward.segment_id)
    bad_ir = copy(ir)
    bad_ir.pm_nodes = list(ir.pm_nodes)
    linear_index = linear_transition.pm_node_indices[0]
    bad_ir.pm_nodes[linear_index] = replace(ir.pm_nodes[linear_index], params=[1])
    with pytest.raises(ValueError):
        render_closed_segment(bad_ir, relation, mixed_backward.segment_id)

    triple_multiref = next(s for s in relation.dependent_chain_plan.segments
                           if s.segment_id == "segment_000231")
    assert tuple(transitions[item].rule_id for item in triple_multiref.transition_ids) == (
        "bw-multiref-sum-sharded-k-rank",
    )
    triple_multiref_source = render_closed_segment(
        ir, relation, triple_multiref.segment_id
    )
    assert "private def segment_000231" in triple_multiref_source

    paired_batch_matmul = next(s for s in relation.dependent_chain_plan.segments
                               if s.segment_id == "segment_000254")
    assert tuple(transitions[item].rule_id for item in paired_batch_matmul.transition_ids) == (
        "bw-matmul-batch-sharded-rank4",
        "bw-matmul-batch-sharded-rank4",
    )
    paired_batch_matmul_source = render_closed_segment(
        ir, relation, paired_batch_matmul.segment_id
    )
    assert "private def segment_000254" in paired_batch_matmul_source

    softmax_transpose = next(s for s in relation.dependent_chain_plan.segments
                             if s.segment_id == "segment_000256")
    assert tuple(transitions[item].rule_id for item in softmax_transpose.transition_ids) == (
        "bw-softmax-sharded-dim2-rank4",
        "transpose-sharded-k-rank",
    )
    softmax_transpose_source = render_closed_segment(
        ir, relation, softmax_transpose.segment_id
    )
    assert "private def segment_000256" in softmax_transpose_source

    backward_div = next(s for s in relation.dependent_chain_plan.segments
                        if s.segment_id == "segment_000257")
    assert tuple(transitions[item].rule_id for item in backward_div.transition_ids) == (
        "div-sharded-k-rank-dim2",
    )
    backward_div_source = render_closed_segment(
        ir, relation, backward_div.segment_id
    )
    assert "private def segment_000257" in backward_div_source

    matmul_view = next(s for s in relation.dependent_chain_plan.segments
                       if s.segment_id == "segment_000259")
    assert tuple(transitions[item].rule_id for item in matmul_view.transition_ids) == (
        "bw-matmul-fst-query-sharded-k-rank",
        "bw-matmul-snd-contraction-reduction-k-rank",
        "bw-view-joined",
    )
    matmul_view_source = render_closed_segment(ir, relation, matmul_view.segment_id)
    assert "private def segment_000259" in matmul_view_source

    transpose_linear_transpose = next(s for s in relation.dependent_chain_plan.segments
                                      if s.segment_id == "segment_000264")
    assert tuple(transitions[item].rule_id for item in transpose_linear_transpose.transition_ids) == (
        "transpose-sharded-k-rank",
        "bw-linear-dx-sequence-sharded-k-rank",
        "transpose-sharded-k-rank",
    )
    transpose_linear_transpose_source = render_closed_segment(
        ir, relation, transpose_linear_transpose.segment_id
    )
    assert "private def segment_000264" in transpose_linear_transpose_source

    row_linear_view = next(s for s in relation.dependent_chain_plan.segments
                           if s.segment_id == "segment_000270")
    assert tuple(transitions[item].rule_id for item in row_linear_view.transition_ids) == (
        "bw-linear-dx-row-reduction-k-rank",
        "bw-view-joined",
    )
    row_linear_view_source = render_closed_segment(
        ir, relation, row_linear_view.segment_id
    )
    assert "private def segment_000270" in row_linear_view_source

    wide_row_linear = next(s for s in relation.dependent_chain_plan.segments
                           if s.segment_id == "segment_000282")
    assert tuple(transitions[item].rule_id for item in wide_row_linear.transition_ids) == (
        "bw-linear-dx-row-reduction-k-rank",
    )
    assert transitions[wide_row_linear.transition_ids[0]].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dx_row_reduction_rank3"
    )
    wide_row_linear_source = render_closed_segment(
        ir, relation, wide_row_linear.segment_id
    )
    assert "private def segment_000282" in wide_row_linear_source

    dim2_pair_sum = next(s for s in relation.dependent_chain_plan.segments
                         if s.segment_id == "segment_000292")
    assert tuple(transitions[item].rule_id for item in dim2_pair_sum.transition_ids) == (
        "bw-multiref-sum-sharded-k-rank",
    )
    assert transitions[dim2_pair_sum.transition_ids[0]].lean_theorem == (
        "TrainVerify.Denote.tensorSum_allGather_dim_K"
    )
    dim2_pair_sum_source = render_closed_segment(
        ir, relation, dim2_pair_sum.segment_id
    )
    assert "private def segment_000292" in dim2_pair_sum_source

    sequence_linear = next(s for s in relation.dependent_chain_plan.segments
                           if s.segment_id == "segment_000295")
    assert tuple(transitions[item].rule_id for item in sequence_linear.transition_ids) == (
        "bw-linear-dx-sequence-sharded-k-rank",
    )
    sequence_linear_source = render_closed_segment(
        ir, relation, sequence_linear.segment_id
    )
    assert "private def segment_000295" in sequence_linear_source

    dual_axis_matmul = next(s for s in relation.dependent_chain_plan.segments
                            if s.segment_id == "segment_000303")
    assert tuple(transitions[item].rule_id for item in dual_axis_matmul.transition_ids) == (
        "bw-matmul-snd-x-sharded-rank4",
        "bw-matmul-fst-y-sharded-rank4",
    )
    dual_axis_matmul_source = render_closed_segment(
        ir, relation, dual_axis_matmul.segment_id
    )
    assert "private def segment_000303" in dual_axis_matmul_source

    dim3_transpose_softmax = next(s for s in relation.dependent_chain_plan.segments
                                  if s.segment_id == "segment_000305")
    assert tuple(transitions[item].rule_id for item in dim3_transpose_softmax.transition_ids) == (
        "bw-softmax-sharded-dim2-rank4",
        "transpose-sharded-k-rank",
    )
    dim3_transpose_softmax_source = render_closed_segment(
        ir, relation, dim3_transpose_softmax.segment_id
    )
    assert "private def segment_000305" in dim3_transpose_softmax_source

    interleaved_alltoall = next(s for s in relation.dependent_chain_plan.segments
                                if s.segment_id == "segment_000312")
    assert tuple(transitions[item].rule_id for item in interleaved_alltoall.transition_ids) == (
        "alltoall-k-rank-layout-transport",
        "alltoall-k-rank-layout-transport",
    )
    interleaved_alltoall_source = render_closed_segment(
        ir, relation, interleaved_alltoall.segment_id
    )
    assert "private def segment_000312" in interleaved_alltoall_source

    column_linear_view = next(s for s in relation.dependent_chain_plan.segments
                              if s.segment_id == "segment_000320")
    assert tuple(transitions[item].rule_id for item in column_linear_view.transition_ids) == (
        "bw-linear-dx-column-sharded-k-rank",
        "bw-view-joined",
    )
    column_linear_view_source = render_closed_segment(
        ir, relation, column_linear_view.segment_id
    )
    assert "private def segment_000320" in column_linear_view_source

    wide_sequence_linear = next(s for s in relation.dependent_chain_plan.segments
                                if s.segment_id == "segment_000330")
    assert tuple(transitions[item].rule_id for item in wide_sequence_linear.transition_ids) == (
        "bw-linear-dx-sequence-sharded-k-rank",
    )
    assert transitions[wide_sequence_linear.transition_ids[0]].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3"
    )
    wide_sequence_linear_source = render_closed_segment(
        ir, relation, wide_sequence_linear.segment_id
    )
    assert "private def segment_000330" in wide_sequence_linear_source

    reconstruction_softmax = next(s for s in relation.dependent_chain_plan.segments
                                   if s.segment_id == "segment_000348")
    assert tuple(transitions[item].rule_id for item in reconstruction_softmax.transition_ids) == (
        "transpose-sharded-k-rank",
        "allreduce-reconstruction-k-rank",
        "full-producer-chunks-k-rank",
        "bw-softmax-sharded-dim2-rank4",
        "allgather-reconstruction-k-rank",
    )
    reconstruction_softmax_source = render_closed_segment(
        ir, relation, reconstruction_softmax.segment_id
    )
    assert "private def segment_000348" in reconstruction_softmax_source

    view_alltoall_div_chunks = next(s for s in relation.dependent_chain_plan.segments
                                    if s.segment_id == "segment_000349")
    assert tuple(transitions[item].rule_id for item in view_alltoall_div_chunks.transition_ids) == (
        "bw-view-joined",
        "alltoall-k-rank-layout-transport",
        "div-sharded-k-rank-dim1",
        "full-producer-chunks-k-rank",
    )
    view_alltoall_div_chunks_source = render_closed_segment(
        ir, relation, view_alltoall_div_chunks.segment_id
    )
    assert "private def segment_000349" in view_alltoall_div_chunks_source

    linear_matmul_reconstruction = next(s for s in relation.dependent_chain_plan.segments
                                        if s.segment_id == "segment_000350")
    assert tuple(transitions[item].rule_id for item in linear_matmul_reconstruction.transition_ids) == (
        "bw-linear-dx-row-reduction-k-rank",
        "allgather-reconstruction-k-rank",
        "bw-matmul-fst-y-sharded-rank4",
        "bw-matmul-snd-x-sharded-rank4",
        "allreduce-reconstruction-k-rank",
    )
    linear_matmul_reconstruction_source = render_closed_segment(
        ir, relation, linear_matmul_reconstruction.segment_id
    )
    assert "private def segment_000350" in linear_matmul_reconstruction_source

    framed_sequence_linear = next(s for s in relation.dependent_chain_plan.segments
                                  if s.segment_id == "segment_000362")
    assert tuple(transitions[item].rule_id for item in framed_sequence_linear.transition_ids) == (
        "bw-linear-dx-sequence-sharded-k-rank",
    )
    framed_sequence_linear_source = render_closed_segment(
        ir, relation, framed_sequence_linear.segment_id
    )
    assert "private def segment_000362" in framed_sequence_linear_source

    singleton_bw_add_projection = next(s for s in relation.dependent_chain_plan.segments
                                       if s.segment_id == "segment_000367")
    assert tuple(transitions[item].rule_id for item in singleton_bw_add_projection.transition_ids) == (
        "bw-add-identity-sharded-k-rank",
    )
    singleton_bw_add_projection_source = render_closed_segment(
        ir, relation, singleton_bw_add_projection.segment_id
    )
    assert "private def segment_000367" in singleton_bw_add_projection_source

    sparse_vocab_embedding = next(s for s in relation.dependent_chain_plan.segments
                                  if s.segment_id == "segment_000369")
    assert tuple(transitions[item].rule_id for item in sparse_vocab_embedding.transition_ids) == (
        "bw-embedding-vocab-sharded-k-rank",
    )
    sparse_vocab_embedding_source = render_closed_segment(
        ir, relation, sparse_vocab_embedding.segment_id
    )
    assert "private def segment_000369" in sparse_vocab_embedding_source

    public_source = render_closed_public_theorem(ir, relation, "Goal107ClosedProbe")
    assert "Goal107ClosedProbe_sharded_target_publication" in public_source

    bundle = compose_closed_dependent_bundle(
        ir, relation, "Goal107ClosedProbe", "denote.gpt_ly4_regen.Goal107ClosedProbe"
    )
    assert b"import denote.KRankTranspose23Extra" in bundle["Segment000224.lean"]
    assert b"import denote.KRankMatmulQueryAxis" in bundle["Segment000259.lean"]
    assert b"have hvalueExact : initSM 568 = initPM 568" in bundle["Public.lean"]
    assert b"shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide" in bundle["Public.lean"]
    assert b"simpa only [List.length_cons, List.length_nil, allReducePrim_singleton_eq] using hp" in bundle["Public.lean"]


def test_yoco3b_ce_projection_gather_reports_missing_public_contract_before_generic_fallback(
    monkeypatch,
):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCO3B.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote")
    root = Path(__file__).resolve().parents[2]
    ir, proof = planned_goal(1, str(root))

    with pytest.raises(
        RelationCompositionError,
        match="CE .fst labels lack the exact public value-bound contract",
    ):
        compile_relation_plan(ir, proof)


def test_gpt_goal9_duplicate_tid_lineage_names_cross_rank_final_writer(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(9, str(root))

    proof = compile_proof_plan(ir, build_default_registry())

    assert ir.lineage.tps == [(3, 577)]
    assert proof.supported is True
    assert all(item.code is not DiagnosticCode.INVALID_LINEAGE for item in proof.diagnostics)



def test_ce_terminal_relation_plan_normalizes_the_backbone(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    assert certificates[0].lean_theorem == (
        "TrainVerify.Denote.GeneratedPatterns."
        "fw_inner_chunk_ce_fst_allGather0_commute_2_of"
    )
    assert "snd_allGatherDim0" in certificates[1].lean_theorem
    assert certificates[1].label_independence_theorem == (
        "TrainVerify.Denote.RelationCompiler."
        "inner_chunk_ce_snd_labels_independent"
    )
    assert all(item.input_step_triple for item in certificates)
    assert all(item.weight_binding == "init:6256" for item in certificates)
    assert all(item.label_binding == "init:4931" for item in certificates)


def test_ce_terminal_transition_requires_input_and_public_authority(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    registry = build_default_registry()

    requirements = []
    for goal_id in (1, 2):
        ir = load_goal_ir(goal_id, str(root))
        proof = compile_proof_plan(ir, registry)
        certificate = match_inner_chunk_ce_projection_gather_two_rank(ir, proof)
        transition = build_certificate_transition_specs(proof, (certificate,))[0]
        expected_pre = [RelationFactSpec("ordinary", certificate.input_step_triple)]
        if goal_id == 1:
            expected_pre.append(
                RelationFactSpec("label_chunks", certificate.label_chunk_step_triple)
            )
        assert transition.pre_facts == tuple(sorted(expected_pre))
        assert transition.post_facts
        requirements.append({item.kind for item in transition.authority_requirements})

    assert requirements[0] == {"tensor_eq", "tensor_shape", "label_bound"}
    assert requirements[1] == {"tensor_eq", "tensor_shape"}


def test_goal1_ce_fst_retains_truthful_label_chunks_through_terminal(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = compiled_goal(1, str(root))
    terminal = next(item for item in relation.transition_specs
                    if item.rule_id == "inner-chunk-ce-projection-gather-two-rank")
    chunk_source = RelationFactSpec(
        "label_chunks", ("init:4931", "pm:13:0", "pm:27:0")
    )
    assert chunk_source in terminal.pre_facts
    chunk_fact = next(item for item in relation.dependent_chain_plan.relation_facts
                      if item.source == chunk_source)
    assert (chunk_fact.kind, chunk_fact.sm_tid, chunk_fact.pm_rank0_tid,
            chunk_fact.pm_rank1_tid, chunk_fact.full_shape,
            chunk_fact.shard_shape) == (
        "label_chunks", 4931, 11714, 11715, (4096,), (2048,)
    )
    terminal_segment = relation.dependent_chain_plan.segments[-1]
    terminal_state = next(item for item in relation.dependent_chain_plan.states
                          if item.state_id == terminal_segment.pre_state_id)
    assert chunk_fact.fact_id in terminal_state.fact_ids


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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        1, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(3, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
    certs = [item for item in relation.certificates if getattr(item, "rule_id", "") == "init-lineage-full-to-two-chunks"]
    assert certs
    assert len({item.sm_tid for item in certs}) == len(certs)
    assert len({item.chunk_step_pair for item in certs}) == len(certs)
    assert all(item.full_shape == (4096,) for item in certs)
    assert all(item.shard_shape == (2048,) for item in certs)
    assert all(item.lean_theorem.endswith("allGatherPrimDimN_chunkPrimDimN_id_dim0_2") for item in certs)
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
    ir, proof = planned_goal(3, str(root))
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof, relation = compiled_goal(
        3, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
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
    ir, proof = planned_goal(3, str(root))
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
    ir, proof = planned_goal(3, str(root))
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
    ir, proof = planned_goal(3, str(root))
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
    ir, proof = planned_goal(3, str(root))
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
    ir, proof, relation = compiled_goal(3, str(root))
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
    ir, proof = planned_goal(3, str(root))
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


def test_compile_proof_plan_alltoall_matches_denote_dims_and_declared_shape():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_gelu", [1], [30])],
        pm_nodes=[Node(0, "AllToAllPrim", [10, 11, 12, 13], [40], [1, 2])],
        tps=[(0, 40)],
        replicated=True,
    )
    ir.sm_shapes = [(1, [1, 32, 2])]
    ir.pm_shapes = [
        (10, [1, 8, 8]), (11, [1, 8, 8]),
        (12, [1, 8, 8]), (13, [1, 8, 8]),
    ]
    ir.pm_num_ranks = 4
    ir.lineage.tsShape = [1, 32, 2]
    ir.lineage.tpShapes = [[1, 32, 2]]
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported
    pm = next(step for step in plan.steps if step.side == "pm")
    assert pm.output_shape == (1, 32, 2)

    ir.pm_shapes.append((40, [1, 2, 32]))
    plan = compile_proof_plan(ir, build_default_registry())
    assert not plan.supported
    assert plan.diagnostics[0].op == "AllToAllPrim"
    assert "conflicts with declared shape [1, 2, 32]" in plan.diagnostics[0].message


def test_compile_proof_plan_infers_batched_matmul_shape_and_rejects_bad_batch():
    ir = _goal_ir(
        sm_nodes=[Node(0, "FW_matmul", [1, 2], [30])],
        pm_nodes=[Node(0, "FW_matmul", [10, 11], [40])],
        tps=[(0, 40)],
        replicated=True,
    )
    ir.sm_shapes = [(1, [1, 4, 8, 8]), (2, [1, 4, 8, 8])]
    ir.pm_shapes = [(10, [1, 4, 8, 8]), (11, [1, 4, 8, 8])]
    ir.lineage.tsShape = [1, 4, 8, 8]
    ir.lineage.tpShapes = [[1, 4, 8, 8]]
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported
    assert all(step.output_shape == (1, 4, 8, 8) for step in plan.steps)

    ir.pm_shapes = [(10, [1, 4, 8, 8]), (11, [2, 4, 8, 8])]
    plan = compile_proof_plan(ir, build_default_registry())
    assert not plan.supported
    assert "batch dimensions differ" in plan.diagnostics[0].message


def test_compile_proof_plan_infers_bw_linear_multi_output_shapes():
    ir = _goal_ir(
        sm_nodes=[Node(0, "BW_linear", [1, 2, 3], [30, 31])],
        pm_nodes=[Node(0, "BW_linear", [10, 11, 12], [40, 41])],
        tps=[(0, 40)],
        replicated=True,
    )
    ir.sm_shapes = [(1, [1, 8, 128]), (2, [1, 8, 32]), (3, [128, 32])]
    ir.pm_shapes = [(10, [1, 8, 128]), (11, [1, 8, 32]), (12, [128, 32])]
    ir.lineage.tsShape = [1, 8, 32]
    ir.lineage.tpShapes = [[1, 8, 32]]
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported
    assert {(step.side, step.output_index, step.output_shape) for step in plan.steps} == {
        ("sm", 0, (1, 8, 32)), ("pm", 0, (1, 8, 32))
    }

    ir.lineage.ts = 31
    ir.lineage.tsShape = [128, 32]
    ir.lineage.tps = [(0, 41)]
    ir.lineage.tpShapes = [[128, 32]]
    plan = compile_proof_plan(ir, build_default_registry())
    assert plan.supported
    assert {(step.side, step.output_index, step.output_shape) for step in plan.steps} == {
        ("sm", 1, (128, 32)), ("pm", 1, (128, 32))
    }


def test_parse_full_init_goal_ids_accepts_compact_coarse_lineage_statement():
    statement = """
    def goal_1_stmt_full : Prop :=
      CoarseLineageHoldsWithInit sm pm goal_1 smInitEnv pmInitEnv initGoals
    """
    generated = """
    def initGoal_10 : LineageGoal := { ts := 10, tsShape := [2], tps := [{ rank := 0, tid := 20 }], tpShapes := [[2]] }
    def initGoal_11 : LineageGoal := { ts := 11, tsShape := [4], tps := [{ rank := 0, tid := 21 }], tpShapes := [[4]] }
    def initGoals : List LineageGoal := [initGoal_10, initGoal_11]
    """
    assert parser_module.parse_full_init_goal_ids(statement, generated, 1) == (10, 11)


def test_rule_registry_resolves_offset_embedding_as_distinct_semantic_identity():
    registry = build_default_registry()
    ordinary = Node(rank=0, op="FW_embedding", ins=[1, 2], outs=[3], params=[])
    offset = Node(rank=1, op="FW_embedding", ins=[1, 2], outs=[3], params=[256])
    malformed = Node(rank=1, op="FW_embedding", ins=[1, 2], outs=[3], params=[1, 2])

    ordinary_rule, ordinary_error = registry.resolve(ordinary, 4)
    offset_rule, offset_error = registry.resolve(offset, 4)
    malformed_rule, malformed_error = registry.resolve(malformed, 4)

    assert ordinary_error is None
    assert ordinary_rule.rule_id == "fw-embedding"
    assert ordinary_rule.denote_fn == "fw_embedding"
    assert ordinary_rule.apply_lemmas == ("applyNode_fw_embedding_out",)
    assert offset_error is None
    assert offset_rule.rule_id == "fw-embedding-offset"
    assert offset_rule.denote_fn == "fw_embedding_offset"
    assert offset_rule.apply_lemmas == ("applyNode_fw_embedding_offset_out",)
    assert malformed_rule is None
    assert "no signature variant" in malformed_error

    backward = Node(rank=2, op="BW_embedding", ins=[1, 2, 3], outs=[4], params=[512])
    backward_rule, backward_error = registry.resolve(backward, 4)
    assert backward_error is None
    assert backward_rule.rule_id == "bw-embedding-offset"
    assert backward_rule.denote_fn == "bw_embedding_offset"
    assert backward_rule.apply_lemmas == ("applyNode_bw_embedding_offset_out",)


def test_compile_proof_plan_infers_bw_sum_and_preserves_offset_embedding_identity():
    backward_sum = _goal_ir(
        sm_nodes=[Node(0, "BW_sum", [1, 2], [30])],
        pm_nodes=[Node(0, "BW_sum", [10, 11], [40])],
        tps=[(0, 40)],
        replicated=True,
    )
    backward_sum.sm_shapes = [(1, [1]), (2, [1, 8, 128])]
    backward_sum.pm_shapes = [(10, [1]), (11, [1, 8, 128])]
    backward_sum.lineage.tsShape = [1, 8, 128]
    backward_sum.lineage.tpShapes = [[1, 8, 128]]
    plan = compile_proof_plan(backward_sum, build_default_registry())
    assert plan.supported
    assert all(step.output_shape == (1, 8, 128) for step in plan.steps)

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
    assert plan.supported is True
    assert {step.rule_id for step in plan.steps} == {"fw-embedding-offset"}
    assert {step.denote_fn for step in plan.steps} == {"fw_embedding_offset"}
    assert {step.apply_lemmas for step in plan.steps} == {
        ("applyNode_fw_embedding_offset_out",)
    }

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
    assert decoded["schema_version"] == 5
    assert decoded["steps"][0]["rule_id"] == "fw-gelu"
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


def test_plan_closed_bundle_unsupported_is_json_and_exit1(monkeypatch, capsys):
    fake_plan = SimpleNamespace(
        supported=True,
        to_dict=lambda: {"status": "complete", "diagnostics": []},
    )
    monkeypatch.setattr(plan_module, "load_goal_ir", lambda *_: SimpleNamespace())
    monkeypatch.setattr(plan_module, "compile_proof_plan", lambda *_: fake_plan)
    monkeypatch.setattr(plan_module, "build_default_registry", lambda: object())
    monkeypatch.setattr(plan_module, "compile_relation_plan", lambda *_: object())
    monkeypatch.setattr(
        plan_module,
        "compose_closed_dependent_bundle",
        lambda *_: (_ for _ in ()).throw(ValueError("unsupported exact segment")),
    )
    assert plan_module.main(["1", "--closed-bundle", "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "unsupported"
    assert payload["certificate_source_complete"] is False
    assert payload["kernel_checked"] is False
    assert payload["proof_complete"] is False
    assert payload["composition"]["diagnostics"][0]["code"] == "composition.unsupported"


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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(3, str(root))
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
    ir, proof, relation = compiled_goal(3, str(root))
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



def test_indexed_stack_terminal_refuses_false_ordinary_dim0_publication(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = compiled_goal(3, str(root))

    terminal = next(
        transition for transition in relation.transition_specs
        if transition.rule_id == "indexed-stack-gather-two-rank"
    )
    assert len(terminal.post_facts) == 1
    target = terminal.post_facts[0]
    assert target.layout == "joined_indexed_stack_dim1"
    assert target.joined_pm_step is not None
    assert target.gather_dim == 1
    assert len(target.source_step_triples) == 24
    assert all(len(triple) == 3 for triple in target.source_step_triples)
    assert target not in {
        RelationFactSpec("ordinary", target.step_triple),
        RelationFactSpec("gather", target.step_triple),
    }
    assert relation.publication_diagnostics == ()
    assert relation.dependent_chain_plan is not None
    materialized = {
        fact.source: fact for fact in relation.dependent_chain_plan.relation_facts
    }[target]
    assert materialized.kind == "joined_indexed_stack_dim1"
    assert materialized.joined_pm_tid == ir.lineage.tps[0][1]
    assert materialized.gather_dim == 1
    assert len(materialized.source_tid_triples) == 24
    assert materialized.full_shape == (24, 4096, 64)
    assert materialized.shard_shape == (24, 2048, 64)
    source = render_closed_relation_declarations(
        relation.dependent_chain_plan, "GeneratedIndexedStackFixture"
    )
    declaration = source.split(
        f"private def {materialized.fact_id} : RelationFact :=", 1
    )[1].split("\n\n", 1)[0]
    assert ".joinedIndexedStack" in declaration
    assert ".ordinary" not in declaration
    assert declaration.count("(") >= 24


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
        external = frozenset(
            fact
            for transition in transitions
            for fact in transition.pre_facts
            if relation_compiler_module._is_external_relation_fact(fact)
        )
        dependencies = build_transition_dependency_plan(
            transitions, external_pre_facts=external
        )
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

    non_init_external = replace(
        transitions[-1].pre_facts[0],
        step_triple=("sm:999:0", "pm:999:0", "pm:1000:0"),
    )
    invalid_externalized = replace(
        transitions[-1], pre_facts=(non_init_external,)
    )
    with pytest.raises(
        RelationCompositionError,
        match="external pre-fact is not pure init authority",
    ):
        build_transition_dependency_plan(
            (*transitions[:-1], invalid_externalized),
            external_pre_facts=external | frozenset({non_init_external}),
        )


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
        external = frozenset(
            fact
            for transition in transitions
            for fact in transition.pre_facts
            if relation_compiler_module._is_external_relation_fact(fact)
        )
        schedule = build_atomic_schedule(
            ir, transitions, external_pre_facts=external
        )
        rerun = build_atomic_schedule(
            ir, tuple(reversed(transitions)), external_pre_facts=external
        )
        assert schedule.complete is True
        assert schedule.digest == rerun.digest
        assert schedule.order == rerun.order
        assert len(schedule.sm_node_components) == len(ir.sm_nodes)
        assert len(schedule.pm_node_components) == len(ir.pm_nodes)
        assert set(schedule.transition_components) == {item.transition_id for item in transitions}
        assert all(component.transition_ids for component in schedule.components)
        assert all(component.sm_range[1] >= component.sm_range[0] for component in schedule.components)
        changed_rule = replace(transitions[0], rule_id=transitions[0].rule_id + "-mutated")
        mutated = build_atomic_schedule(
            ir, (changed_rule, *transitions[1:]), external_pre_facts=external
        )
        assert mutated.transition_digest != schedule.transition_digest
        assert mutated.digest != schedule.digest
        assert all(component.pm_range[1] >= component.pm_range[0] for component in schedule.components)
        for transition in transitions:
            component_id = schedule.transition_components[transition.transition_id]
            assert all(schedule.sm_node_components[index] == component_id for index in transition.sm_node_indices)
            assert all(schedule.pm_node_components[index] == component_id for index in transition.pm_node_indices)
    broken = replace(transitions[-1], pm_node_indices=(len(ir.pm_nodes),))
    with pytest.raises(RelationCompositionError, match="out of bounds"):
        build_atomic_schedule(
            ir,
            (*transitions[:-1], broken),
            external_pre_facts=external,
        )


def test_k_rank_sum_allreduce_terminal_is_topology_and_shape_derived():
    sm_input = "sm:0:0"
    pm_inputs = tuple(f"pm:{rank}:0" for rank in range(4))
    sm_sum = "sm:1:0"
    pm_sums = tuple(f"pm:{rank + 4}:0" for rank in range(4))
    pm_reduce = "pm:8:0"
    steps = [
        SimpleNamespace(step_id=sm_input, side="sm", op="FW_linear", rank=0,
                        input_bindings=(), output_shape=(8, 4)),
        *(
            SimpleNamespace(step_id=ref, side="pm", op="FW_linear", rank=rank,
                            input_bindings=(), output_shape=(2, 4))
            for rank, ref in enumerate(pm_inputs)
        ),
        SimpleNamespace(step_id=sm_sum, side="sm", op="FW_sum", rank=0,
                        input_bindings=(sm_input,), output_shape=(1,)),
        *(
            SimpleNamespace(step_id=ref, side="pm", op="FW_sum", rank=rank,
                            input_bindings=(pm_inputs[rank],), output_shape=(1,))
            for rank, ref in enumerate(pm_sums)
        ),
        SimpleNamespace(step_id=pm_reduce, side="pm", op="AllReducePrim", rank=0,
                        input_bindings=pm_sums, output_shape=(1,)),
    ]
    proof = SimpleNamespace(
        steps=tuple(steps),
        target_steps=(sm_sum, pm_reduce),
    )
    ir = SimpleNamespace(sm_num_ranks=1, pm_num_ranks=4)

    terminal = relation_compiler_module.match_sum_allreduce_k_rank(ir, proof)

    assert terminal.rank_count == 4
    assert terminal.gather_dim == 0
    assert terminal.input_fact == RelationFactSpec(
        "sharded", (sm_input, *pm_inputs), gather_dim=0
    )
    assert terminal.sm_sum_step == sm_sum
    assert terminal.pm_sum_steps == pm_sums
    assert terminal.pm_allreduce_step == pm_reduce
    assert terminal.lean_theorem == (
        "TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum"
    )


def test_k_rank_sum_producer_decomposes_reduction_to_exact_dim1_shards():
    rank_count = 4
    sm_input = "sm:340:0"
    sm_sum = "sm:341:0"
    pm_inputs = tuple(f"pm:{2224 + rank}:0" for rank in range(rank_count))
    pm_sums = tuple(f"pm:{2228 + 2 * rank}:0" for rank in range(rank_count))
    full_shape = (1, 1024, 50257)
    shard_shape = (1, 256, 50257)
    steps = [
        SimpleNamespace(step_id=sm_input, side="sm", op="FW_identity", rank=0,
                        input_bindings=(), input_shapes=(), parameters=(),
                        output_shape=full_shape),
        *(SimpleNamespace(step_id=ref, side="pm", op="FW_identity", rank=rank,
                          input_bindings=(), input_shapes=(), parameters=(),
                          output_shape=shard_shape)
          for rank, ref in enumerate(pm_inputs)),
        SimpleNamespace(step_id=sm_sum, side="sm", op="FW_sum", rank=0,
                        input_bindings=(sm_input,), input_shapes=(full_shape,),
                        parameters=(), output_shape=(1,)),
        *(SimpleNamespace(step_id=ref, side="pm", op="FW_sum", rank=rank,
                          input_bindings=(pm_inputs[rank],), input_shapes=(shard_shape,),
                          parameters=(), output_shape=(1,))
          for rank, ref in enumerate(pm_sums)),
    ]
    reduction = RelationFactSpec("reduction", (sm_sum, *pm_sums))
    certificates, frontiers, layouts = (
        relation_compiler_module.advance_k_rank_sum_producer_frontiers(
            SimpleNamespace(steps=tuple(steps)),
            (reduction.step_triple,),
            ("reduction",),
        )
    )

    assert frontiers == ((sm_input, *pm_inputs),)
    assert layouts == ("sharded",)
    assert len(certificates) == 1
    certificate = certificates[0]
    assert certificate.rank_count == rank_count
    assert certificate.gather_dim == 1
    assert certificate.full_shape == full_shape
    assert certificate.shard_shape == shard_shape
    assert certificate.input_fact == RelationFactSpec(
        "sharded", (sm_input, *pm_inputs), gather_dim=1
    )
    assert certificate.output_fact == reduction
    assert certificate.sm_sum_step == sm_sum
    assert certificate.pm_sum_steps == pm_sums
    assert certificate.lean_theorem == (
        "TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum"
    )

    transitions = build_certificate_transition_specs(
        SimpleNamespace(steps=tuple(steps)), certificates
    )
    assert len(transitions) == 1
    assert transitions[0].pre_facts == (certificate.input_fact,)
    assert transitions[0].post_facts == (certificate.output_fact,)
    assert transitions[0].sm_node_indices == (341,)
    assert transitions[0].pm_node_indices == (2228, 2230, 2232, 2234)


def test_k_rank_linear_frontier_preserves_ordered_shards_and_external_weight():
    sm_input = "sm:0:0"
    pm_inputs = tuple(f"pm:{rank}:0" for rank in range(4))
    sm_output = "sm:1:0"
    pm_outputs = tuple(f"pm:{rank + 4}:0" for rank in range(4))
    steps = [
        SimpleNamespace(step_id=sm_input, side="sm", op="FW_identity", rank=0,
                        input_bindings=(), output_shape=(1, 8, 4)),
        *(
            SimpleNamespace(step_id=ref, side="pm", op="FW_identity", rank=rank,
                            input_bindings=(), output_shape=(1, 2, 4))
            for rank, ref in enumerate(pm_inputs)
        ),
        SimpleNamespace(step_id=sm_output, side="sm", op="FW_linear", rank=0,
                        input_bindings=(sm_input, "init:99"),
                        input_shapes=((1, 8, 4), (6, 4)), output_shape=(1, 8, 6)),
        *(
            SimpleNamespace(step_id=ref, side="pm", op="FW_linear", rank=rank,
                            input_bindings=(pm_inputs[rank], "init:99"),
                            input_shapes=((1, 2, 4), (6, 4)), output_shape=(1, 2, 6))
            for rank, ref in enumerate(pm_outputs)
        ),
    ]
    certificates, frontiers, layouts = (
        relation_compiler_module.advance_k_rank_linear_relation_frontiers(
            SimpleNamespace(steps=tuple(steps)),
            ((sm_output, *pm_outputs),),
            ("sharded",),
        )
    )
    assert frontiers == ((sm_input, *pm_inputs),)
    assert layouts == ("sharded",)
    assert len(certificates) == 1
    cert = certificates[0]
    assert cert.rank_count == 4
    assert cert.gather_dim == 1
    assert cert.external_weight_tid == 99
    assert cert.external_weight_shape == (6, 4)
    assert cert.input_fact == RelationFactSpec(
        "sharded", (sm_input, *pm_inputs), gather_dim=1
    )
    assert cert.output_fact == RelationFactSpec(
        "sharded", (sm_output, *pm_outputs), gather_dim=1
    )
    assert cert.lean_theorem.endswith("fw_linear_3d_allGatherPrimDimN_dim1_comm")
    transition = relation_compiler_module.build_certificate_transition_specs(
        SimpleNamespace(), certificates
    )[0]
    assert transition.authority_requirements == (
        relation_compiler_module.TransitionAuthorityRequirement(
            "tensor_eq", ("sm", "pm"), (99, 99)
        ),
        relation_compiler_module.TransitionAuthorityRequirement(
            "tensor_shape", ("pm",), (99,), (6, 4)
        ),
    )

    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=tuple(steps)),
        ((sm_output, *pm_outputs),),
        ("sharded",),
        rules=("linear_k",),
        certificate_sink=sink,
    )
    assert normalized == ((sm_input, *pm_inputs),)
    assert normalized_layouts == ("sharded",)
    assert sink == list(certificates)


def test_external_initial_state_renders_k_rank_init_sharded_fact():
    lineage = SimpleNamespace(
        ts=1603, tsShape=[100, 16],
        tps=[(0, 3057), (1, 3058), (2, 3059), (3, 3060)],
        tpShapes=[[100, 4], [100, 4], [100, 4], [100, 4]],
        gatherDim=1, replicated=False,
    )
    ir = SimpleNamespace(
        init_goals_ref="TrainVerify.Denote.Generated.initGoals",
        sm_graph_ref="TrainVerify.Denote.Generated.gSM",
        pm_graph_ref="TrainVerify.Denote.Generated.gPM",
        packed_cu_contracts=(), tensor_value_bound_contracts=(),
        sm_input_value_classes=(), pm_input_value_classes=(),
        init_lineages={1603: lineage}, full_init_goal_ids=frozenset({1603}),
    )
    spec = relation_compiler_module.init_lineage_relation_fact(lineage)
    record = relation_compiler_module.ClosedRelationFactRecord(
        fact_id="fact_000001", source=spec, kind="sharded", sm_tid=1603,
        pm_tids=(3057, 3058, 3059, 3060), metadata_tid=None,
        metadata_region_id=None, full_shape=tuple(lineage.tsShape),
        shard_shape=tuple(lineage.tpShapes[0]), gather_dim=1,
    )
    anchor = relation_compiler_module.ClosedTensorShapeFactRecord(
        fact_id="anchor_sm_shape_1603", side="sm", tid=1603,
        shape=tuple(lineage.tsShape), init_goal_id=1603,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(record,), authority_facts=(), anchor_fact=anchor,
        states=(
            SimpleNamespace(state_id="state_000000", fact_ids=(anchor.fact_id, record.fact_id)),
            SimpleNamespace(state_id="state_000001", fact_ids=(anchor.fact_id,)),
        ),
        segments=(SimpleNamespace(pre_state_id="state_000000"),),
    )
    source = composer_module.render_closed_external_initial_state(
        ir, SimpleNamespace(dependent_chain_plan=chain), "GPTKInit"
    )
    assert "ShardedRel.of_init_goal" in source
    assert "Generated.initGoal_1603" in source
    assert "[3057, 3058, 3059, 3060]" in source
    assert "hPM 3057" in source and "hPM 3060" in source


def test_k_rank_hidden_sharded_embedding_uses_ordered_init_weight_authority():
    sm = SimpleNamespace(
        step_id="sm:1:0", side="sm", op="FW_embedding", rank=0,
        input_bindings=("init:40", "init:50"),
        input_shapes=((1, 8), (100, 16)), parameters=(), output_shape=(1, 8, 16),
    )
    pm = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank}:0", side="pm", op="FW_embedding", rank=rank,
            input_bindings=("init:40", f"init:{60 + rank}"),
            input_shapes=((1, 8), (100, 4)), parameters=(), output_shape=(1, 8, 4),
        )
        for rank in range(4)
    )
    lineage = SimpleNamespace(
        ts=50, tsShape=[100, 16], tps=[(rank, 60 + rank) for rank in range(4)],
        tpShapes=[[100, 4] for _ in range(4)], gatherDim=1, replicated=False,
    )
    frontier = (sm.step_id, *(step.step_id for step in pm))
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_hidden_sharded_embedding(
        SimpleNamespace(steps=(sm, *pm)), SimpleNamespace(init_lineages={50: lineage}),
        (frontier,), ("sharded",),
    )
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rank_count == 4
    assert cert.ids_tid == 40
    assert cert.weight_fact == RelationFactSpec(
        "sharded", ("init:50", "init:60", "init:61", "init:62", "init:63"),
        gather_dim=1,
    )
    assert cert.output_fact == RelationFactSpec("sharded", frontier, gather_dim=2)
    assert frontiers == (cert.weight_fact.step_triple,)
    assert layouts == ("sharded",)
    assert cert.lean_theorem.endswith("fw_embedding_hidden_shards_k_rank")
    transitions = relation_compiler_module.build_certificate_transition_specs(
        SimpleNamespace(), certs
    )
    assert transitions[0].pre_facts == (cert.weight_fact,)
    assert transitions[0].post_facts == (cert.output_fact,)
    assert transitions[0].authority_requirements == (
        relation_compiler_module.TransitionAuthorityRequirement(
            "tensor_eq", ("sm", "pm"), (40, 40)
        ),
        relation_compiler_module.TransitionAuthorityRequirement(
            "tensor_shape", ("pm",), (40,), shape=(1, 8)
        ),
    )
    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=(sm, *pm)), (frontier,), ("sharded",),
        rules=("embedding_k",),
        goal_ir=SimpleNamespace(init_lineages={50: lineage}),
        certificate_sink=sink,
    )
    assert (normalized, normalized_layouts, sink) == (
        (cert.weight_fact.step_triple,), ("sharded",), [cert]
    )


def test_k_rank_hidden_sharded_embedding_supports_vector_ids_rank2_outputs():
    sm = SimpleNamespace(
        step_id="sm:1:0", side="sm", op="FW_embedding", rank=0,
        input_bindings=("init:40", "init:50"),
        input_shapes=((4096,), (100, 16)), parameters=(), output_shape=(4096, 16),
    )
    pm = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank}:0", side="pm", op="FW_embedding", rank=rank,
            input_bindings=("init:40", f"init:{60 + rank}"),
            input_shapes=((4096,), (100, 8)), parameters=(), output_shape=(4096, 8),
        )
        for rank in range(2)
    )
    lineage = SimpleNamespace(
        ts=50, tsShape=[100, 16], tps=[(rank, 60 + rank) for rank in range(2)],
        tpShapes=[[100, 8] for _ in range(2)], gatherDim=1, replicated=False,
    )
    frontier = (sm.step_id, *(step.step_id for step in pm))
    certs, _, _ = relation_compiler_module.advance_k_rank_hidden_sharded_embedding(
        SimpleNamespace(steps=(sm, *pm)), SimpleNamespace(init_lineages={50: lineage}),
        (frontier,), ("sharded",),
    )
    assert len(certs) == 1
    assert certs[0].output_fact == RelationFactSpec("sharded", frontier, gather_dim=1)
    assert certs[0].lean_theorem == "TrainVerify.Denote.fw_embedding_hidden_shards_two"


def test_k_rank_hidden_sharded_embedding_rejects_distinct_ids_authority():
    sm = SimpleNamespace(step_id="sm:1:0", side="sm", op="FW_embedding", rank=0,
                         input_bindings=("init:40", "init:50"), output_shape=(1, 8, 16))
    pm = tuple(
        SimpleNamespace(step_id=f"pm:{rank}:0", side="pm", op="FW_embedding", rank=rank,
                        input_bindings=(f"init:{41 + rank}", f"init:{60 + rank}"),
                        output_shape=(1, 8, 4)) for rank in range(4)
    )
    lineage = SimpleNamespace(
        ts=50, tsShape=[100, 16], tps=[(rank, 60 + rank) for rank in range(4)],
        tpShapes=[[100, 4] for _ in range(4)], gatherDim=1, replicated=False,
    )
    frontier = (sm.step_id, *(step.step_id for step in pm))
    with pytest.raises(RelationCompositionError, match="ids authority"):
        relation_compiler_module.advance_k_rank_hidden_sharded_embedding(
            SimpleNamespace(steps=(sm, *pm)), SimpleNamespace(init_lineages={50: lineage}),
            (frontier,), ("sharded",),
        )


@pytest.mark.parametrize("rank_count", (3, 4))
def test_k_rank_vocab_sharded_embedding_decomposes_reduction_to_external_weights(rank_count):
    shard_rows, hidden = 7, 12
    ids_shape = (1, 8)
    output_shape = (*ids_shape, hidden)
    sm = SimpleNamespace(
        step_id="sm:1:0", side="sm", op="FW_embedding", rank=0,
        input_bindings=("init:40", "init:50"),
        input_shapes=(ids_shape, (rank_count * shard_rows, hidden)), parameters=(),
        output_shape=output_shape,
    )
    pm = tuple(SimpleNamespace(
        step_id=f"pm:{rank}:0", side="pm", op="FW_embedding", rank=rank,
        input_bindings=("init:40", f"init:{60 + rank}"),
        input_shapes=(ids_shape, (shard_rows, hidden)),
        parameters=(rank * shard_rows,), output_shape=output_shape,
    ) for rank in range(rank_count))
    lineage = SimpleNamespace(
        ts=50, tsShape=[rank_count * shard_rows, hidden],
        tps=[(rank, 60 + rank) for rank in range(rank_count)],
        tpShapes=[[shard_rows, hidden] for _ in range(rank_count)],
        gatherDim=0, replicated=False,
    )
    frontier = (sm.step_id, *(step.step_id for step in pm))
    reduction = RelationFactSpec("reduction", frontier)
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_vocab_sharded_embedding_producer(
        SimpleNamespace(steps=(sm, *pm)), SimpleNamespace(init_lineages={50: lineage}),
        (frontier,), ("reduction",),
    )
    assert len(certs) == 1
    cert = certs[0]
    assert (cert.rank_count, cert.ids_tid, cert.shard_rows, cert.hidden_size) == (rank_count, 40, shard_rows, hidden)
    assert cert.weight_fact == RelationFactSpec(
        "sharded", ("init:50", *(f"init:{60 + rank}" for rank in range(rank_count))), gather_dim=0,
    )
    assert cert.output_fact == reduction
    assert (frontiers, layouts) == ((cert.weight_fact.step_triple,), ("sharded",))
    assert cert.lean_theorem.endswith("fw_embedding_eq_allReduce_offset_shards")
    transition = build_certificate_transition_specs(SimpleNamespace(), certs)[0]
    assert (transition.pre_facts, transition.post_facts) == ((cert.weight_fact,), (reduction,))
    assert transition.authority_requirements == (
        relation_compiler_module.TransitionAuthorityRequirement("tensor_eq", ("sm", "pm"), (40, 40)),
        relation_compiler_module.TransitionAuthorityRequirement("tensor_shape", ("pm",), (40,), (1, 8)),
    )
    sink = []
    normalized = normalize_relation_frontiers(
        SimpleNamespace(steps=(sm, *pm)), (frontier,), ("reduction",),
        rules=("embedding_vocab_reduction_k",), goal_ir=SimpleNamespace(init_lineages={50: lineage}),
        certificate_sink=sink,
    )
    assert (*normalized, sink) == ((cert.weight_fact.step_triple,), ("sharded",), [cert])


@pytest.mark.parametrize(("mutation", "message"), (
    ("plain_pm", "offset semantics"), ("wrong_offset", "offset semantics"),
    ("wrong_weight_order", "weight authority order"), ("wrong_weight_shape", "vocab/hidden shape"),
    ("different_ids", "ids authority"),
))
def test_k_rank_vocab_sharded_embedding_rejects_unchecked_authority(mutation, message):
    rank_count, shard_rows, hidden = 4, 7, 12
    ids_shape = (1, 8)
    sm = SimpleNamespace(
        step_id="sm:1:0", side="sm", op="FW_embedding", rank=0,
        input_bindings=("init:40", "init:50"), input_shapes=(ids_shape, (28, hidden)),
        parameters=(), output_shape=(*ids_shape, hidden),
    )
    pm = [SimpleNamespace(
        step_id=f"pm:{rank}:0", side="pm", op="FW_embedding", rank=rank,
        input_bindings=("init:40", f"init:{60 + rank}"), input_shapes=(ids_shape, (shard_rows, hidden)),
        parameters=(rank * shard_rows,), output_shape=(*ids_shape, hidden),
    ) for rank in range(rank_count)]
    lineage = SimpleNamespace(
        ts=50, tsShape=[28, hidden], tps=[(rank, 60 + rank) for rank in range(rank_count)],
        tpShapes=[[shard_rows, hidden] for _ in range(rank_count)], gatherDim=0, replicated=False,
    )
    if mutation == "plain_pm": pm[1] = SimpleNamespace(**{**pm[1].__dict__, "parameters": ()})
    elif mutation == "wrong_offset": pm[2] = SimpleNamespace(**{**pm[2].__dict__, "parameters": (99,)})
    elif mutation == "wrong_weight_order": lineage.tps[1], lineage.tps[2] = lineage.tps[2], lineage.tps[1]
    elif mutation == "wrong_weight_shape": lineage.tpShapes[3] = [shard_rows + 1, hidden]
    elif mutation == "different_ids":
        pm[3] = SimpleNamespace(**{**pm[3].__dict__, "input_bindings": ("init:41", pm[3].input_bindings[1])})
    frontier = (sm.step_id, *(step.step_id for step in pm))
    with pytest.raises(RelationCompositionError, match=message):
        relation_compiler_module.advance_k_rank_vocab_sharded_embedding_producer(
            SimpleNamespace(steps=(sm, *pm)), SimpleNamespace(init_lineages={50: lineage}),
            (frontier,), ("reduction",),
        )


def test_k_rank_full_producer_chunks_reconstruct_arbitrary_ordered_k():
    sm = SimpleNamespace(step_id="sm:1:0", side="sm", op="FW_view", rank=0,
                         input_bindings=(), parameters=(1, 8, 12), output_shape=(1, 8, 12))
    producer = SimpleNamespace(step_id="pm:0:0", side="pm", op="FW_view", rank=0,
                               input_bindings=(), parameters=(1, 8, 12), output_shape=(1, 8, 12))
    chunks = tuple(
        SimpleNamespace(step_id=f"pm:{rank + 1}:0", side="pm", op="ChunkPrim", rank=rank,
                        input_bindings=(producer.step_id,), parameters=(1,), output_shape=(1, 2, 12))
        for rank in range(4)
    )
    frontier = (sm.step_id, *(step.step_id for step in chunks))
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_full_producer_chunks(
        SimpleNamespace(steps=(sm, producer, *chunks)), (frontier,), ("sharded",)
    )
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rank_count == 4
    assert cert.chunk_dim == 1
    assert cert.input_fact == RelationFactSpec(
        "joined", (sm.step_id,), joined_pm_step=producer.step_id
    )
    assert cert.output_fact == RelationFactSpec("sharded", frontier, gather_dim=1)
    assert cert.pm_chunk_steps == tuple(step.step_id for step in chunks)
    assert cert.lean_theorem.endswith("allGatherPrimDimN_chunks_ofFn")
    assert frontiers == ((sm.step_id, producer.step_id),)
    assert layouts == ("joined",)
    transition = relation_compiler_module.build_certificate_transition_specs(
        SimpleNamespace(), certs
    )[0]
    assert transition.pre_facts == (cert.input_fact,)
    assert transition.post_facts == (cert.output_fact,)
    # The joined pre-fact owns the producer equality; this transition owns only chunks.
    assert transition.sm_node_indices == ()
    assert transition.pm_node_indices == (1, 2, 3, 4)
    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=(sm, producer, *chunks)), (frontier,), ("sharded",),
        rules=("full_producer_k",), certificate_sink=sink,
    )
    assert (normalized, normalized_layouts, sink) == (
        ((sm.step_id, producer.step_id),), ("joined",), [cert]
    )


def test_k_rank_full_producer_chunks_rejects_duplicate_or_reordered_ranks():
    sm = SimpleNamespace(step_id="sm:1:0", side="sm", op="FW_view", rank=0,
                         input_bindings=(), parameters=(), output_shape=(1, 8, 12))
    producer = SimpleNamespace(step_id="pm:0:0", side="pm", op="FW_view", rank=0,
                               input_bindings=(), parameters=(), output_shape=(1, 8, 12))
    chunks = tuple(
        SimpleNamespace(step_id=f"pm:{rank + 1}:0", side="pm", op="ChunkPrim",
                        rank=(0 if rank == 1 else rank), input_bindings=(producer.step_id,),
                        parameters=(1,), output_shape=(1, 2, 12)) for rank in range(4)
    )
    frontier = (sm.step_id, *(step.step_id for step in chunks))
    with pytest.raises(RelationCompositionError, match="ordered ranks"):
        relation_compiler_module.advance_k_rank_full_producer_chunks(
            SimpleNamespace(steps=(sm, producer, *chunks)), (frontier,), ("sharded",)
        )


def test_k_rank_output_sharded_linear_uses_joined_activation_and_init_weight_authority():
    sm_activation = SimpleNamespace(step_id="sm:0:0", side="sm", op="FW_gelu", rank=0,
                                    input_bindings=(), output_shape=(1, 8, 12))
    pm_activation = SimpleNamespace(step_id="pm:0:0", side="pm", op="AllGatherPrim", rank=0,
                                    input_bindings=(), output_shape=(1, 8, 12))
    sm_out = SimpleNamespace(step_id="sm:1:0", side="sm", op="FW_linear", rank=0,
                             input_bindings=(sm_activation.step_id, "init:50"),
                             output_shape=(1, 8, 16))
    pm_out = tuple(
        SimpleNamespace(step_id=f"pm:{rank + 1}:0", side="pm", op="FW_linear", rank=rank,
                        input_bindings=(pm_activation.step_id, f"init:{60 + rank}"),
                        input_shapes=((1, 8, 12), (4, 12)),
                        output_shape=(1, 8, 4))
        for rank in range(4)
    )
    lineage = SimpleNamespace(
        ts=50, tsShape=[16, 12],
        tps=[(rank, 60 + rank) for rank in range(4)],
        tpShapes=[[4, 12] for _ in range(4)], gatherDim=0, replicated=False,
    )
    frontier = (sm_out.step_id, *(step.step_id for step in pm_out))
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_output_sharded_linear_frontiers(
        SimpleNamespace(steps=(sm_activation, pm_activation, sm_out, *pm_out)),
        SimpleNamespace(init_lineages={50: lineage}),
        (frontier,), ("sharded",),
    )
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rank_count == 4
    assert cert.activation_fact == RelationFactSpec(
        "joined", (sm_activation.step_id,), joined_pm_step=pm_activation.step_id
    )
    assert cert.weight_fact == RelationFactSpec(
        "sharded", ("init:50", "init:60", "init:61", "init:62", "init:63"),
        gather_dim=0,
    )
    assert cert.output_fact == RelationFactSpec("sharded", frontier, gather_dim=2)
    assert cert.activation_shape == (1, 8, 12)
    assert cert.weight_full_shape == (16, 12)
    assert cert.weight_shard_shape == (4, 12)
    assert cert.output_full_shape == (1, 8, 16)
    assert cert.output_shard_shape == (1, 8, 4)
    assert frontiers == (
        (sm_activation.step_id, pm_activation.step_id), cert.weight_fact.step_triple,
    )
    assert layouts == ("joined", "sharded")
    assert cert.lean_theorem.endswith("fw_linear_3d_weight_allGatherPrimDimN_dim0_comm")
    transition = relation_compiler_module.build_certificate_transition_specs(
        SimpleNamespace(), certs
    )[0]
    assert transition.pre_facts == (cert.activation_fact, cert.weight_fact)
    assert transition.post_facts == (cert.output_fact,)
    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=(sm_activation, pm_activation, sm_out, *pm_out)),
        (frontier,), ("sharded",), rules=("output_linear_k",),
        goal_ir=SimpleNamespace(init_lineages={50: lineage}), certificate_sink=sink,
    )
    assert (normalized, normalized_layouts, sink) == (
        ((sm_activation.step_id, pm_activation.step_id), cert.weight_fact.step_triple),
        ("joined", "sharded"), [cert]
    )


def test_k_rank_output_sharded_linear_rejects_weight_authority_order_mismatch():
    sm_activation = SimpleNamespace(step_id="sm:0:0", side="sm", op="FW_gelu", rank=0,
                                    input_bindings=(), output_shape=(1, 8, 12))
    pm_activation = SimpleNamespace(step_id="pm:0:0", side="pm", op="AllGatherPrim", rank=0,
                                    input_bindings=(), output_shape=(1, 8, 12))
    sm_out = SimpleNamespace(step_id="sm:1:0", side="sm", op="FW_linear", rank=0,
                             input_bindings=(sm_activation.step_id, "init:50"),
                             output_shape=(1, 8, 16))
    pm_out = tuple(
        SimpleNamespace(step_id=f"pm:{rank + 1}:0", side="pm", op="FW_linear", rank=rank,
                        input_bindings=(pm_activation.step_id, f"init:{63 - rank}"),
                        output_shape=(1, 8, 4)) for rank in range(4)
    )
    lineage = SimpleNamespace(
        ts=50, tsShape=[16, 12], tps=[(rank, 60 + rank) for rank in range(4)],
        tpShapes=[[4, 12] for _ in range(4)], gatherDim=0, replicated=False,
    )
    frontier = (sm_out.step_id, *(step.step_id for step in pm_out))
    with pytest.raises(RelationCompositionError, match="weight authority"):
        relation_compiler_module.advance_k_rank_output_sharded_linear_frontiers(
            SimpleNamespace(steps=(sm_activation, pm_activation, sm_out, *pm_out)),
            SimpleNamespace(init_lineages={50: lineage}), (frontier,), ("sharded",),
        )


def test_k_rank_local_linear_skips_dynamic_weight_variant_without_error():
    sm_out = SimpleNamespace(step_id="sm:2:0", side="sm", op="FW_linear", rank=0,
                             input_bindings=("sm:0:0", "sm:1:0"), output_shape=(1, 8, 6))
    pm_out = tuple(
        SimpleNamespace(step_id=f"pm:{rank + 8}:0", side="pm", op="FW_linear", rank=rank,
                        input_bindings=(f"pm:{rank}:0", f"pm:{rank + 4}:0"),
                        output_shape=(1, 2, 6))
        for rank in range(4)
    )
    producers = (
        SimpleNamespace(step_id="sm:0:0", side="sm", rank=0, output_shape=(1, 8, 4)),
        SimpleNamespace(step_id="sm:1:0", side="sm", rank=0, output_shape=(6, 4)),
        *(SimpleNamespace(step_id=f"pm:{rank}:0", side="pm", rank=rank,
                          output_shape=(1, 2, 4)) for rank in range(4)),
        *(SimpleNamespace(step_id=f"pm:{rank + 4}:0", side="pm", rank=rank,
                          output_shape=(2, 4)) for rank in range(4)),
    )
    frontier = (sm_out.step_id, *(step.step_id for step in pm_out))
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_linear_relation_frontiers(
        SimpleNamespace(steps=(*producers, sm_out, *pm_out)), (frontier,), ("sharded",)
    )
    assert certs == ()
    assert frontiers == (frontier,)
    assert layouts == ("sharded",)

    sm_out.input_bindings = ("sm:0:0", "init:91")
    for rank, step in enumerate(pm_out):
        step.input_bindings = (f"pm:{rank}:0", f"init:{92 + rank}")
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_linear_relation_frontiers(
        SimpleNamespace(steps=(*producers, sm_out, *pm_out)), (frontier,), ("sharded",)
    )
    assert certs == ()
    assert frontiers == (frontier,)
    assert layouts == ("sharded",)


def test_k_rank_gelu_uses_generic_pointwise_theorem_for_dim2():
    sm_in = SimpleNamespace(step_id="sm:0:0", side="sm", op="FW_identity", rank=0,
                            input_bindings=(), output_shape=(1, 8, 12))
    pm_in = tuple(SimpleNamespace(step_id=f"pm:{rank}:0", side="pm", op="FW_identity",
                                  rank=rank, input_bindings=(), output_shape=(1, 8, 3))
                  for rank in range(4))
    sm_out = SimpleNamespace(step_id="sm:1:0", side="sm", op="FW_gelu", rank=0,
                             input_bindings=(sm_in.step_id,),
                             input_shapes=((1, 8, 12),), output_shape=(1, 8, 12))
    pm_out = tuple(SimpleNamespace(step_id=f"pm:{rank + 4}:0", side="pm", op="FW_gelu",
                                   rank=rank, input_bindings=(pm_in[rank].step_id,),
                                   input_shapes=((1, 8, 3),),
                                   output_shape=(1, 8, 3)) for rank in range(4))
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_gelu_relation_frontiers(
        SimpleNamespace(steps=(sm_in, *pm_in, sm_out, *pm_out)),
        ((sm_out.step_id, *(step.step_id for step in pm_out)),), ("sharded",)
    )
    assert frontiers == ((sm_in.step_id, *(step.step_id for step in pm_in)),)
    assert layouts == ("sharded",)
    assert len(certs) == 1
    assert certs[0].gather_dim == 2
    assert certs[0].external_tids == ()
    assert certs[0].lean_theorem.endswith("fw_gelu_allGatherPrimDimN_eq")

    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=(sm_in, *pm_in, sm_out, *pm_out)),
        ((sm_out.step_id, *(step.step_id for step in pm_out)),),
        ("sharded",), rules=("gelu_k",), certificate_sink=sink,
    )
    assert normalized == frontiers
    assert normalized_layouts == layouts
    assert sink == list(certs)


def test_k_rank_layernorm_frontier_uses_generic_local_backend():
    sm_in = SimpleNamespace(step_id="sm:0:0", side="sm", op="FW_add", rank=0,
                            input_bindings=(), output_shape=(1, 8, 6))
    pm_in = tuple(
        SimpleNamespace(step_id=f"pm:{rank}:0", side="pm", op="FW_add", rank=rank,
                        input_bindings=(), output_shape=(1, 2, 6))
        for rank in range(4)
    )
    sm_out = SimpleNamespace(
        step_id="sm:1:0", side="sm", op="FW_layernorm", rank=0,
        input_bindings=(sm_in.step_id, "init:91", "init:92"),
        input_shapes=((1, 8, 6), (6,), (6,)), output_shape=(1, 8, 6)
    )
    pm_out = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank + 4}:0", side="pm", op="FW_layernorm", rank=rank,
            input_bindings=(pm_in[rank].step_id, "init:91", "init:92"),
            input_shapes=((1, 2, 6), (6,), (6,)), output_shape=(1, 2, 6),
        )
        for rank in range(4)
    )
    certs, frontiers, layouts = (
        relation_compiler_module.advance_k_rank_layernorm_relation_frontiers(
            SimpleNamespace(steps=(sm_in, *pm_in, sm_out, *pm_out)),
            ((sm_out.step_id, *(step.step_id for step in pm_out)),),
            ("sharded",),
        )
    )
    assert frontiers == ((sm_in.step_id, *(step.step_id for step in pm_in)),)
    assert layouts == ("sharded",)
    assert len(certs) == 1
    assert certs[0].external_tids == (91, 92)
    assert certs[0].op == "FW_layernorm"
    assert certs[0].lean_theorem.endswith("fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d")


def test_k_rank_multiref_projection_preserves_ordered_sharded_frontier():
    sm_input = "sm:0:0"
    pm_inputs = tuple(f"pm:{rank}:0" for rank in range(4))
    sm_output = "sm:1:1"
    pm_outputs = tuple(f"pm:{rank + 4}:1" for rank in range(4))
    steps = [
        SimpleNamespace(step_id=sm_input, side="sm", op="FW_identity", rank=0,
                        input_bindings=(), output_shape=(1, 8, 6),
                        parameters=(), output_index=0),
        *(SimpleNamespace(step_id=ref, side="pm", op="FW_identity", rank=rank,
                          input_bindings=(), output_shape=(1, 2, 6),
                          parameters=(), output_index=0)
          for rank, ref in enumerate(pm_inputs)),
        SimpleNamespace(step_id=sm_output, side="sm", op="FW_multiref", rank=0,
                        input_bindings=(sm_input,), output_shape=(1, 8, 6),
                        parameters=(2,), output_index=1),
        *(SimpleNamespace(step_id=ref, side="pm", op="FW_multiref", rank=rank,
                          input_bindings=(pm_inputs[rank],), output_shape=(1, 2, 6),
                          parameters=(2,), output_index=1)
          for rank, ref in enumerate(pm_outputs)),
    ]
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_multiref_relation_frontiers(
        SimpleNamespace(steps=tuple(steps)),
        ((sm_output, *pm_outputs),),
        ("sharded",),
    )
    assert frontiers == ((sm_input, *pm_inputs),)
    assert layouts == ("sharded",)
    assert len(certs) == 1
    assert certs[0].rank_count == 4
    assert certs[0].projection == 1
    assert certs[0].arity == 2
    assert certs[0].input_fact.gather_dim == 1
    assert certs[0].output_fact.gather_dim == 1
    assert certs[0].lean_theorem.endswith("applyNode_fw_multiref_at")

    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=tuple(steps)),
        ((sm_output, *pm_outputs),),
        ("sharded",),
        rules=("multiref_k",),
        certificate_sink=sink,
    )
    assert normalized == frontiers
    assert normalized_layouts == layouts
    assert sink == list(certs)


@pytest.mark.parametrize(
    ("shard_shape", "expected_dim"),
    [((1, 2, 12), 1), ((1, 8, 3), 2)],
)
def test_k_rank_add_frontier_expands_two_dynamic_sharded_inputs(shard_shape, expected_dim):
    sm_inputs = ("sm:0:0", "sm:1:0")
    pm_inputs = tuple(
        tuple(f"pm:{arg * 4 + rank}:0" for rank in range(4))
        for arg in range(2)
    )
    sm_output = "sm:2:0"
    pm_outputs = tuple(f"pm:{rank + 8}:0" for rank in range(4))
    steps = [
        *(SimpleNamespace(step_id=ref, side="sm", op="FW_identity", rank=0,
                          input_bindings=(), output_shape=(1, 8, 12))
          for ref in sm_inputs),
        *(SimpleNamespace(step_id=pm_inputs[arg][rank], side="pm", op="FW_identity",
                          rank=rank, input_bindings=(), output_shape=shard_shape)
          for arg in range(2) for rank in range(4)),
        SimpleNamespace(step_id=sm_output, side="sm", op="FW_add", rank=0,
                        input_bindings=sm_inputs, output_shape=(1, 8, 12)),
        *(SimpleNamespace(step_id=pm_outputs[rank], side="pm", op="FW_add", rank=rank,
                          input_bindings=(pm_inputs[0][rank], pm_inputs[1][rank]),
                          output_shape=shard_shape)
          for rank in range(4)),
    ]
    certs, frontiers, layouts = relation_compiler_module.advance_k_rank_add_relation_frontiers(
        SimpleNamespace(steps=tuple(steps)),
        ((sm_output, *pm_outputs),),
        ("sharded",),
    )
    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=tuple(steps)),
        ((sm_output, *pm_outputs),),
        ("sharded",),
        rules=("add_k",),
        certificate_sink=sink,
    )
    expected = (
        (sm_inputs[0], *pm_inputs[0]),
        (sm_inputs[1], *pm_inputs[1]),
    )
    assert len(certs) == 1
    assert certs[0].gather_dim == expected_dim
    assert certs[0].lean_theorem == "TrainVerify.Denote.fw_add_allGather_dim_K"
    assert frontiers == expected
    assert layouts == ("sharded", "sharded")
    assert normalized == expected
    assert normalized_layouts == ("sharded", "sharded")
    assert sink == list(certs)


def test_k_rank_alltoall_frontier_transports_gather_dimension():
    sm_ref = "sm:0:0"
    input_refs = tuple(f"pm:{rank}:0" for rank in range(4))
    output_refs = tuple(f"pm:{rank + 4}:0" for rank in range(4))
    steps = [
        SimpleNamespace(
            step_id=sm_ref,
            side="sm",
            op="FW_identity",
            rank=0,
            input_bindings=(),
            parameters=(),
            output_shape=(8, 4),
        )
    ]
    steps.extend(
        SimpleNamespace(
            step_id=ref,
            side="pm",
            op="FW_identity",
            rank=rank,
            input_bindings=(),
            parameters=(),
            output_shape=(2, 4),
        )
        for rank, ref in enumerate(input_refs)
    )
    steps.extend(
        SimpleNamespace(
            step_id=ref,
            side="pm",
            op="AllToAllPrim",
            rank=rank,
            input_bindings=input_refs,
            parameters=(0, 1),
            output_shape=(8, 1),
        )
        for rank, ref in enumerate(output_refs)
    )

    certificates, frontiers, layouts = (
        relation_compiler_module.advance_k_rank_alltoall_relation_frontiers(
            SimpleNamespace(steps=tuple(steps)),
            ((sm_ref, *output_refs),),
            ("sharded",),
        )
    )

    assert len(certificates) == 1
    assert certificates[0].rank_count == 4
    assert certificates[0].input_gather_dim == 0
    assert certificates[0].output_gather_dim == 1
    assert certificates[0].lean_theorem == "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    assert certificates[0].input_fact == RelationFactSpec(
        "sharded", (sm_ref, *input_refs), gather_dim=0
    )
    assert certificates[0].output_fact == RelationFactSpec(
        "sharded", (sm_ref, *output_refs), gather_dim=1
    )
    assert frontiers == ((sm_ref, *input_refs),)
    assert layouts == ("sharded",)

    transitions = build_certificate_transition_specs(
        SimpleNamespace(steps=tuple(steps)), certificates
    )
    assert len(transitions) == 1
    assert transitions[0].pre_facts == (certificates[0].input_fact,)
    assert transitions[0].post_facts == (certificates[0].output_fact,)
    assert transitions[0].sm_node_indices == ()
    assert transitions[0].pm_node_indices == (4, 5, 6, 7)

    sink = []
    normalized, normalized_layouts = normalize_relation_frontiers(
        SimpleNamespace(steps=tuple(steps)),
        ((sm_ref, *output_refs),),
        ("sharded",),
        rules=("alltoall_k",),
        certificate_sink=sink,
    )
    assert normalized == ((sm_ref, *input_refs),)
    assert normalized_layouts == ("sharded",)
    assert sink == list(certificates)


def _synthetic_k_rank_segment_relation(*, family: str, rank_count: int = 4, framed: bool = False):
    assert rank_count > 0
    anchor = relation_compiler_module.ClosedTensorShapeFactRecord(
        fact_id="anchor", side="sm", tid=999, shape=(1,), init_goal_id=999,
    )
    if family == "chunks":
        pre_spec = RelationFactSpec("joined", ("sm:0:0",), joined_pm_step="pm:0:0")
        post_spec = RelationFactSpec(
            "sharded", ("sm:0:0", *(f"pm:{rank + 1}:0" for rank in range(rank_count))),
            gather_dim=1,
        )
        pre = relation_compiler_module.ClosedRelationFactRecord(
            "fact_pre", pre_spec, "joined", 10, (), None, None,
            (2, 2 * rank_count), (2, 2 * rank_count), joined_pm_tid=20,
        )
        post = relation_compiler_module.ClosedRelationFactRecord(
            "fact_post", post_spec, "sharded", 10,
            tuple(30 + rank for rank in range(rank_count)), None, None,
            (2, 2 * rank_count), (2, 2), gather_dim=1,
        )
        certificate = relation_compiler_module.KRankFullProducerChunksCertificate(
            rule_id="full-producer-chunks-k-rank", rank_count=rank_count, chunk_dim=1,
            input_fact=pre_spec, output_fact=post_spec, sm_step_id="sm:0:0",
            pm_producer_step="pm:0:0",
            pm_chunk_steps=tuple(f"pm:{rank + 1}:0" for rank in range(rank_count)),
            lean_theorem="TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",
        )
        transition = _bind_certificate_digest(
            relation_compiler_module.CertificateTransitionSpec(
                "transition", certificate.rule_id, (pre_spec,), (post_spec,), (),
                tuple(range(1, rank_count + 1)), certificate.lean_theorem,
            ),
            certificate,
        )
        sm_nodes = [Node(0, "FW_identity", [1], [10], [])]
        pm_nodes = [
            Node(0, "FW_identity", [2], [20], []),
            *(Node(rank, "ChunkPrim", [20], [30 + rank], [1])
              for rank in range(rank_count)),
        ]
        sm_range, pm_range = (1, 1), (1, rank_count + 1)
    elif family == "sum":
        sm_writer_index = 2 if framed else 1
        pm_writer_indices = (
            tuple(rank_count + 2 * rank for rank in range(rank_count))
            if framed else tuple(rank + rank_count for rank in range(rank_count))
        )
        pre_spec = RelationFactSpec(
            "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(rank_count))),
            gather_dim=1,
        )
        post_spec = RelationFactSpec(
            "reduction", (f"sm:{sm_writer_index}:0", *(f"pm:{index}:0" for index in pm_writer_indices)),
        )
        pre = relation_compiler_module.ClosedRelationFactRecord(
            "fact_pre", pre_spec, "sharded", 10,
            tuple(20 + rank for rank in range(rank_count)), None, None,
            (1, 2 * rank_count, 3), (1, 2, 3), gather_dim=1,
        )
        post = relation_compiler_module.ClosedRelationFactRecord(
            "fact_post", post_spec, "reduction", 11,
            tuple(30 + rank for rank in range(rank_count)), None, None,
            (1,), (1,),
        )
        certificate = relation_compiler_module.KRankSumProducerCertificate(
            rule_id="sum-producer-sharded-k-rank-dim1", rank_count=rank_count,
            gather_dim=1, full_shape=(1, 2 * rank_count, 3), shard_shape=(1, 2, 3),
            input_fact=pre_spec, output_fact=post_spec,
            sm_sum_step=f"sm:{sm_writer_index}:0",
            pm_sum_steps=tuple(f"pm:{index}:0" for index in pm_writer_indices),
            lean_theorem="TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum",
        )
        transition = _bind_certificate_digest(
            relation_compiler_module.CertificateTransitionSpec(
                "transition", certificate.rule_id, (pre_spec,), (post_spec,),
                (sm_writer_index,), pm_writer_indices, certificate.lean_theorem,
            ),
            certificate,
        )
        sm_nodes = [Node(0, "FW_identity", [1], [10], [])]
        pm_nodes = [Node(rank, "FW_identity", [2 + rank], [20 + rank], [])
                    for rank in range(rank_count)]
        if framed:
            sm_nodes += [
                Node(0, "FW_identity", [700], [701], []),
                Node(0, "FW_sum", [10], [11], []),
                Node(0, "FW_identity", [702], [703], []),
                Node(0, "FW_identity", [704], [705], []),
            ]
            for rank in range(rank_count):
                pm_nodes.append(Node(rank, "FW_sum", [20 + rank], [30 + rank], []))
                if rank + 1 < rank_count:
                    pm_nodes.append(Node(rank, "FW_identity", [800 + rank], [900 + rank], []))
            sm_range, pm_range = (1, 5), (rank_count, 3 * rank_count - 1)
        else:
            sm_nodes.append(Node(0, "FW_sum", [10], [11], []))
            pm_nodes += [Node(rank, "FW_sum", [20 + rank], [30 + rank], [])
                         for rank in range(rank_count)]
            sm_range, pm_range = (1, 2), (rank_count, 2 * rank_count)
    elif family == "alltoall":
        pre_spec = RelationFactSpec(
            "sharded", ("sm:0:0", *(f"init:{20 + rank}" for rank in range(rank_count))),
            gather_dim=0,
        )
        post_spec = RelationFactSpec(
            "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(rank_count))),
            gather_dim=1,
        )
        pre = relation_compiler_module.ClosedRelationFactRecord(
            "fact_pre", pre_spec, "sharded", 10,
            tuple(20 + rank for rank in range(rank_count)), None, None,
            (2 * rank_count, rank_count), (2, rank_count), gather_dim=0,
        )
        post = relation_compiler_module.ClosedRelationFactRecord(
            "fact_post", post_spec, "sharded", 10,
            tuple(30 + rank for rank in range(rank_count)), None, None,
            (2 * rank_count, rank_count), (2 * rank_count, 1), gather_dim=1,
        )
        certificate = relation_compiler_module.KRankAllToAllRelationCertificate(
            rule_id="alltoall-k-rank-layout-transport", rank_count=rank_count,
            input_gather_dim=0, output_gather_dim=1,
            input_fact=pre_spec, output_fact=post_spec,
            pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(rank_count)),
            lean_theorem="TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn",
        )
        transition = _bind_certificate_digest(
            relation_compiler_module.CertificateTransitionSpec(
                "transition", certificate.rule_id, (pre_spec,), (post_spec,), (),
                tuple(range(rank_count)), certificate.lean_theorem,
            ),
            certificate,
        )
        inputs = [20 + rank for rank in range(rank_count)]
        sm_nodes = []
        pm_nodes = [Node(rank, "AllToAllPrim", inputs, [30 + rank], [0, 1])
                    for rank in range(rank_count)]
        sm_range, pm_range = (0, 0), (0, rank_count)
    else:
        raise AssertionError(family)
    states = (
        relation_compiler_module.ClosedRelationStateRecord("state_pre", ("anchor", "fact_pre")),
        relation_compiler_module.ClosedRelationStateRecord("state_post", ("anchor", "fact_post")),
    )
    segment = relation_compiler_module.ClosedDependentSegmentRecord(
        "segment_000000", "component", "state_pre", "state_post", ("transition",),
        sm_range, pm_range,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(pre, post), authority_facts=(), anchor_fact=anchor,
        states=states, segments=(segment,),
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=(transition,),
        certificates=(certificate,),
    )
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=rank_count,
        sm_graph_ref="SyntheticKRank.smGraph", pm_graph_ref="SyntheticKRank.pmGraph",
    )
    return ir, relation


def _synthetic_k_rank_multiref_relation(component_count, rank_count=4):
    """Closed list-indexed multiref component with shared exact writers."""
    assert component_count in (2, 3)
    sm_index, pm_start = 3, 21
    sm_input = 100
    pm_inputs = tuple(200 + rank for rank in range(rank_count))
    sm_outputs = tuple(110 + projection for projection in range(component_count))
    pm_outputs = tuple(
        tuple(300 + rank * 10 + projection for projection in range(component_count))
        for rank in range(rank_count)
    )
    input_spec = RelationFactSpec(
        "sharded",
        ("sm:2:0", *(f"pm:{17 + rank}:0" for rank in range(rank_count))),
        gather_dim=1,
    )
    input_record = relation_compiler_module.ClosedRelationFactRecord(
        "fact_input", input_spec, "sharded", sm_input, pm_inputs, None, None,
        (1, 2 * rank_count, 3), (1, 2, 3), gather_dim=1,
    )
    output_specs = tuple(
        RelationFactSpec(
            "sharded",
            (f"sm:{sm_index}:{projection}",
             *(f"pm:{pm_start + rank}:{projection}" for rank in range(rank_count))),
            gather_dim=1,
        )
        for projection in range(component_count)
    )
    output_records = tuple(
        relation_compiler_module.ClosedRelationFactRecord(
            f"fact_output_{projection}", spec, "sharded", sm_outputs[projection],
            tuple(outputs[projection] for outputs in pm_outputs), None, None,
            (1, 2 * rank_count, 3), (1, 2, 3), gather_dim=1,
        )
        for projection, spec in enumerate(output_specs)
    )
    certificates = tuple(
        relation_compiler_module.KRankMultirefRelationCertificate(
            rule_id="multiref-sharded-k-rank", rank_count=rank_count, gather_dim=1,
            projection=projection, pm_projections=(projection,) * rank_count,
            arity=component_count,
            input_fact=input_spec, output_fact=output_specs[projection],
            sm_step_id=f"sm:{sm_index}:{projection}",
            pm_step_ids=tuple(
                f"pm:{pm_start + rank}:{projection}" for rank in range(rank_count)
            ),
            lean_theorem="TrainVerify.Denote.applyNode_fw_multiref_at",
        )
        for projection in range(component_count)
    )
    transitions = tuple(
        _bind_certificate_digest(
            relation_compiler_module.CertificateTransitionSpec(
                f"transition_{projection}", certificate.rule_id,
                (input_spec,), (output_specs[projection],), (sm_index,),
                tuple(range(pm_start, pm_start + rank_count)), certificate.lean_theorem,
            ),
            certificate,
        )
        for projection, certificate in enumerate(certificates)
    )
    anchor = relation_compiler_module.ClosedTensorShapeFactRecord(
        "anchor", "sm", 999, (1,), 999,
    )
    states = (
        relation_compiler_module.ClosedRelationStateRecord(
            "state_pre", ("anchor", "fact_input")
        ),
        relation_compiler_module.ClosedRelationStateRecord(
            "state_post", ("anchor", *(record.fact_id for record in output_records))
        ),
    )
    segment = relation_compiler_module.ClosedDependentSegmentRecord(
        "segment_000005" if component_count == 2 else "segment_000007",
        "component", "state_pre", "state_post",
        tuple(transition.transition_id for transition in transitions),
        (sm_index, sm_index + 1), (pm_start, pm_start + rank_count),
    )
    filler_sm = [Node(0, "FW_identity", [400 + i], [500 + i], []) for i in range(sm_index)]
    filler_pm = [Node(i % rank_count, "FW_identity", [600 + i], [700 + i], [])
                 for i in range(pm_start)]
    sm_node = Node(0, "FW_multiref", [sm_input], list(sm_outputs), [component_count])
    pm_nodes = [
        Node(rank, "FW_multiref", [pm_inputs[rank]], list(pm_outputs[rank]),
             [component_count])
        for rank in range(rank_count)
    ]
    chain = SimpleNamespace(
        complete=True, relation_facts=(input_record, *output_records),
        authority_facts=(), anchor_fact=anchor, states=states, segments=(segment,),
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=transitions,
        certificates=certificates,
    )
    ir = SimpleNamespace(
        sm_nodes=[*filler_sm, sm_node], pm_nodes=[*filler_pm, *pm_nodes],
        sm_num_ranks=1, pm_num_ranks=rank_count,
        sm_graph_ref=f"SyntheticMultiref{component_count}.smGraph",
        pm_graph_ref=f"SyntheticMultiref{component_count}.pmGraph",
    )
    return ir, relation


def _synthetic_vocab_embedding_reduction_relation(rank_count=3, *, framed=False):
    shard_rows, hidden = 7, 12
    sm_writer_index = 1 if framed else 0
    pm_writer_indices = tuple(2 * rank for rank in range(rank_count)) if framed else tuple(range(rank_count))
    weight_spec = RelationFactSpec(
        "sharded", ("init:50", *(f"init:{60 + rank}" for rank in range(rank_count))), gather_dim=0,
    )
    reduction_spec = RelationFactSpec(
        "reduction", (f"sm:{sm_writer_index}:0", *(f"pm:{index}:0" for index in pm_writer_indices)),
    )
    weight = relation_compiler_module.ClosedRelationFactRecord(
        "fact_weight", weight_spec, "sharded", 50, tuple(60 + r for r in range(rank_count)),
        None, None, (rank_count * shard_rows, hidden), (shard_rows, hidden), gather_dim=0,
    )
    reduction = relation_compiler_module.ClosedRelationFactRecord(
        "fact_reduction", reduction_spec, "reduction", 100,
        tuple(200 + r for r in range(rank_count)), None, None, (1, 8, hidden), (1, 8, hidden),
    )
    anchor = relation_compiler_module.ClosedTensorShapeFactRecord(
        "anchor", "sm", 999, (1,), 999,
    )
    ids_eq = relation_compiler_module.ClosedTensorEqFactRecord(
        "authority_ids_eq_40", "sm", 40, "pm", 40,
    )
    certificate = relation_compiler_module.KRankVocabShardedEmbeddingProducerCertificate(
        rule_id="embedding-vocab-sharded-reduction-k-rank", rank_count=rank_count,
        ids_tid=40, shard_rows=shard_rows, hidden_size=hidden, ids_shape=(1, 8),
        full_weight_shape=(rank_count * shard_rows, hidden), shard_weight_shape=(shard_rows, hidden),
        weight_fact=weight_spec, output_fact=reduction_spec,
        sm_step_id=f"sm:{sm_writer_index}:0",
        pm_step_ids=tuple(f"pm:{index}:0" for index in pm_writer_indices),
        lean_theorem="TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards",
    )
    transition = _bind_certificate_digest(
        relation_compiler_module.CertificateTransitionSpec(
            "transition", certificate.rule_id, (weight_spec,), (reduction_spec,),
            (sm_writer_index,), pm_writer_indices, certificate.lean_theorem,
            (
                relation_compiler_module.TransitionAuthorityRequirement(
                    "tensor_eq", ("sm", "pm"), (40, 40)),
                relation_compiler_module.TransitionAuthorityRequirement(
                    "tensor_shape", ("pm",), (40,), (1, 8)),
            ),
        ),
        certificate,
    )
    ids_shape = relation_compiler_module.ClosedTensorShapeFactRecord(
        "authority_ids_shape_40", "pm", 40, (1, 8), 40,
    )
    states = (
        relation_compiler_module.ClosedRelationStateRecord(
            "state_pre", ("anchor", "authority_ids_eq_40", "authority_ids_shape_40", "fact_weight")
        ),
        relation_compiler_module.ClosedRelationStateRecord(
            "state_post", ("anchor", "authority_ids_eq_40", "authority_ids_shape_40", "fact_reduction")
        ),
    )
    sm_writer = Node(0, "FW_embedding", [40, 50], [100], [])
    pm_writers = [
        Node(rank, "FW_embedding", [40, 60 + rank], [200 + rank], [rank * shard_rows])
        for rank in range(rank_count)
    ]
    if framed:
        sm_nodes = [Node(0, "FW_identity", [9000], [9001]), sm_writer,
                    Node(0, "FW_identity", [9002], [9003])]
        pm_nodes = []
        for rank, writer in enumerate(pm_writers):
            pm_nodes.append(writer)
            if rank + 1 < rank_count:
                pm_nodes.append(Node(rank, "FW_identity", [9100 + rank], [9200 + rank]))
    else:
        sm_nodes, pm_nodes = [sm_writer], pm_writers
    segment = relation_compiler_module.ClosedDependentSegmentRecord(
        "segment_000000", "component", "state_pre", "state_post", ("transition",),
        (0, len(sm_nodes)), (0, len(pm_nodes)),
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(weight, reduction), authority_facts=(ids_eq, ids_shape),
        anchor_fact=anchor, states=states, segments=(segment,),
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=(transition,), certificates=(certificate,),
    )
    ir = SimpleNamespace(
        sm_nodes=sm_nodes,
        pm_nodes=pm_nodes,
        sm_num_ranks=1, pm_num_ranks=rank_count,
        sm_graph_ref="SyntheticEmbedding.smGraph", pm_graph_ref="SyntheticEmbedding.pmGraph",
    )
    return ir, relation


@pytest.mark.parametrize("component_count", [2, 3])
def test_closed_k_rank_multiref_component_is_generic_atomic_and_exact(component_count):
    ir, relation = _synthetic_k_rank_multiref_relation(component_count)
    segment_id = "segment_000005" if component_count == 2 else "segment_000007"

    source = render_closed_segment(ir, relation, segment_id)

    assert f"private def {segment_id}" in source
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("foldl_faithful_multiref_middle_writer") == component_count * 5
    assert "smNodes := segment_" in source and "pmNodes := segment_" in source
    assert "pmTids : List Tid := [200, 201, 202, 203]" in source
    assert "rankCount = 4" not in source
    assert source.count("have hout_") == component_count
    assert "RelationState.Holds.fold_frame" in source
    assert "sorry" not in source and "False.elim" not in source


def test_closed_k_rank_multiref_component_fails_closed_on_theorem_output_and_rank_tampering():
    ir, relation = _synthetic_k_rank_multiref_relation(3)
    segment_id = "segment_000007"

    bad_transition = replace(
        relation.transition_specs[0], lean_theorem="TrainVerify.Denote.bad_multiref"
    )
    bad = SimpleNamespace(
        **{**relation.__dict__,
           "transition_specs": (bad_transition, *relation.transition_specs[1:])}
    )
    with pytest.raises(ValueError, match="theorem identity"):
        render_closed_segment(ir, bad, segment_id)

    bad_certificate = replace(
        relation.certificates[1], output_fact=relation.certificates[0].output_fact
    )
    bad = SimpleNamespace(
        **{**relation.__dict__,
           "certificates": (relation.certificates[0], bad_certificate,
                            relation.certificates[2])}
    )
    with pytest.raises(ValueError, match="exact typed certificate"):
        render_closed_segment(ir, bad, segment_id)

    rank_ir = SimpleNamespace(**ir.__dict__)
    rank_ir.pm_nodes = list(ir.pm_nodes)
    target = rank_ir.pm_nodes[22]
    rank_ir.pm_nodes[22] = Node(0, target.op, list(target.ins), list(target.outs),
                                list(target.params))
    with pytest.raises(ValueError, match="ordered ranks"):
        render_closed_segment(rank_ir, relation, segment_id)

    output_ir = SimpleNamespace(**ir.__dict__)
    output_ir.sm_nodes = list(ir.sm_nodes)
    target = output_ir.sm_nodes[3]
    output_ir.sm_nodes[3] = Node(
        target.rank, target.op, list(target.ins), [*target.outs[:-1], 9999],
        list(target.params),
    )
    with pytest.raises(ValueError, match="output authority"):
        render_closed_segment(output_ir, relation, segment_id)


def test_fresh_k_rank_multiref_pair_and_triple_witness_is_renderer_output(tmp_path):
    modules = []
    for component_count in (2, 3):
        ir, relation = _synthetic_k_rank_multiref_relation(component_count)
        namespace = f"SyntheticMultiref{component_count}"
        segment_id = "segment_000005" if component_count == 2 else "segment_000007"
        declarations = render_closed_relation_declarations(
            relation.dependent_chain_plan, namespace
        )
        if modules:
            namespace_line = f"namespace TrainVerify.Denote.{namespace}"
            declaration_lines = declarations.splitlines()
            declarations = "\n".join(
                declaration_lines[declaration_lines.index(namespace_line):]
            )
        rendered = render_closed_segment(ir, relation, segment_id)
        sm_nodes = "[" + ", ".join(
            composer_module._node_text(node) for node in ir.sm_nodes
        ) + "]"
        pm_nodes = "[" + ", ".join(
            composer_module._node_text(node) for node in ir.pm_nodes
        ) + "]"
        modules.append("\n".join((
            declarations,
            f"namespace TrainVerify.Denote.{namespace}",
            "noncomputable section",
            f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
            f"private def pmGraph : GraphDecl := {{ numRanks := 4, nodes := {pm_nodes} }}",
            rendered,
            f"#print axioms {segment_id}",
            "end",
            f"end TrainVerify.Denote.{namespace}",
        )))
    source = "\n\n".join(modules) + "\n"
    witness = tmp_path / "GeneratedKRankMultirefCompilerWitness.lean"
    witness.write_text(source)
    assert witness.read_text() == source
    assert source == "\n\n".join(modules) + "\n"
    assert source.count("import denote.RelationCompiler") == 1
    assert source.count("#print axioms segment_") == 2
# RED fixture: two embedding transitions share one atomic SCC and are interleaved.
def _synthetic_mixed_embedding_relation(rank_count=3):
    hidden_ids, vocab_ids = 40, 41
    hidden_shard, shard_rows, hidden = 4, 7, 12
    hs = RelationFactSpec("sharded", ("init:50", *(f"init:{60+r}" for r in range(rank_count))), gather_dim=1)
    ho = RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{2*r}:0" for r in range(rank_count))), gather_dim=2)
    vs = RelationFactSpec("sharded", ("init:51", *(f"init:{80+r}" for r in range(rank_count))), gather_dim=0)
    vo = RelationFactSpec("reduction", ("sm:1:0", *(f"pm:{2*r+1}:0" for r in range(rank_count))))
    facts = (
        relation_compiler_module.ClosedRelationFactRecord("fact_hidden_weight", hs, "sharded", 50, tuple(60+r for r in range(rank_count)), None, None, (7, rank_count*hidden_shard), (7, hidden_shard), gather_dim=1),
        relation_compiler_module.ClosedRelationFactRecord("fact_vocab_weight", vs, "sharded", 51, tuple(80+r for r in range(rank_count)), None, None, (rank_count*shard_rows, hidden), (shard_rows, hidden), gather_dim=0),
        relation_compiler_module.ClosedRelationFactRecord("fact_hidden_output", ho, "sharded", 100, tuple(200+r for r in range(rank_count)), None, None, (1, 8, rank_count*hidden_shard), (1, 8, hidden_shard), gather_dim=2),
        relation_compiler_module.ClosedRelationFactRecord("fact_reduction", vo, "reduction", 101, tuple(300+r for r in range(rank_count)), None, None, (1, 8, hidden), (1, 8, hidden)),
    )
    anchor = relation_compiler_module.ClosedTensorShapeFactRecord("anchor", "sm", 999, (1,), 999)
    authorities = (
        relation_compiler_module.ClosedTensorEqFactRecord("hidden_eq", "sm", hidden_ids, "pm", hidden_ids),
        relation_compiler_module.ClosedTensorShapeFactRecord("hidden_shape", "pm", hidden_ids, (1, 8), hidden_ids),
        relation_compiler_module.ClosedTensorEqFactRecord("vocab_eq", "sm", vocab_ids, "pm", vocab_ids),
        relation_compiler_module.ClosedTensorShapeFactRecord("vocab_shape", "pm", vocab_ids, (1, 8), vocab_ids),
    )
    hc = relation_compiler_module.KRankHiddenShardedEmbeddingCertificate(
        "embedding-hidden-sharded-k-rank", rank_count, hidden_ids, (1, 8),
        (7, rank_count*hidden_shard), (7, hidden_shard),
        (1, 8, rank_count*hidden_shard), (1, 8, hidden_shard), hs, ho,
        "sm:0:0", tuple(f"pm:{2*r}:0" for r in range(rank_count)),
        "TrainVerify.Denote.fw_embedding_hidden_shards_k_rank")
    vc = relation_compiler_module.KRankVocabShardedEmbeddingProducerCertificate(
        "embedding-vocab-sharded-reduction-k-rank", rank_count, vocab_ids, shard_rows, hidden,
        (1, 8), (rank_count*shard_rows, hidden), (shard_rows, hidden), vs, vo,
        "sm:1:0", tuple(f"pm:{2*r+1}:0" for r in range(rank_count)),
        "TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards")
    req = lambda tid: (
        relation_compiler_module.TransitionAuthorityRequirement("tensor_eq", ("sm", "pm"), (tid, tid)),
        relation_compiler_module.TransitionAuthorityRequirement("tensor_shape", ("pm",), (tid,), (1, 8)))
    ht = _bind_certificate_digest(
        relation_compiler_module.CertificateTransitionSpec(
            "hidden", hc.rule_id, (hs,), (ho,), (0,),
            tuple(2*r for r in range(rank_count)), hc.lean_theorem, req(hidden_ids)
        ),
        hc,
    )
    vt = _bind_certificate_digest(
        relation_compiler_module.CertificateTransitionSpec(
            "vocab", vc.rule_id, (vs,), (vo,), (1,),
            tuple(2*r+1 for r in range(rank_count)), vc.lean_theorem, req(vocab_ids)
        ),
        vc,
    )
    pre_ids = ("anchor", "hidden_eq", "hidden_shape", "vocab_eq", "vocab_shape", "fact_hidden_weight", "fact_vocab_weight")
    states = (relation_compiler_module.ClosedRelationStateRecord("state_pre", pre_ids), relation_compiler_module.ClosedRelationStateRecord("state_post", pre_ids[:-2] + ("fact_hidden_output", "fact_reduction")))
    segment = relation_compiler_module.ClosedDependentSegmentRecord("segment_000000", "component", "state_pre", "state_post", ("hidden", "vocab"), (0, 2), (0, 2*rank_count))
    chain = SimpleNamespace(complete=True, relation_facts=facts, authority_facts=authorities, anchor_fact=anchor, states=states, segments=(segment,))
    relation = SimpleNamespace(dependent_chain_plan=chain, transition_specs=(ht, vt), certificates=(hc, vc))
    sm_nodes = [Node(0, "FW_embedding", [hidden_ids, 50], [100], []), Node(0, "FW_embedding", [vocab_ids, 51], [101], [])]
    pm_nodes = []
    for rank in range(rank_count):
        pm_nodes += [Node(rank, "FW_embedding", [hidden_ids, 60+rank], [200+rank], []), Node(rank, "FW_embedding", [vocab_ids, 80+rank], [300+rank], [rank*shard_rows])]
    ir = SimpleNamespace(sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=rank_count, sm_graph_ref="SyntheticMixedEmbedding.smGraph", pm_graph_ref="SyntheticMixedEmbedding.pmGraph")
    return ir, relation


def test_closed_mixed_embedding_segment_uses_one_exact_ordered_fold_per_axis():
    ir, relation = _synthetic_mixed_embedding_relation(3)
    source = render_closed_segment(ir, relation, "segment_000000")
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert "fw_embedding_hidden_shards_k_rank" in source
    assert "fw_embedding_eq_allReduce_offset_shards" in source
    assert "hiddenPmWeightTids : List Tid := [60, 61, 62]" in source
    assert "vocabPmWeightTids : List Tid := [80, 81, 82]" in source
    assert "let rankCount := hiddenPmWeightTids.length" in source
    assert "rankCount = 3" not in source
    assert source.index('ins := [40, 60]') < source.index('ins := [41, 80]') < source.index('ins := [40, 61]')
    assert "sorry" not in source and "False.elim" not in source


@pytest.mark.parametrize("tamper", ["rank", "role", "certificate", "footprint"])
def test_closed_mixed_embedding_segment_fails_closed_on_authority_tampering(tamper):
    ir, relation = _synthetic_mixed_embedding_relation(3)
    if tamper == "rank": ir.pm_nodes[2].rank = 2
    elif tamper == "role": ir.pm_nodes[0].ins = [41, 60]
    elif tamper == "certificate":
        bad = replace(relation.certificates[0], ids_tid=41)
        relation = SimpleNamespace(**{**relation.__dict__, "certificates": (bad, relation.certificates[1])})
    else:
        bad = replace(relation.transition_specs[0], pm_node_indices=(0, 2))
        relation = SimpleNamespace(**{**relation.__dict__, "transition_specs": (bad, relation.transition_specs[1])})
    with pytest.raises(ValueError, match="mixed K-rank embedding"):
        render_closed_segment(ir, relation, "segment_000000")


def test_closed_vocab_embedding_reduction_segment_is_dynamic_exact_and_offset_aware(tmp_path):
    ir, relation = _synthetic_vocab_embedding_reduction_relation(rank_count=3)
    source = render_closed_segment(ir, relation, "segment_000000")
    assert "fw_embedding_eq_allReduce_offset_shards" in source
    assert "applyNode_fw_embedding_out" in source
    assert source.count("applyNode_fw_embedding_offset_out") == 3
    assert "applyNode_fw_embedding_offset_out SyntheticEmbedding.pmGraph t 1 7 40 61 201" in source
    assert "List.ofFn_succ, List.ofFn_zero, List.getD" in source
    assert "subst contribution" in source
    assert "let rankCount := pmWeightTids.length" in source
    assert "pmWeightTids : List Tid := [60, 61, 62]" in source
    assert "pmOutputTids : List Tid := [200, 201, 202]" in source
    assert "rankCount = 3" not in source
    assert "fw_embedding (pmStore 40)" not in source
    assert "ReductionRel" in source
    assert "sorry" not in source and "False.elim" not in source

    declarations = render_closed_relation_declarations(relation.dependent_chain_plan, "SyntheticEmbedding")
    sm_nodes = "[" + ", ".join(composer_module._node_text(node) for node in ir.sm_nodes) + "]"
    pm_nodes = "[" + ", ".join(composer_module._node_text(node) for node in ir.pm_nodes) + "]"
    witness_source = "\n".join((
        declarations, "namespace TrainVerify.Denote.SyntheticEmbedding", "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        source, "#print axioms segment_000000", "end", "end TrainVerify.Denote.SyntheticEmbedding", "",
    ))
    witness = tmp_path / "GeneratedVocabEmbeddingReductionWitness.lean"
    witness.write_text(witness_source)
    assert witness.read_text() == witness_source


def test_closed_vocab_embedding_reduction_accepts_sparse_writers_in_full_frame():
    ir, relation = _synthetic_vocab_embedding_reduction_relation(rank_count=3, framed=True)

    source = render_closed_segment(ir, relation, "segment_000000")

    assert source.count('op := "OpName.FW_identity"') >= 4
    assert "smNodes.take 1" in source
    assert "pmNodes.take 0" in source
    assert "pmNodes.take 2" in source
    assert "pmNodes.take 4" in source
    assert source.count("foldl_faithful_middle_writer") >= 4
    assert "sorry" not in source and "False.elim" not in source


def test_closed_k_rank_full_producer_chunks_segment_is_generic_and_exact():
    ir, relation = _synthetic_k_rank_segment_relation(family="chunks")
    source = render_closed_segment(ir, relation, "segment_000000")
    assert "allGatherPrimDimN_chunks_ofFn" in source
    assert "let rankCount := pmTids.length" in source
    assert "pmTids : List Tid := [30, 31, 32, 33]" in source
    assert source.count('op := "OpName.ChunkPrim"') >= 8
    assert "smNodes := []" in source
    assert "FW_identity" not in source
    assert "hSmWriter" not in source
    assert "rankCount = 4" not in source


def test_closed_k_rank_sum_producer_segment_is_generic_and_exact():
    ir, relation = _synthetic_k_rank_segment_relation(family="sum")
    source = render_closed_segment(ir, relation, "segment_000000")
    assert "fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum" in source
    assert "let rankCount := pmInputTids.length" in source
    assert "pmInputTids : List Tid := [20, 21, 22, 23]" in source
    assert source.count('op := "OpName.FW_sum"') >= 10
    assert "rankCount = 4" not in source
    assert "AllReducePrim" not in source


def test_closed_k_rank_sum_producer_accepts_sparse_writers_and_full_frame_ranges():
    ir, relation = _synthetic_k_rank_segment_relation(family="sum", rank_count=4, framed=True)
    source = render_closed_segment(ir, relation, "segment_000000")
    assert source.count("foldl (applyNodeDistributedFaithful SyntheticKRank.smGraph)") >= 1
    assert source.count("foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph)") >= 1
    assert source.count('op := "OpName.FW_sum"') >= 10
    assert source.count('op := "OpName.FW_identity"') >= 12
    assert "pmNodes.take 0" in source
    assert "pmNodes.take 2" in source
    assert "pmNodes.take 4" in source
    assert "pmNodes.take 6" in source
    assert "smNodes.take 1" in source
    assert "rankCount = 4" not in source
    assert "sorry" not in source and "False.elim" not in source


@pytest.mark.parametrize("side, mutation", [
    ("sm", "live-input"), ("sm", "semantic-output"),
    ("pm", "live-input"), ("pm", "semantic-output"),
])
def test_closed_k_rank_sum_producer_rejects_frame_writes_to_live_tids(side, mutation):
    ir, relation = _synthetic_k_rank_segment_relation(family="sum", rank_count=4, framed=True)
    if side == "sm":
        ir.sm_nodes[1].outs = [10 if mutation == "live-input" else 11]
    else:
        ir.pm_nodes[5].outs = [20 if mutation == "live-input" else 30]
    with pytest.raises(ValueError, match="frame node writes a live relation/authority TID"):
        render_closed_segment(ir, relation, "segment_000000")


def test_closed_k_rank_sum_producer_rejects_nonpartitioned_sparse_footprint():
    ir, relation = _synthetic_k_rank_segment_relation(family="sum", rank_count=4, framed=True)
    transition = replace(relation.transition_specs[0], pm_node_indices=(4, 6, 8, 8))
    relation = SimpleNamespace(**{**relation.__dict__, "transition_specs": (transition,)})
    with pytest.raises(ValueError, match="exact semantic-writer/frame partition"):
        render_closed_segment(ir, relation, "segment_000000")


def test_fresh_k_rank_sum_frame_segment_witness_is_renderer_output():
    ir, relation = _synthetic_k_rank_segment_relation(family="sum", rank_count=4, framed=True)
    namespace = "SyntheticKRank"
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    rendered = render_closed_segment(ir, relation, "segment_000000")
    sm_nodes = "[" + ", ".join(
        composer_module._node_text(node) for node in ir.sm_nodes
    ) + "]"
    pm_nodes = "[" + ", ".join(
        composer_module._node_text(node) for node in ir.pm_nodes
    ) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 4, nodes := {pm_nodes} }}",
        rendered,
        "#print axioms segment_000000",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/GeneratedKRankSumProducerFrameWitness.lean"
    )
    assert witness.read_text() == source
    assert rendered == render_closed_segment(ir, relation, "segment_000000")
    assert "sorry" not in source


def test_closed_k_rank_alltoall_segment_is_generic_and_exact():
    ir, relation = _synthetic_k_rank_segment_relation(family="alltoall")
    source = render_closed_segment(ir, relation, "segment_000000")
    assert "allGatherPrimDimN_allToAllPrimWithDims_ofFn" in source
    assert "let rankCount := pmTids.length" in source
    assert "pmTids : List Tid := [30, 31, 32, 33]" in source
    assert source.count('op := "OpName.AllToAllPrim"') >= 8
    assert "rankCount = 4" not in source


def test_generated_k_rank_alltoall_witness_is_exact_renderer_output():
    ir, relation = _synthetic_k_rank_segment_relation(family="alltoall")
    namespace = "SyntheticKRank"
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    rendered = render_closed_segment(ir, relation, "segment_000000")
    sm_nodes = "[" + ", ".join(
        composer_module._node_text(node) for node in ir.sm_nodes
    ) + "]"
    pm_nodes = "[" + ", ".join(
        composer_module._node_text(node) for node in ir.pm_nodes
    ) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 4, nodes := {pm_nodes} }}",
        rendered,
        "#print axioms segment_000000",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/GeneratedKRankAllToAllCompilerWitness.lean"
    )
    assert witness.read_text() == source
    assert "sorry" not in source and "False.elim" not in source


def test_closed_k_rank_alltoall_selects_certificate_by_exact_transition_facts():
    ir, relation = _synthetic_k_rank_segment_relation(family="alltoall")
    expected = render_closed_segment(ir, relation, "segment_000000")
    unrelated_input = RelationFactSpec(
        "sharded", ("sm:99:0", "pm:99:0", "pm:100:0"), gather_dim=0,
    )
    unrelated = replace(relation.certificates[0], input_fact=unrelated_input)
    with_unrelated = SimpleNamespace(
        **{**relation.__dict__, "certificates": (unrelated, relation.certificates[0])}
    )

    assert render_closed_segment(ir, with_unrelated, "segment_000000") == expected


def test_closed_k_rank_alltoall_rejects_malformed_or_ambiguous_exact_certificate():
    ir, relation = _synthetic_k_rank_segment_relation(family="alltoall")
    certificate = relation.certificates[0]
    malformed = replace(
        certificate,
        input_fact=RelationFactSpec(
            "sharded", ("sm:99:0", "pm:99:0", "pm:100:0"), gather_dim=0,
        ),
    )
    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir, SimpleNamespace(**{**relation.__dict__, "certificates": (malformed,)}),
            "segment_000000",
        )

    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir,
            SimpleNamespace(
                **{**relation.__dict__, "certificates": (certificate, certificate)}
            ),
            "segment_000000",
        )


def test_generated_k_rank_full_producer_chunks_witness_is_exact_renderer_output():
    ir, relation = _synthetic_k_rank_segment_relation(family="chunks")
    namespace = "SyntheticKRank"
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    rendered = render_closed_segment(ir, relation, "segment_000000")
    sm_nodes = "[" + ", ".join(
        composer_module._node_text(node) for node in ir.sm_nodes
    ) + "]"
    pm_nodes = "[" + ", ".join(
        composer_module._node_text(node) for node in ir.pm_nodes
    ) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 4, nodes := {pm_nodes} }}",
        rendered,
        "#print axioms segment_000000",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/GeneratedKRankFullProducerChunksCompilerWitness.lean"
    )
    assert witness.read_text() == source
    assert "sorry" not in source and "False.elim" not in source


def test_closed_k_rank_full_producer_chunks_selects_one_exact_typed_certificate():
    ir, relation = _synthetic_k_rank_segment_relation(family="chunks")
    certificate = relation.certificates[0]
    expected = render_closed_segment(ir, relation, "segment_000000")
    unrelated = replace(
        certificate,
        input_fact=RelationFactSpec(
            "joined", ("sm:99:0",), joined_pm_step="pm:99:0"
        ),
    )
    with_unrelated = SimpleNamespace(
        **{**relation.__dict__, "certificates": (unrelated, certificate)}
    )

    assert render_closed_segment(ir, with_unrelated, "segment_000000") == expected

    _, alltoall_relation = _synthetic_k_rank_segment_relation(family="alltoall")
    wrong_class = replace(
        alltoall_relation.certificates[0],
        rule_id=certificate.rule_id,
        lean_theorem=certificate.lean_theorem,
        input_fact=certificate.input_fact,
        output_fact=certificate.output_fact,
    )
    malformed_certificates = (
        wrong_class,
        replace(certificate, rule_id="unrelated-rule"),
        replace(certificate, lean_theorem="TrainVerify.Denote.unrelated"),
        replace(certificate, input_fact=unrelated.input_fact),
        replace(
            certificate,
            output_fact=RelationFactSpec(
                "sharded",
                ("sm:99:0", *(f"pm:{rank + 1}:0" for rank in range(4))),
                gather_dim=1,
            ),
        ),
    )
    for malformed in malformed_certificates:
        with pytest.raises(ValueError, match="one exact typed certificate"):
            render_closed_segment(
                ir,
                SimpleNamespace(**{**relation.__dict__, "certificates": (malformed,)}),
                "segment_000000",
            )

    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir,
            SimpleNamespace(
                **{**relation.__dict__, "certificates": (certificate, certificate)}
            ),
            "segment_000000",
        )


def test_closed_k_rank_segment_rejects_wrong_writer_footprint_and_embedding_exactly():
    ir, relation = _synthetic_k_rank_segment_relation(family="chunks")
    bad_transition = replace(relation.transition_specs[0], pm_node_indices=(0, 1, 2, 3, 4))
    bad = SimpleNamespace(**{**relation.__dict__, "transition_specs": (bad_transition,)})
    with pytest.raises(ValueError, match="writers must lie inside the complete PM frame"):
        render_closed_segment(ir, bad, "segment_000000")

    embedding = replace(
        relation.transition_specs[0],
        rule_id="embedding-hidden-sharded-k-rank",
        lean_theorem="TrainVerify.Denote.fw_embedding_hidden_shards_k_rank",
    )
    unsupported = SimpleNamespace(**{**relation.__dict__, "transition_specs": (embedding,)})
    with pytest.raises(
        ValueError,
        match="embedding-hidden-sharded-k-rank lacks one exact typed certificate",
    ):
        render_closed_segment(ir, unsupported, "segment_000000")


def test_relation_plan_schema_versions_list_indexed_k_rank_facts():
    from trainverify.bridge_emitter.relation_compiler import RelationPlan

    plan = RelationPlan(
        family="fixture",
        terminal_rule_id="fixture",
        synchronized_steps=(),
        certificates=(),
        unresolved_frontiers=(),
        unresolved_layouts=(),
        unresolved_side_conditions=(),
    )

    assert plan.schema_version == 7


def test_closed_relation_facts_materialize_list_indexed_k_rank_shards():
    refs = ("sm:0:0", "pm:0:0", "pm:1:0", "pm:2:0", "pm:3:0")
    spec = RelationFactSpec("sharded", refs, gather_dim=1)
    steps = (
        SimpleNamespace(step_id=refs[0], side="sm", output_tid=10, output_shape=[2, 8]),
        *(
            SimpleNamespace(
                step_id=ref,
                side="pm",
                output_tid=20 + rank,
                output_shape=[2, 2],
            )
            for rank, ref in enumerate(refs[1:])
        ),
    )
    transition = SimpleNamespace(
        transition_id="k-rank",
        pre_facts=(),
        post_facts=(spec,),
    )
    relation = SimpleNamespace(
        transition_specs=(transition,),
        dependency_plan=SimpleNamespace(order=("k-rank",)),
        zigzag_regions=(),
        certificates=(),
    )

    facts = materialize_closed_relation_facts(
        SimpleNamespace(init_lineages={}), SimpleNamespace(steps=steps), relation
    )

    assert len(facts) == 1
    assert facts[0].kind == "sharded"
    assert facts[0].sm_tid == 10
    assert facts[0].pm_tids == (20, 21, 22, 23)
    assert facts[0].gather_dim == 1
    assert facts[0].full_shape == (2, 8)
    assert facts[0].shard_shape == (2, 2)


def test_init_lineage_relation_fact_preserves_ordered_k_rank_authority():
    sharded = SimpleNamespace(
        ts=10, tsShape=[8, 6],
        tps=[(0, 20), (1, 21), (2, 22), (3, 23)],
        tpShapes=[[2, 6], [2, 6], [2, 6], [2, 6]],
        gatherDim=None, replicated=False,
    )
    fact = relation_compiler_module.init_lineage_relation_fact(sharded)
    assert fact == RelationFactSpec(
        "sharded", ("init:10", "init:20", "init:21", "init:22", "init:23"),
        gather_dim=0,
    )

    replicated = SimpleNamespace(
        ts=11, tsShape=[3, 5],
        tps=[(0, 30), (1, 30), (2, 30)],
        tpShapes=[[3, 5], [3, 5], [3, 5]],
        gatherDim=None, replicated=True,
    )
    assert relation_compiler_module.init_lineage_relation_fact(replicated) == RelationFactSpec(
        "replicated", ("init:11", "init:30", "init:30", "init:30")
    )
    distinct_replicas = SimpleNamespace(
        ts=12, tsShape=[3, 5],
        tps=[(0, 31), (1, 32), (2, 33)],
        tpShapes=[[3, 5], [3, 5], [3, 5]],
        gatherDim=None, replicated=True,
    )
    with pytest.raises(RelationCompositionError, match="value authority"):
        relation_compiler_module.init_lineage_relation_fact(distinct_replicas)


def test_close_k_rank_init_authority_requires_exact_ordered_lineage():
    lineage = SimpleNamespace(
        ts=50, tsShape=[100, 16],
        tps=[(rank, 60 + rank) for rank in range(4)],
        tpShapes=[[100, 4] for _ in range(4)],
        gatherDim=1, replicated=False,
    )
    exact = ("init:50", "init:60", "init:61", "init:62", "init:63")
    wrong = ("init:50", "init:61", "init:60", "init:62", "init:63")
    closed, remaining, layouts = relation_compiler_module.close_k_rank_init_authority(
        SimpleNamespace(init_lineages={50: lineage}),
        (exact, wrong), ("sharded", "sharded"),
    )
    assert closed == (RelationFactSpec("sharded", exact, gather_dim=1),)
    assert remaining == (wrong,)
    assert layouts == ("sharded",)


def test_init_lineage_relation_fact_rejects_reordered_or_malformed_authority():
    reordered = SimpleNamespace(
        ts=10, tsShape=[8, 6], tps=[(1, 21), (0, 20)],
        tpShapes=[[4, 6], [4, 6]], gatherDim=0, replicated=False,
    )
    with pytest.raises(RelationCompositionError, match="ordered ranks"):
        relation_compiler_module.init_lineage_relation_fact(reordered)
    malformed = SimpleNamespace(
        ts=10, tsShape=[8, 6], tps=[(0, 20), (1, 21)],
        tpShapes=[[3, 6], [3, 6]], gatherDim=0, replicated=False,
    )
    with pytest.raises(RelationCompositionError, match="shape contract"):
        relation_compiler_module.init_lineage_relation_fact(malformed)


def test_closed_sharded_fact_resolves_pm_init_tids_from_lineage_authority():
    lineage = SimpleNamespace(
        ts=10, tsShape=[8, 6],
        tps=[(0, 20), (1, 21), (2, 22), (3, 23)],
        tpShapes=[[2, 6], [2, 6], [2, 6], [2, 6]],
    )
    spec = RelationFactSpec(
        "sharded", ("init:10", "init:20", "init:21", "init:22", "init:23"),
        gather_dim=0,
    )
    transition = SimpleNamespace(transition_id="init-weight", pre_facts=(spec,), post_facts=())
    relation = SimpleNamespace(
        transition_specs=(transition,), dependency_plan=SimpleNamespace(order=("init-weight",)),
        zigzag_regions=(), certificates=(),
    )
    facts = materialize_closed_relation_facts(
        SimpleNamespace(init_lineages={10: lineage}), SimpleNamespace(steps=()), relation
    )
    assert len(facts) == 1
    assert facts[0].sm_tid == 10
    assert facts[0].pm_tids == (20, 21, 22, 23)
    assert facts[0].full_shape == (8, 6)
    assert facts[0].shard_shape == (2, 6)


def test_closed_relation_facts_materialize_and_render_k_rank_replicated():
    refs = ("sm:0:0", "pm:0:0", "pm:1:0", "pm:2:0", "pm:3:0")
    spec = RelationFactSpec("replicated", refs)
    steps = (
        SimpleNamespace(step_id=refs[0], side="sm", output_tid=10, output_shape=(1, 8, 6)),
        *(SimpleNamespace(step_id=ref, side="pm", output_tid=20 + rank,
                          output_shape=(1, 8, 6)) for rank, ref in enumerate(refs[1:])),
    )
    transition = SimpleNamespace(transition_id="replicated", pre_facts=(), post_facts=(spec,))
    relation = SimpleNamespace(
        transition_specs=(transition,),
        dependency_plan=SimpleNamespace(order=("replicated",)),
        zigzag_regions=(), certificates=(),
    )
    facts = materialize_closed_relation_facts(
        SimpleNamespace(init_lineages={}), SimpleNamespace(steps=steps), relation
    )
    assert len(facts) == 1
    assert facts[0].kind == "replicated"
    assert facts[0].sm_tid == 10
    assert facts[0].pm_tids == (20, 21, 22, 23)
    assert facts[0].full_shape == (1, 8, 6)
    assert facts[0].shard_shape == (1, 8, 6)

    chain = SimpleNamespace(
        complete=True, relation_facts=facts, authority_facts=(),
        anchor_fact=SimpleNamespace(fact_id="anchor", side="sm", tid=99, shape=(1,)),
        states=(SimpleNamespace(state_id="state_000000", fact_ids=(facts[0].fact_id,)),),
    )
    source = render_closed_relation_declarations(chain, "KRankFixture")
    assert ".replicated 10 [20, 21, 22, 23] [1, 8, 6]" in source


def test_closed_relation_facts_materialize_and_render_generic_joined_result():
    spec = RelationFactSpec(
        "joined", ("sm:1:0",), joined_pm_step="pm:8:0"
    )
    proof = SimpleNamespace(steps=(
        SimpleNamespace(step_id="sm:1:0", side="sm", output_tid=10, output_shape=(1,)),
        SimpleNamespace(step_id="pm:8:0", side="pm", output_tid=20, output_shape=(1,)),
    ))
    transition = SimpleNamespace(
        transition_id="terminal",
        pre_facts=(),
        post_facts=(spec,),
    )
    relation = SimpleNamespace(
        transition_specs=(transition,),
        dependency_plan=SimpleNamespace(order=("terminal",)),
        certificates=(),
        zigzag_regions=(),
    )
    facts = materialize_closed_relation_facts(
        SimpleNamespace(init_lineages={}), proof, relation
    )
    assert len(facts) == 1
    assert facts[0].kind == "joined"
    assert facts[0].sm_tid == 10
    assert facts[0].pm_tids == ()
    assert facts[0].joined_pm_tid == 20
    assert facts[0].full_shape == (1,)

    chain = SimpleNamespace(
        complete=True,
        relation_facts=facts,
        authority_facts=(),
        anchor_fact=SimpleNamespace(
            fact_id="anchor_fact",
            side="sm",
            tid=10,
            shape=(1,),
        ),
        states=(SimpleNamespace(
            state_id="state:initial",
            fact_ids=("anchor_fact", facts[0].fact_id),
        ),),
    )
    source = render_closed_relation_declarations(chain, "GeneratedKRank")
    assert ".joined 10 20 [1]" in source


def test_closed_relation_declarations_render_list_indexed_k_rank_fact():
    fact = SimpleNamespace(
        fact_id="fact_000000",
        kind="sharded",
        sm_tid=10,
        pm_tids=(20, 21, 22, 23),
        gather_dim=1,
        full_shape=(2, 8),
        shard_shape=(2, 2),
    )
    chain = SimpleNamespace(
        complete=True,
        relation_facts=(fact,),
        authority_facts=(),
        anchor_fact=SimpleNamespace(
            fact_id="anchor", side="sm", tid=99, shape=(1,)
        ),
        states=(SimpleNamespace(state_id="state_000000", fact_ids=("fact_000000",)),),
    )

    source = render_closed_relation_declarations(chain, "KRankFixture")

    assert ".sharded 10 [20, 21, 22, 23] 1 [2, 8] [2, 2]" in source
    assert ".ordinary 10 20 21" not in source


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
            assert fact.sm_tid >= 0
            if fact.kind == "joined":
                assert fact.joined_pm_tid is not None and fact.joined_pm_tid >= 0
                assert fact.pm_tids == ()
            else:
                assert fact.pm_tids and all(tid >= 0 for tid in fact.pm_tids)
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
        expected_authority_kinds = {"tensor_eq", "tensor_shape", "gather", "packed_cu"}
        if ir.tensor_value_bound_contracts:
            expected_authority_kinds.add("label_bound")
        assert {fact.kind for fact in chain.authority_facts} == expected_authority_kinds
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    ir, proof, relation = compiled_goal(1, str(root))
    by_id = {item.transition_id: item for item in relation.transition_specs}
    segment = next(item for item in relation.dependent_chain_plan.segments
        if len(item.transition_ids) == 1 and by_id[item.transition_ids[0]].lean_theorem.endswith("fw_rms_norm_allGather0_commute_2_core"))
    source = render_closed_rms_norm_segment(ir, relation, segment.segment_id)
    assert "Ordinary2Rel.rms_norm_2d" in source
    assert "have hWeightFact" in source
    assert "have hweight : smStore" in source
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


def _synthetic_bw_unshuffle_goal(monkeypatch):
    """Synthetic op substitution on real YOCO topology, not production authority."""
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    ir = load_goal_ir(1, str(Path(__file__).resolve().parents[2]))
    for side in ("sm", "pm"):
        for node in getattr(ir, side + "_nodes"):
            if node.op == "FW_maybe_shuffle":
                node.op = "BW_maybe_unshuffle"
        attr = side + "_replica_groups"
        setattr(ir, attr, tuple(
            replace(group, irname="BW_maybe_unshuffle")
            if "maybe_shuffle" in group.irname else group
            for group in getattr(ir, attr)
        ))
    return ir


def test_synthetic_bw_unshuffle_closes_ordinary_to_zigzag(monkeypatch):
    ir = _synthetic_bw_unshuffle_goal(monkeypatch)
    proof = compile_proof_plan(ir, build_default_registry())
    assert proof.supported
    relation = compile_relation_plan(ir, proof)
    assert relation.unresolved_frontiers == ()
    assert relation.unresolved_side_conditions == ()
    assert relation.dependent_chain_plan.complete
    certs = [c for c in relation.certificates
             if c.rule_id == "bw-maybe-unshuffle-ordinary-to-zigzag-two-rank"]
    assert len(certs) == 1
    cert = certs[0]
    assert type(cert) is relation_compiler_module.FaithfulShuffleCertificate
    assert cert.pm_replica_members == ((0, 9750), (1, 9751))
    transitions = {t.transition_id: t for t in relation.transition_specs}
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if any(transitions[t].rule_id == cert.rule_id for t in s.transition_ids))
    source = render_closed_segment(ir, relation, segment.segment_id)
    assert "applyNodeDistributed_bw_maybe_unshuffle_out" in source
    assert "applyNodeDistributedFaithful_shuffle_out" not in source
    assert "Ordinary2Rel.to_zigzag_shuffle" in source
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert "sorry" not in source


@pytest.fixture(scope="module", params=["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def shuffle_entry_case(request):
    with pytest.MonkeyPatch.context() as mp:
        ir = _synthetic_bw_unshuffle_goal(mp)
        if request.param == "FW_maybe_shuffle":
            for side in ("sm", "pm"):
                for node in getattr(ir, side + "_nodes"):
                    if node.op == "BW_maybe_unshuffle":
                        node.op = request.param
                attr = side + "_replica_groups"
                setattr(ir, attr, tuple(replace(g, irname=request.param)
                    if g.irname == "BW_maybe_unshuffle" else g for g in getattr(ir, attr)))
        relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    cert = next(c for c in relation.certificates
                if type(c) is relation_compiler_module.FaithfulShuffleCertificate)
    transition = next(t for t in relation.transition_specs if t.rule_id == cert.rule_id)
    segment = next(s for s in relation.dependent_chain_plan.segments
                   if transition.transition_id in s.transition_ids)
    return ir, relation, cert, transition, segment


def _singleton_shuffle_entry(case):
    """Synthetic isolated boundary; graph refs need new exact declarations for Lean."""
    from copy import deepcopy
    ir, relation, cert, transition, segment = deepcopy(case)
    ir.sm_nodes = [ir.sm_nodes[i] for i in transition.sm_node_indices]
    ir.pm_nodes = [ir.pm_nodes[i] for i in transition.pm_node_indices]
    ir.sm_shapes = [(ir.sm_nodes[0].ins[0], list(cert.full_shape)), *ir.sm_shapes]
    ir.pm_shapes = [(n.ins[0], list(cert.shard_shape)) for n in ir.pm_nodes] + ir.pm_shapes
    ir.lineage = LineageGoal(ir.sm_nodes[0].outs[0], list(cert.full_shape),
        [(n.rank, n.outs[0]) for n in ir.pm_nodes], [list(cert.shard_shape)] * 2, gatherDim=0)
    old_post = transition.post_facts[0]
    cert = replace(cert, output_step_triple=("sm:0:0", "pm:0:0", "pm:1:0"))
    post = replace(old_post, step_triple=cert.output_step_triple)
    transition = _bind_certificate_digest(replace(transition,
        sm_node_indices=(0,), pm_node_indices=(0, 1), post_facts=(post,)), cert)
    chain = relation.dependent_chain_plan
    removed = {f.fact_id for f in chain.relation_facts
               if any(f.source in t.post_facts for t in relation.transition_specs
                      if t.transition_id in segment.transition_ids and t.transition_id != transition.transition_id)}
    segment = replace(segment, transition_ids=(transition.transition_id,), sm_range=(0, 1), pm_range=(0, 2))
    target = next(f.fact_id for f in chain.relation_facts if f.source == old_post)
    chain = replace(chain, segments=(segment,),
        initial_state_id=segment.pre_state_id, terminal_state_id=segment.post_state_id,
        terminal_target_fact_id=target, retained_target_fact_ids=(target,),
        expected_sm_node_count=1, expected_pm_node_count=2,
        states=tuple(replace(s, fact_ids=tuple(f for f in s.fact_ids if f not in removed))
                     if s.state_id == segment.post_state_id else s for s in chain.states
                     if s.state_id in (segment.pre_state_id, segment.post_state_id)),
        relation_facts=tuple(replace(f, source=post) if f.source == old_post else f for f in chain.relation_facts))
    relation = replace(relation, certificates=(cert,), transition_specs=(transition,),
        dependent_chain_plan=chain,
        zigzag_regions=tuple(replace(region, frontier_triples=tuple(
            cert.output_step_triple if f == old_post.step_triple else f for f in region.frontier_triples))
            for region in relation.zigzag_regions))
    return ir, relation, cert, transition, segment


@pytest.mark.parametrize("mutation", ["mixed", "cp4", "params", "order"])
def test_shuffle_entry_matcher_remains_bounded(shuffle_entry_case, mutation):
    from copy import deepcopy
    ir, relation, cert, transition, segment = deepcopy(shuffle_entry_case)
    proof = compile_proof_plan(ir, build_default_registry())
    if mutation == "cp4":
        ir.pm_num_ranks = 4
    else:
        target = cert.output_step_triple[-1]
        changes = {"mixed": {"op": "FW_maybe_shuffle" if ir.pm_nodes[transition.pm_node_indices[1]].op == "BW_maybe_unshuffle" else "BW_maybe_unshuffle"},
                   "params": {"parameters": (4, 1)}, "order": {"rank": 0}}
        proof = replace(proof, steps=tuple(replace(s, **changes[mutation])
                        if s.step_id == target else s for s in proof.steps))
    call = lambda: relation_compiler_module.advance_faithful_shuffle_relation_frontiers(
        ir, proof, (cert.output_step_triple,), ("zigzag",))
    if mutation == "mixed":
        certificates, frontiers, _ = call()
        assert not certificates and frontiers == (cert.output_step_triple,)
    else:
        with pytest.raises(RelationCompositionError):
            call()


def test_shuffle_entry_singleton_is_shared_and_dispatched(shuffle_entry_case):
    ir, relation, cert, transition, segment = _singleton_shuffle_entry(shuffle_entry_case)
    spec = relation_compiler_module.get_closed_rule_spec(cert.rule_id)
    assert spec.certificate_type is relation_compiler_module.FaithfulShuffleCertificate
    assert spec.singleton_renderer == "composer:render_closed_shuffle_entry_segment"
    source = render_closed_segment(ir, relation, segment.segment_id)
    assert "Ordinary2Rel.to_zigzag_shuffle" in source
    assert "hRmsOut" not in source
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert "sorry" not in source


@pytest.mark.parametrize("mutation", ["digest", "duplicate", "type", "theorem", "roles",
    "certificate_shape", "node_shape", "rank_count", "group_order", "group_op",
    "metadata_source", "region", "packed", "frame"])
def test_shuffle_entry_rejects_stale_authority(shuffle_entry_case, mutation):
    from copy import deepcopy
    ir, relation, cert, transition, segment = deepcopy(shuffle_entry_case)
    chain = relation.dependent_chain_plan
    if mutation == "digest":
        transition = replace(transition, certificate_digest="0" * 64)
    elif mutation == "duplicate":
        relation = replace(relation, certificates=(*relation.certificates, cert))
    elif mutation in {"type", "theorem", "roles", "certificate_shape", "metadata_source"}:
        changes = {"theorem": {"lean_theorem": "wrong"},
                   "roles": {"input_step_triple": tuple(reversed(cert.input_step_triple))},
                   "certificate_shape": {"shard_shape": (1, 1)},
                   "metadata_source": {"metadata_source": "wrong"}}
        bad = SimpleNamespace(**vars(cert)) if mutation == "type" else replace(cert, **changes[mutation])
        relation = replace(relation, certificates=tuple(bad if c is cert else c for c in relation.certificates))
        if mutation in {"certificate_shape", "metadata_source"}:
            transition = _bind_certificate_digest(transition, bad)
    elif mutation == "node_shape":
        tid = ir.pm_nodes[transition.pm_node_indices[0]].outs[0]
        ir.pm_shapes = [(t, shape) for t, shape in ir.pm_shapes if t != tid] + [(tid, [1, 1])]
    elif mutation == "rank_count":
        ir.pm_num_ranks = 4
    elif mutation in {"group_order", "group_op"}:
        ir.pm_replica_groups = tuple(
            replace(g, members=tuple(reversed(g.members))) if mutation == "group_order"
            else replace(g, irname="wrong")
            for g in ir.pm_replica_groups if any(m.primary_out_tid == cert.pm_replica_members[0][1] for m in g.members))
    elif mutation == "region":
        relation = replace(relation, zigzag_regions=())
    elif mutation == "packed":
        ir.packed_cu_contracts = ()
    elif mutation == "frame":
        chain = replace(chain, states=tuple(replace(s, fact_ids=())
            if s.state_id == segment.pre_state_id else s for s in chain.states))
    relation = replace(relation, dependent_chain_plan=chain, transition_specs=tuple(
        transition if t.transition_id == transition.transition_id else t for t in relation.transition_specs))
    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize("side", ["sm", "pm"])
def test_shuffle_entry_backward_missing_group_fails_closed(shuffle_entry_case, side):
    from copy import deepcopy
    ir, relation, cert, transition, segment = deepcopy(shuffle_entry_case)
    setattr(ir, side + "_replica_groups", ())
    if ir.sm_nodes[transition.sm_node_indices[0]].op == "FW_maybe_shuffle":
        # Preserve the established forward legacy-authority path.
        assert render_closed_segment(ir, relation, segment.segment_id)
    else:
        with pytest.raises(ValueError, match="backward shuffle requires explicit"):
            render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize("singleton", [False, True])
def test_shuffle_entry_coordinated_buddy_order_is_rejected(shuffle_entry_case, singleton):
    from copy import deepcopy
    case = _singleton_shuffle_entry(shuffle_entry_case) if singleton else deepcopy(shuffle_entry_case)
    ir, relation, cert, transition, segment = case
    bad = replace(cert, pm_replica_members=tuple(reversed(cert.pm_replica_members)))
    ir.pm_replica_groups = tuple(
        replace(g, members=tuple(reversed(g.members)))
        if any(m.primary_out_tid == cert.pm_replica_members[0][1] for m in g.members) else g
        for g in ir.pm_replica_groups)
    transition = _bind_certificate_digest(transition, bad)
    relation = replace(relation,
        certificates=tuple(bad if c == cert else c for c in relation.certificates),
        transition_specs=tuple(transition if t.transition_id == transition.transition_id else t
                               for t in relation.transition_specs))
    with pytest.raises(ValueError, match="buddy roles"):
        render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize("singleton", [False, True])
def test_shuffle_entry_missing_only_packed_authority_is_rejected(shuffle_entry_case, singleton):
    from copy import deepcopy
    case = _singleton_shuffle_entry(shuffle_entry_case) if singleton else deepcopy(shuffle_entry_case)
    ir, relation, cert, transition, segment = case
    chain = relation.dependent_chain_plan
    packed = next(f.fact_id for f in chain.authority_facts
                  if f.kind == "packed_cu" and f.tid == cert.contract_metadata_tid and f.side == "pm")
    before = next(s for s in chain.states if s.state_id == segment.pre_state_id)
    assert packed in before.fact_ids and len(before.fact_ids) > 1
    chain = replace(chain, states=tuple(
        replace(s, fact_ids=tuple(f for f in s.fact_ids if f != packed))
        if s.state_id == before.state_id else s for s in chain.states))
    relation = replace(relation, dependent_chain_plan=chain)
    with pytest.raises(ValueError, match="authority is not live"):
        render_closed_segment(ir, relation, segment.segment_id)


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
    assert "have hWeightRel" in source
    assert "have hWeight : smStore 5596 = pmStore 5596 := hWeightRel.1" in source
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
    ir, proof, relation = compiled_goal(1, str(root))
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
    init_chunk_count = sum(
        getattr(item, "rule_id", "") == "init-lineage-full-to-two-chunks"
        for item in relation.certificates
    )
    assert init_chunk_count > 0
    assert source.count("foldl_faithful_chunk_middle_writer") == 2 * init_chunk_count
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
    assert "have hw0 : fact_" in source
    assert "change smStore 4953 = pmStore 4953 ∧" in source
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


def test_closed_full_producer_renderer_supports_single_transition_generic_component(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    segment = relation.dependent_chain_plan.segments[278]

    source = render_closed_full_producer_to_segment(ir, relation, segment.segment_id)

    assert segment.sm_range == (539, 540) and segment.pm_range == (1184, 1189)
    assert len(segment.transition_ids) == 1
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert "GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks" in source
    assert "authority_replicated_eq_5660.Holds" in source
    assert "authority_replicated_shape_pm_5660.Holds" in source
    assert "authority_pm_metadata_eq_000000_5602" in source
    assert "authority_packed_cu_000000" in source
    assert "decodeCuSeqlens (pmFinal 5602) = [0, 4096]" in source
    assert "smFinal 5661" in source and "pmFinal 9914" in source and "pmFinal 9915" in source
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


def test_final_zigzag_certificate_consumers_keep_exact_metadata_authority_live(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    chain = relation.dependent_chain_plan
    assert chain is not None
    states = {state.state_id: set(state.fact_ids) for state in chain.states}
    transitions = {transition.transition_id: transition for transition in relation.transition_specs}
    authority = {fact.fact_id: fact for fact in chain.authority_facts}

    mixed = next(segment for segment in chain.segments if any(
        transitions[tid].rule_id == "zigzag-full-moe-expert-split-two-rank"
        for tid in segment.transition_ids
    ) and segment.segment_id == "segment_000479")
    unshuffle = next(segment for segment in chain.segments if any(
        transitions[tid].rule_id == "zigzag-to-ordinary-unshuffle-two-rank"
        for tid in segment.transition_ids
    ) and segment.segment_id == "segment_000485")

    for segment in (mixed, unshuffle):
        live = [authority[fact_id] for fact_id in states[segment.pre_state_id] if fact_id in authority]
        packed = [fact for fact in live if fact.kind == "packed_cu"]
        assert len(packed) == 1
        assert any(
            fact.kind == "tensor_eq"
            and fact.left_side == "pm"
            and fact.right_side == "pm"
            and fact.right_tid == packed[0].tid
            for fact in live
        )

    assert not any(
        authority[fact_id].kind == "packed_cu"
        for fact_id in states[unshuffle.post_state_id]
        if fact_id in authority
    )


def test_terminal_ce_consumer_keeps_ordinary_rms_relation_live(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    chain = relation.dependent_chain_plan
    assert chain is not None
    transitions = {transition.transition_id: transition for transition in relation.transition_specs}
    states = {state.state_id: set(state.fact_ids) for state in chain.states}
    records = {record.source: record for record in chain.relation_facts}
    ce_segment = next(segment for segment in chain.segments if any(
        transitions[tid].rule_id == "inner-chunk-ce-projection-gather-two-rank"
        for tid in segment.transition_ids
    ))
    ce_transition = next(
        transitions[tid] for tid in ce_segment.transition_ids
        if transitions[tid].rule_id == "inner-chunk-ce-projection-gather-two-rank"
    )
    input_spec = next(fact for fact in ce_transition.pre_facts if fact.layout == "ordinary")
    input_record = records[input_spec]
    assert input_record.kind == "ordinary"
    assert all(records[fact].fact_id in states[ce_segment.pre_state_id] for fact in ce_transition.pre_facts)
    rms_segment = chain.segments[chain.segments.index(ce_segment) - 1]
    assert input_record.fact_id in states[rms_segment.post_state_id]
    assert render_closed_rms_norm_segment(ir, relation, rms_segment.segment_id)


def test_closed_goal2_ce_snd_terminal_renderer_is_generic_exact_single_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(2, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    terminal = next(
        transition for transition in relation.transition_specs
        if transition.rule_id == "inner-chunk-ce-projection-gather-two-rank"
    )
    assert terminal.post_facts[0].layout == "joined_ordinary"
    assert terminal.post_facts[0].joined_pm_step is not None
    terminal_fact = next(
        fact for fact in relation.dependent_chain_plan.relation_facts
        if fact.source == terminal.post_facts[0]
    )
    assert terminal_fact.joined_pm_tid == 4927
    source = render_closed_ce_snd_segment(ir, relation, "segment_000487")
    assert source == render_closed_segment(ir, relation, "segment_000487")
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("segment_000487_sm_nodes.foldl") == 1
    assert source.count("segment_000487_pm_nodes.foldl") == 1
    assert source.count("ClosedDepSegmentCertificate ") == 1
    assert source.count("private theorem segment_000487_sm_writer_value") == 1
    assert source.count("private theorem segment_000487_pm0_writer_value") == 1
    assert source.count("private theorem segment_000487_pm1_writer_value") == 1
    assert source.count("private theorem segment_000487_semantic_core") == 1
    assert source.count("private theorem segment_000487_output_shapes") == 1
    assert source.count("private theorem segment_000487_output_relation") == 1
    certificate = source[source.index("private def segment_000487 :"):]
    assert "foldl_faithful_middle_writer" not in certificate
    assert "fw_inner_chunk_ce_snd_allGatherDim0_shards" not in certificate
    assert "fw_inner_chunk_ce_snd_shape" not in certificate
    assert "fw_inner_chunk_ce_snd_allGatherDim0_shards" in source
    assert source.count("RelationCompiler.inner_chunk_ce_snd_labels_independent") == 2
    assert "applyNode_fw_inner_chunk_ce_snd_out_1p" in source
    assert "op := \"OpName.AllGatherPrim\"" in source
    assert "segment_000487_pm_final pmStore 4927" in source
    assert "public_value := ?_" in source
    assert "applyNode_allGatherPrimDimN_out" in source
    assert "authority_transition_eq_sm_6256_pm_6256.Holds" in source
    assert "authority_transition_shape_pm_6256.Holds" in source
    assert "ins := [6255, 6256, 4931]" in source
    assert "ins := [11712, 6256, 11714]" in source
    assert "ins := [11713, 6256, 11715]" in source
    assert "chunkPrimDimN" not in source
    assert "Goal_2" not in source


def test_closed_ce_snd_terminal_renderer_rejects_wrong_theorem_and_node_roles(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(2, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    segment = next(item for item in relation.dependent_chain_plan.segments if item.segment_id == "segment_000487")
    transition_id = segment.transition_ids[0]
    transitions = tuple(
        replace(item, lean_theorem="TrainVerify.Denote.wrong")
        if item.transition_id == transition_id else item
        for item in relation.transition_specs
    )
    with pytest.raises(ValueError, match="CE .snd renderer theorem mismatch"):
        render_closed_ce_snd_segment(ir, replace(relation, transition_specs=transitions), segment.segment_id)
    nodes = list(ir.pm_nodes)
    nodes[segment.pm_range[0]] = replace(nodes[segment.pm_range[0]], rank=1)
    with pytest.raises(ValueError, match="CE .snd node roles"):
        render_closed_ce_snd_segment(replace(ir, pm_nodes=nodes), relation, segment.segment_id)


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
    for prerequisite in ("hFact1", "hFact2", "hFact3", "hFact14"):
        assert f" at {prerequisite}" in source
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
    attention = render_closed_segment(ir, relation, "segment_000007")
    assert "Ordinary2Rel.sliding_attention" in attention
    segment = next(item for item in relation.dependent_chain_plan.segments if item.segment_id == "segment_000007")
    target_id = segment.transition_ids[0]
    broken = replace(
        relation,
        transition_specs=tuple(
            replace(item, rule_id="synthetic-unsupported-k-rank-rule")
            if item.transition_id == target_id else item
            for item in relation.transition_specs
        ),
    )
    with pytest.raises(ValueError, match="unsupported closed segment family.*synthetic-unsupported"):
        render_closed_segment(ir, broken, "segment_000007")

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
    assert "have hwEq2 : smStore 5604 = pmStore 5604 := hwRel2.1" in source
    assert "pmFinal 5602 = pmStore 5602" in source
    assert "metadata_region_id" not in source


def test_goals34_atomic_full_producer_two_local_linear_renderer_is_exact_single_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    expected_ranges = {3: ((5, 8), (38, 47)), 4: ((5, 8), (36, 45))}
    for goal_id in (3, 4):
        ir = load_goal_ir(goal_id, str(root))
        relation = compile_relation_plan(
            ir, compile_proof_plan(ir, build_default_registry())
        )
        segment = relation.dependent_chain_plan.segments[5]

        source = render_closed_linear_segment(ir, relation, segment.segment_id)

        assert (segment.sm_range, segment.pm_range) == expected_ranges[goal_id]
        assert source == render_closed_segment(ir, relation, segment.segment_id)
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count("Ordinary2Rel.per_head_linear_fullProducer_chunks") == 1
        assert source.count("Ordinary2Rel.per_head_linear ") == 2
        assert source.count("foldl_faithful_chunk_writer") == 2
        assert f"Goal_{goal_id}" not in source

        complete_source = compose_closed_dependent_chain(ir, relation, f"ClosedGoal{goal_id}")
        assert f"noncomputable def ClosedGoal{goal_id}_chain" in complete_source
        assert "segment_000005" in complete_source
        assert "segment_000017" in complete_source


def test_goal4_zigzag_full_producer_retains_exact_metadata_region_authority(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(4, str(root))
    relation = compile_relation_plan(
        ir, compile_proof_plan(ir, build_default_registry())
    )
    chain = relation.dependent_chain_plan
    segment = next(
        item for item in chain.segments if item.segment_id == "segment_000278"
    )
    states = {item.state_id: item for item in chain.states}
    records = {item.source: item for item in chain.relation_facts}
    transitions = {item.transition_id: item for item in relation.transition_specs}
    transition = transitions[segment.transition_ids[0]]
    pre = records[transition.pre_facts[0]]
    assert (pre.metadata_tid, pre.metadata_region_id) == (5602, 0)
    assert "authority_pm_metadata_eq_000000_5602" in states[segment.pre_state_id].fact_ids

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "[authority_pm_metadata_eq_000000_5602" in source
    assert "decodeCuSeqlens (pmFinal 5602) = [0, 4096]" in source
    assert len(source.encode()) < 2_500_000


def test_goals34_mixed_moe_renderer_accepts_actual_atomic_topologies(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    expected_transition_counts = {3: 16, 4: 17}

    for goal_id in (3, 4):
        ir = load_goal_ir(goal_id, str(root))
        relation = compile_relation_plan(
            ir, compile_proof_plan(ir, build_default_registry())
        )
        chain = relation.dependent_chain_plan
        segment = next(
            item for item in chain.segments if item.segment_id == "segment_000017"
        )
        states = {item.state_id: item for item in chain.states}
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
        fresh = [item for item in after.fact_ids if item not in before.fact_ids]

        source = render_closed_mixed_moe_segment(
            ir, relation, segment.segment_id
        )

        assert len(segment.transition_ids) == expected_transition_counts[goal_id]
        assert source == render_closed_segment(ir, relation, segment.segment_id)
        assert len(source.encode()) < 2_500_000
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count("segment_000017_sm_nodes.foldl") == 2
        assert source.count("segment_000017_pm_nodes.foldl") == 2
        assert all(fact_id in source for fact_id in fresh)
        assert f"Goal_{goal_id}" not in source
        if goal_id == 4:
            assert "Ordinary2Rel.topk_routing_gate_scores" in source

        complete_source = compose_closed_dependent_chain(
            ir, relation, f"ClosedGoal{goal_id}AfterMixedMoe"
        )
        assert f"noncomputable def ClosedGoal{goal_id}AfterMixedMoe_chain" in complete_source
        assert "segment_000017" in complete_source


def test_goals34_zigzag_mixed_moe_renderer_preserves_layout_through_exact_unshuffle(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]

    for goal_id in (3, 4):
        ir = load_goal_ir(goal_id, str(root))
        relation = compile_relation_plan(
            ir, compile_proof_plan(ir, build_default_registry())
        )
        chain = relation.dependent_chain_plan
        segment = next(
            item for item in chain.segments if item.segment_id == "segment_000270"
        )
        states = {item.state_id: item for item in chain.states}
        records = {item.source: item for item in chain.relation_facts}
        transitions = {
            item.transition_id: item for item in relation.transition_specs
        }
        ordered = [transitions[item] for item in segment.transition_ids]
        unshuffle = ordered[12]

        assert len(ordered) == 17
        assert unshuffle.rule_id == "zigzag-topk-unshuffle-two-rank"
        assert records[unshuffle.pre_facts[0]].kind == "zigzag"
        assert records[unshuffle.post_facts[0]].kind == "ordinary"

        source = render_closed_mixed_moe_segment(
            ir, relation, segment.segment_id
        )
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
        intra = {
            records[fact].fact_id
            for transition in ordered
            for fact in (*transition.pre_facts, *transition.post_facts)
            if records[fact].fact_id not in before.fact_ids
        }

        assert source == render_closed_segment(ir, relation, segment.segment_id)
        assert len(source.encode()) < 2_500_000
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count("ClosedDepSegmentCertificate ") == 1
        assert "GeneratedPatterns.Zigzag2Rel.all2all_moe_gmm_full_1x2" in source
        assert "GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single" in source
        assert "GeneratedPatterns.Ordinary2Rel" in source
        assert all(fact_id in source for fact_id in intra)
        assert all(
            fact_id in source
            for fact_id in after.fact_ids
            if fact_id not in before.fact_ids
        )
        assert f"Goal_{goal_id}" not in source

        closed = compose_closed_dependent_chain(
            ir, relation, f"ClosedGoal{goal_id}AfterZigzagMixedMoe"
        )
        assert "segment_000480" in closed
        assert "smNodes =" in closed and "pmNodes =" in closed


def test_closed_exit_unshuffle_renderer_is_generic_exact_single_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))

    source = render_closed_unshuffle_segment(ir, relation, "segment_000485")

    assert source == render_closed_segment(ir, relation, "segment_000485")
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("ClosedDepSegmentCertificate ") == 1
    assert "GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single" in source
    assert source.count("applyNodeDistributedFaithful_unshuffle_out") == 3
    assert "ins := [6247, 6252]" in source
    assert "ins := [11598, 6252]" in source
    assert "ins := [11599, 6252]" in source
    assert "authority_packed_cu_000000.Holds" in source
    assert "authority_pm_metadata_eq_000000_5602.Holds" in source
    assert "PackedCuSeqlensWF.decoded_single" in source
    assert "Goal_1" not in source


def test_closed_bw_shuffle_reuses_exact_unshuffle_relation_and_renderer(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    selected = []
    for nodes in (ir.sm_nodes, ir.pm_nodes):
        for node in nodes:
            if node.op == "FW_maybe_unshuffle" and node.ins[1] == 6252:
                node.op = "BW_maybe_shuffle"
                selected.append(node)
    assert len(selected) == 3
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    transition = next(
        item for item in relation.transition_specs
        if item.rule_id == "bw-maybe-shuffle-zigzag-to-ordinary-two-rank"
    )
    segment = next(
        item for item in relation.dependent_chain_plan.segments
        if transition.transition_id in item.transition_ids
    )
    source = render_closed_unshuffle_segment(ir, relation, segment.segment_id)
    assert source == render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("applyNodeDistributed_bw_maybe_shuffle_out") == 3
    assert "bw_maybe_shuffle_collective_eq_fw_unshuffle" in source


def test_goals34_closed_indexed_stack_renderer_is_truthful_generic_and_one_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    for goal_id in (3, 4):
        ir = load_goal_ir(goal_id, str(root))
        relation = compile_relation_plan(
            ir, compile_proof_plan(ir, build_default_registry())
        )
        segment = relation.dependent_chain_plan.segments[-1]
        source = render_closed_indexed_stack_segment(
            ir, relation, segment.segment_id
        )
        assert source == render_closed_segment(ir, relation, segment.segment_id)
        assert source.count(f"private def {segment.segment_id}_smFinal") == 1
        assert source.count(f"private def {segment.segment_id}_pmFinal") == 1
        assert source.count(
            f"{segment.segment_id}_smNodes.foldl (applyNodeDistributedFaithful"
        ) == 1
        assert source.count(
            f"{segment.segment_id}_pmNodes.foldl (applyNodeDistributedFaithful"
        ) == 1
        assert source.count("ClosedDepSegmentCertificate ") == 1
        assert source.count(
            f"private theorem {segment.segment_id}_writer_values_source_preservation"
        ) == 1
        assert sum(
            f"private theorem {segment.segment_id}_source_{index:02d}" in source
            for index in range(24)
        ) == 24
        assert source.count(
            f"private theorem {segment.segment_id}_indexed_stack_semantic"
        ) == 1
        assert (
            "sound := by\n    intro smStore pmStore hstate\n"
            f"    simpa [{segment.segment_id}_smFinal, {segment.segment_id}_pmFinal] using "
            f"({segment.segment_id}_publish_state smStore pmStore hstate)"
        ) in source
        assert "fw_stack_allGather0_dim1_commute_2d_element" in source
        assert source.count("applyNode_fw_stack_out") == 3
        assert "JoinedIndexedStack2Rel" in source
        target = next(
            transition.post_facts[0] for transition in relation.transition_specs
            if transition.rule_id == "indexed-stack-gather-two-rank"
        )
        terminal_fact = next(
            fact for fact in relation.dependent_chain_plan.relation_facts
            if fact.source == target
        )
        assert terminal_fact.joined_pm_tid == ir.lineage.tps[0][1]
        assert f"({segment.segment_id}_pmFinal pmStore) {terminal_fact.joined_pm_tid}" in source
        assert "public_value := ?_" in source
        assert "applyNode_allGatherPrimDimN_out" in source
        assert source.count("change GeneratedPatterns.Ordinary2Rel") == 24
        assert "have hSource00" in source and "have hSource23" in source
        assert (
            f"source_relations := {segment.segment_id}_ordered_source_relations "
            "smStore pmStore hstate"
        ) in source
        assert f"Goal_{goal_id}" not in source



def test_goal1_closed_ce_fst_renderer_uses_exact_live_authority_and_one_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(
        ir, compile_proof_plan(ir, build_default_registry())
    )
    source = render_closed_ce_fst_segment(ir, relation, "segment_000487")
    assert source == render_closed_segment(ir, relation, "segment_000487")
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("ClosedDepSegmentCertificate ") == 1
    assert "GeneratedPatterns.fw_inner_chunk_ce_fst_allGather0_commute_2_of" in source
    assert "hChunks" in source and ".Holds smStore pmStore" in source
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, "ClosedGoal1CE"
    )
    assert ".labelChunks 4931 11714 11715 0 [4096] [2048]" in declarations
    assert "applyNode_fw_inner_chunk_ce_fst_out_1p" in source
    assert "Goal_1" not in source

    chain = relation.dependent_chain_plan
    label_less = tuple(item for item in chain.relation_facts
                       if item.kind != "label_chunks")
    with pytest.raises(ValueError, match="label-chunk authority"):
        render_closed_ce_fst_segment(
            ir, replace(relation, dependent_chain_plan=replace(
                chain, relation_facts=label_less
            )), "segment_000487"
        )


def test_closed_exit_unshuffle_renderer_rejects_non_authoritative_metadata(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    chain = relation.dependent_chain_plan
    assert chain is not None
    aliases = tuple(
        replace(fact, right_tid=6254)
        if fact.fact_id == "authority_pm_metadata_eq_000000_5602"
        else fact
        for fact in chain.authority_facts
    )
    broken_chain = replace(chain, authority_facts=aliases)

    with pytest.raises(ValueError, match="metadata equality authority mismatch"):
        render_closed_unshuffle_segment(
            ir, replace(relation, dependent_chain_plan=broken_chain), "segment_000485"
        )


def test_closed_chain_composer_advances_past_atomic_per_head_zigzag_rms(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(1, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    source = compose_closed_dependent_chain(ir, relation, "ClosedGoal1")
    assert "noncomputable def ClosedGoal1_chain" in source
    for segment_id in ("segment_000257", "segment_000265", "segment_000278", "segment_000479"):
        assert segment_id in source

def test_goal3_closed_norm_full_producer_segment_is_generic_exact_single_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    ir = load_goal_ir(3, str(root))
    relation = compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))

    source = render_closed_segment(ir, relation, "segment_000479")

    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert source.count("segment_000479_sm_nodes.foldl") == 1
    assert source.count("segment_000479_pm_nodes.foldl") == 1
    assert "GeneratedPatterns.Zigzag2Rel.norm_linear_fullProducer_chunks" in source
    assert "hProducer1.trans hProducer0.symm" in source
    assert "hDecodedCu" in source
    assert "Goal_3" not in source
    assert "6218" in source and "[64, 1024]" in source


def test_goals34_standalone_topk_unshuffle_is_generic_exact_and_one_fold(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    expected = {
        3: ("topk_routing_map", 6248, (6221, 11524, 11525), (6249, 11602, 11603)),
        4: ("topk_routing_gate_scores", 6250, (6222, 11526, 11527), (6251, 11604, 11605)),
    }

    for goal_id, (theorem, metadata_tid, projected, outputs) in expected.items():
        ir = load_goal_ir(goal_id, str(root))
        relation = compile_relation_plan(
            ir, compile_proof_plan(ir, build_default_registry())
        )
        source = render_closed_segment(ir, relation, "segment_000480")

        assert len(source.encode()) < 2_500_000
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count("ClosedDepSegmentCertificate ") == 1
        assert f"GeneratedPatterns.Zigzag2Rel.{theorem}" in source
        assert "GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single" in source
        assert "change GeneratedPatterns.Zigzag2Rel" in source
        assert "change GeneratedPatterns.Ordinary2Rel" in source
        assert f"(pmFinal {metadata_tid})" in source
        assert "authority_packed_cu_000000.Holds" in source
        assert f"authority_pm_metadata_eq_000000_{metadata_tid}.Holds" in source
        assert all(str(tid) in source for tid in (*projected, *outputs))
        assert source.count("applyNodeDistributedFaithful_unshuffle_out") == 3
        assert "fun x => x" not in source
        assert f"Goal_{goal_id}" not in source


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
        "  .cons (segment_parameterized Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph) "
        "SyntheticClosedChain_suffix_000002"
    ) in source
    assert "theorem SyntheticClosedChain_chain_sm_nodes : SyntheticClosedChain_chain.smNodes = Synthetic.Graphs.smGraph.nodes := by\n  rfl" in source
    assert "theorem SyntheticClosedChain_chain_pm_nodes : SyntheticClosedChain_chain.pmNodes = Synthetic.Graphs.pmGraph.nodes := by\n  rfl" in source


def test_closed_bundle_is_deterministic_bounded_public_and_acyclic(monkeypatch):
    anchor = SimpleNamespace(
        fact_id="anchor_fact", kind="tensor_shape", side="sm", tid=7, shape=(1,)
    )
    states = tuple(
        SimpleNamespace(state_id=f"state_{index:06d}", fact_ids=("anchor_fact",))
        for index in range(3)
    )
    segments = (
        SimpleNamespace(
            segment_id="segment_000000", pre_state_id=states[0].state_id,
            post_state_id=states[1].state_id, transition_ids=("transition_0",),
        ),
        SimpleNamespace(
            segment_id="segment_000001", pre_state_id=states[1].state_id,
            post_state_id=states[2].state_id, transition_ids=("transition_1",),
        ),
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(), authority_facts=(), anchor_fact=anchor,
        states=states, segments=segments, terminal_target_fact_id="terminal_fact",
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain,
        transition_specs=tuple(
            SimpleNamespace(
                transition_id=f"transition_{index}",
                rule_id=f"synthetic-{index}",
                lean_theorem=f"Synthetic.Theorems.synthetic_{index}",
            )
            for index in range(2)
        ),
    )
    ir = SimpleNamespace(
        n=17, sm_graph_ref="Synthetic.Graphs.smGraph",
        pm_graph_ref="Synthetic.Graphs.pmGraph",
        public_statement_module="Synthetic.Graphs",
    )
    rendered = {
        "segment_000000": (
            "private def segment_000000 :\n"
            "    ClosedDepSegmentCertificate Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph "
            "state_000000 state_000001 := by\n  exact syntheticCertificate\n"
        ),
        "segment_000001": (
            "private noncomputable def segment_000001\n"
            "    (smGraph pmGraph : GraphDecl) :\n"
            "    ClosedDepSegmentCertificate smGraph pmGraph state_000001 state_000002 := by\n"
            "  exact syntheticParameterizedCertificate smGraph pmGraph\n"
        ),
    }
    monkeypatch.setattr(
        composer_module, "render_closed_segment",
        lambda _ir, _relation, segment_id: rendered[segment_id],
    )
    public_text = (
        "theorem prove_goal_17_closed : Synthetic.Graphs.goal_17_stmt_full := by\n"
        "  exact syntheticPublicProof\n"
    )
    monkeypatch.setattr(
        composer_module, "render_closed_public_theorem",
        lambda _ir, _relation, _namespace: public_text,
    )

    first = compose_closed_dependent_bundle(
        ir, relation, "SyntheticClosed", "Synthetic.Bundle", max_source_bytes=2500
    )
    second = compose_closed_dependent_bundle(
        ir, relation, "SyntheticClosed", "Synthetic.Bundle", max_source_bytes=2500
    )

    assert first == second
    assert list(first) == [
        "Facts000.lean", "States000.lean", "Segment000000.lean",
        "Segment000001.lean", "Chain.lean", "Public.lean",
    ]
    assert all(len(payload) < 2500 for payload in first.values())
    decoded = {path: payload.decode() for path, payload in first.items()}
    assert public_text.strip() in decoded["Public.lean"]
    assert "import Synthetic.Bundle.Chain\n" in decoded["Public.lean"]
    assert (
        "theorem SyntheticClosed_chain_sm_nodes : SyntheticClosed_chain.smNodes = "
        "Synthetic.Graphs.smGraph.nodes := by\n  rfl"
        in decoded["Chain.lean"]
    )
    assert (
        "theorem SyntheticClosed_chain_pm_nodes : SyntheticClosed_chain.pmNodes = "
        "Synthetic.Graphs.pmGraph.nodes := by\n  rfl"
        in decoded["Chain.lean"]
    )
    assert "native_decide" not in decoded["Chain.lean"]
    assert (
        ".cons (segment_000001 Synthetic.Graphs.smGraph Synthetic.Graphs.pmGraph)"
        in decoded["Chain.lean"]
    )
    assert "private def segment_000000" not in decoded["Segment000000.lean"]
    assert "noncomputable def segment_000000" in decoded["Segment000000.lean"]
    order = {f"Synthetic.Bundle.{Path(path).stem}": index for index, path in enumerate(first)}
    for index, source in enumerate(decoded.values()):
        for imported in (line[7:] for line in source.splitlines() if line.startswith("import Synthetic.Bundle.")):
            assert order[imported] < index


def test_closed_bundle_publisher_replaces_tree_without_stale_files(tmp_path):
    destination = tmp_path / "Goal17Closed"
    destination.mkdir()
    (destination / "stale.lean").write_text("stale")
    bundle = {"Facts000.lean": b"facts\n", "Public.lean": b"public\n"}

    _publish_closed_bundle(bundle, destination)

    assert sorted(path.name for path in destination.iterdir()) == ["Facts000.lean", "Public.lean"]
    assert (destination / "Facts000.lean").read_bytes() == b"facts\n"
    assert not list(tmp_path.glob(".Goal17Closed.staged-*"))


def test_closed_bundle_kernel_check_emits_importable_olean_tree(tmp_path, monkeypatch):
    project = tmp_path / "trainverify"
    source_root = project / "denote" / "fixture" / "Goal1Closed"
    source_root.mkdir(parents=True)
    bundle = {
        "Facts000.lean": b"def fact := True\n",
        "States000.lean": b"import denote.fixture.Goal1Closed.Facts000\n",
    }
    for relative, payload in bundle.items():
        (source_root / relative).write_bytes(payload)

    calls = []

    def fake_run(argv, **kwargs):
        calls.append((argv, kwargs))
        output = Path(argv[argv.index("-o") + 1])
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(b"olean")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(emit2_module.subprocess, "run", fake_run)
    failure = _compile_closed_bundle_sources(
        bundle,
        source_root,
        "denote.fixture.Goal1Closed",
        project_dir=project,
    )

    assert failure is None
    assert len(calls) == 2
    expected_root = project / ".lake/build/lib/lean/denote/fixture/Goal1Closed"
    assert calls[0][0][-3:] == [
        "-o",
        str(expected_root / "Facts000.olean"),
        str(source_root / "Facts000.lean"),
    ]
    assert calls[1][0][-3:] == [
        "-o",
        str(expected_root / "States000.olean"),
        str(source_root / "States000.lean"),
    ]
    assert (expected_root / "Facts000.olean").stat().st_mode & 0o777 == 0o400
    assert not list(tmp_path.glob(".Goal17Closed.previous-*"))


def test_closed_bundle_kernel_check_builds_missing_project_import_first(tmp_path, monkeypatch):
    project = tmp_path / "trainverify"
    authority = project / "denote" / "fixture" / "Authority.lean"
    authority.parent.mkdir(parents=True)
    authority.write_text("def authority := True\n")
    source_root = project / "denote" / "fixture" / "Goal1Closed"
    source_root.mkdir()
    bundle = {
        "Facts000.lean": b"import denote.fixture.Authority\ndef fact := authority\n",
    }
    (source_root / "Facts000.lean").write_bytes(bundle["Facts000.lean"])
    calls = []

    def fake_run(argv, **kwargs):
        calls.append(argv)
        output = Path(argv[argv.index("-o") + 1])
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(b"olean")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(emit2_module.subprocess, "run", fake_run)
    failure = _compile_closed_bundle_sources(
        bundle, source_root, "denote.fixture.Goal1Closed", project_dir=project
    )

    assert failure is None
    assert [Path(call[-1]).name for call in calls] == ["Authority.lean", "Facts000.lean"]
    assert calls[0][calls[0].index("-o") + 1] == str(
        project / ".lake/build/lib/lean/denote/fixture/Authority.olean"
    )


def test_closed_bundle_kernel_check_does_not_trust_newer_project_olean(tmp_path, monkeypatch):
    project = tmp_path / "trainverify"
    authority = project / "denote" / "fixture" / "Authority.lean"
    authority.parent.mkdir(parents=True)
    authority.write_text("def authority := True\n")
    source_root = project / "denote" / "fixture" / "Goal1Closed"
    source_root.mkdir()
    bundle = {
        "Facts000.lean": b"import denote.fixture.Authority\ndef fact := authority\n",
    }
    (source_root / "Facts000.lean").write_bytes(bundle["Facts000.lean"])
    object_path = project / ".lake/build/lib/lean/denote/fixture/Authority.olean"
    object_path.parent.mkdir(parents=True)
    object_path.write_bytes(b"stale-but-newer")
    os.utime(object_path, ns=(authority.stat().st_atime_ns, authority.stat().st_mtime_ns + 1))
    calls = []

    def fake_run(argv, **kwargs):
        calls.append(argv)
        output = Path(argv[argv.index("-o") + 1])
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(b"fresh-olean")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(emit2_module.subprocess, "run", fake_run)
    failure = _compile_closed_bundle_sources(
        bundle, source_root, "denote.fixture.Goal1Closed", project_dir=project
    )

    assert failure is None
    assert [Path(call[-1]).name for call in calls] == ["Authority.lean", "Facts000.lean"]
    assert object_path.read_bytes() == b"fresh-olean"


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
    segment = next(
        item for item in relation.dependent_chain_plan.segments
        if item.segment_id == "segment_000006"
    )
    transition_by_id = {item.transition_id: item for item in relation.transition_specs}
    fact_by_source = {
        item.source: item.fact_id for item in relation.dependent_chain_plan.relation_facts
    }
    post_fact_ids = {
        fact_by_source[source]
        for transition_id in segment.transition_ids
        for source in transition_by_id[transition_id].post_facts
    }
    assert len(post_fact_ids) == 2
    assert all(f"{fact_id}.Holds" in source for fact_id in post_fact_ids)
    assert source.count(
        f"let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref})"
    ) == 1
    assert source.count(
        f"let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref})"
    ) == 1
    assert "applyNodeDistributedFaithful smGraph" not in source
    assert "applyNodeDistributedFaithful pmGraph" not in source


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
            assert (
                f"change GeneratedPatterns.Zigzag2Rel "
                f"({segment_id}_smFinal smStore" in source
            )


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


def _synthetic_external_chain(initial_facts, target=None):
    target = target or SimpleNamespace(
        fact_id="terminal_relation", kind="ordinary", sm_tid=900,
        pm_rank0_tid=901, pm_rank1_tid=902,
        full_shape=(8, 4), shard_shape=(4, 4),
    )
    initial = SimpleNamespace(
        state_id="state_000000",
        fact_ids=tuple(fact.fact_id for fact in initial_facts),
    )
    terminal = SimpleNamespace(
        state_id="state_000001", fact_ids=(target.fact_id,)
    )
    chain = SimpleNamespace(
        complete=True,
        authority_facts=tuple(initial_facts),
        anchor_fact=initial_facts[0],
        relation_facts=(target,),
        states=(initial, terminal),
        segments=(SimpleNamespace(
            segment_id="segment_000000",
            pre_state_id=initial.state_id,
            post_state_id=terminal.state_id,
        ),),
        terminal_target_fact_id=target.fact_id,
    )
    return SimpleNamespace(dependent_chain_plan=chain)


def _synthetic_external_ir(*, tps=((0, 901), (1, 902))):
    return GoalIR(
        n=17, sm_nodes=[], pm_nodes=[], sm_shapes=[], pm_shapes=[],
        lineage=LineageGoal(
            ts=900, tsShape=[8, 4], tps=list(tps),
            tpShapes=[[4, 4] for _ in tps], gatherDim=0, replicated=False,
        ),
        prereqs=[],
        sm_graph_ref="Synthetic.Graphs.sm_goal_17",
        pm_graph_ref="Synthetic.Graphs.pm_goal_17",
        public_statement_module="Synthetic.Graphs",
        public_statement_ref="Synthetic.Generated.goal_17_stmt_full",
        lineage_ref="Synthetic.Generated.goal_17",
        init_goals_ref="Synthetic.Generated.initGoals",
        sm_num_ranks=1, pm_num_ranks=2,
        sm_input_value_classes=(SimpleNamespace(source="sm-alias", tids=(10, 11)),),
        pm_input_value_classes=(SimpleNamespace(source="pm-alias", tids=(20, 21)),),
        sm_input_value_classes_ref="Synthetic.Generated.smInputValueClasses",
        pm_input_value_classes_ref="Synthetic.Generated.pmInputValueClasses",
        packed_cu_contracts=(SimpleNamespace(
            side="pm", tid=30, total_tokens=8, num_ranks=2
        ),),
        tensor_value_bound_contracts=(SimpleNamespace(
            side="pm", tid=40, length=8, upper_bound=16
        ),),
        init_lineages={
            50: LineageGoal(
                ts=50, tsShape=[4], tps=[(0, 51)], tpShapes=[[4]],
                gatherDim=0, replicated=False,
            ),
            60: LineageGoal(
                ts=60, tsShape=[8, 4], tps=[(0, 61), (1, 62)],
                tpShapes=[[4, 4], [4, 4]], gatherDim=1, replicated=False,
            ),
        },
        full_init_goal_ids=(50, 60),
    )


def test_parser_recovers_exact_public_init_goals_reference(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]

    goal3 = load_goal_ir(3, str(root))
    goal4 = load_goal_ir(4, str(root))

    assert goal3.public_statement_ref == (
        "TrainVerify.Denote.GeneratedGoals.goal_3_stmt_full"
    )
    assert not goal3.public_statement_uses_contract_wrapper
    assert goal3.public_statement_contract_ref == (
        "TrainVerify.Denote.GeneratedGoals.Goal3FullExternalInputs"
    )
    assert goal3.public_statement_uses_faithful_evaluator
    assert goal4.public_statement_uses_contract_wrapper
    assert goal4.public_statement_contract_ref == (
        "TrainVerify.Denote.GeneratedGoals.Goal4ExternalInputContract"
    )
    assert goal4.sm_input_value_classes_ref == (
        "TrainVerify.Denote.Generated.smInputValueClasses"
    )
    assert goal4.pm_input_value_classes_ref == (
        "TrainVerify.Denote.Generated.pmInputValueClasses"
    )
    assert goal4.public_statement_ref == (
        "TrainVerify.Denote.GeneratedGoals.goal_4_stmt_full"
    )
    assert goal3.init_goals_ref == "TrainVerify.Denote.Generated.initGoals"
    assert goal4.init_goals_ref == (
        "TrainVerify.Denote.GeneratedGoals.goal_4_full_initGoals"
    )


def test_external_initial_state_renderer_chunks_large_fact_dispatchers():
    facts = tuple(
        SimpleNamespace(
            fact_id=f"shape_{tid}", kind="tensor_shape", side="sm",
            tid=tid, shape=(4,),
        )
        for tid in range(100, 165)
    )
    source = render_closed_external_initial_state(
        _synthetic_external_ir(), _synthetic_external_chain(facts), "SyntheticClosed"
    )
    assert source.count("private theorem SyntheticClosed_initial_chunk_") == 3
    assert "rcases List.mem_append.mp covered with hfact0 | covered" in source
    state_body = source.split("private theorem SyntheticClosed_initial_state", 1)[1]
    assert "rcases hfact with rfl | hfact" not in state_body


def test_external_initial_state_renderer_derives_every_authority_contract_exactly():
    facts = (
        SimpleNamespace(fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)),
        SimpleNamespace(fact_id="eq_sm", kind="tensor_eq", left_side="sm", left_tid=10, right_side="sm", right_tid=11),
        SimpleNamespace(fact_id="eq_singleton", kind="tensor_eq", left_side="sm", left_tid=50, right_side="pm", right_tid=51),
        SimpleNamespace(fact_id="gather_dim1", kind="gather", sm_tid=60, pm_rank0_tid=61, pm_rank1_tid=62, dim=1, full_shape=(8, 4), shard_shape=(4, 4)),
        SimpleNamespace(fact_id="packed_pm", kind="packed_cu", side="pm", tid=30, total_tokens=8, num_ranks=2),
        SimpleNamespace(fact_id="bound_pm", kind="label_bound", side="pm", tid=40, length=8, upper_bound=16),
    )
    ir = _synthetic_external_ir()
    ir.init_goals_ref = "Synthetic.Graphs.goal_17_full_initGoals"
    source = render_closed_external_initial_state(
        ir, _synthetic_external_chain(facts), "SyntheticClosed"
    )
    assert "StoreShapesHold initSM Synthetic.Graphs.sm_goal_17InitEnv" in source
    assert "InitGoalsHold Synthetic.Graphs.pm_goal_17.numRanks" in source
    assert "InputValueClassesHold Synthetic.Generated.smInputValueClasses" in source
    assert "InputValueClassesHold Synthetic.Generated.pmInputValueClasses" in source
    assert "InputValueClassesHold.eq_of_mem" in source
    assert "InitGoalHolds.singleton_value_eq" in source
    assert "InitGoalHolds.gather2_dim" in source
    assert "Synthetic.Generated.initGoal_50" in source
    assert "Synthetic.Graphs.initGoal_50" not in source
    assert "hPacked_0" in source and "exact hPacked_0" in source
    assert "hBound_0" in source and "exact hBound_0" in source
    assert ": state_000000.Holds initSM initPM" in source
    assert "Goal_17" not in source and "Tid" not in source


def test_external_initial_state_renderer_fails_closed_on_unsupported_orientation_and_kind():
    ir = _synthetic_external_ir()
    reverse = SimpleNamespace(
        fact_id="reverse", kind="tensor_eq",
        left_side="pm", left_tid=51, right_side="sm", right_tid=50,
    )
    with pytest.raises(ValueError, match="unsupported tensor equality orientation"):
        render_closed_external_initial_state(ir, _synthetic_external_chain((reverse,)), "SyntheticClosed")
    unknown = SimpleNamespace(fact_id="mystery", kind="oracle")
    with pytest.raises(ValueError, match="unsupported initial authority kind"):
        render_closed_external_initial_state(ir, _synthetic_external_chain((unknown,)), "SyntheticClosed")


def test_public_theorem_renderer_consumes_kernel_joined_target_for_singleton_public_lineage():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_faithful_evaluator = True
    ir.lineage.tsShape = [4, 4]
    ir.lineage.tpShapes = [[4, 4]]
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined_ordinary", sm_tid=900,
        pm_rank0_tid=910, pm_rank1_tid=911, joined_pm_tid=901,
        full_shape=(4, 4), shard_shape=(2, 4),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )
    source = render_closed_public_theorem(
        ir, _synthetic_external_chain((anchor,), target), "SyntheticClosed"
    )
    assert "theorem prove_goal_17_closed : Synthetic.Generated.goal_17_stmt_full" in source
    assert "using htarget.public_value" in source
    assert "reconstructWithDim_singleton" in source
    assert "reconstructWithDim_cons_cons_nonscalar" not in source
    assert "[(4, 4)]" not in source
    assert "= [[4, 4]]" in source
    assert "Pattern_17" not in source and "Goal_17" not in source


def test_public_theorem_renderer_accepts_canonical_joined_target():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_contract_wrapper = False
    ir.public_statement_uses_faithful_evaluator = True
    ir.sm_input_value_classes = ()
    ir.pm_input_value_classes = ()
    ir.packed_cu_contracts = ()
    ir.tensor_value_bound_contracts = ()
    ir.lineage.tsShape = [1]
    ir.lineage.tpShapes = [[1]]
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined", sm_tid=900,
        joined_pm_tid=901, full_shape=(1,),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )
    source = render_closed_public_theorem(
        ir, _synthetic_external_chain((anchor,), target), "SyntheticClosed"
    )
    assert "using hvalue" in source
    assert "= [[1]]" in source
    assert "hContract" not in source
    assert "hFaithfulContract" in source
    assert "InputValueClassesHold" not in source
    assert "public_from_shapes" not in source
    assert "SyntheticClosed_public_body_proof initSM initPM hSM hPM hInit" in source
    assert "rcases htarget with ⟨hvalue, hsmShape, hpmShape⟩" in source
    assert "htarget.full_shape" not in source
    assert "@[irreducible] private def SyntheticClosed_public_statement" in source
    assert "private theorem SyntheticClosed_target_from_external_inputs" in source
    assert "@[irreducible] private def SyntheticClosed_public_body_statement" in source
    assert "private theorem SyntheticClosed_public_body_proof" in source
    assert "private theorem SyntheticClosed_public_proof" in source
    assert "have htarget := SyntheticClosed_target_from_external_inputs" in source
    assert "simpa only [SyntheticClosed_public_statement]" in source


def test_public_theorem_renderer_bridges_faithful_certificate_to_plain_statement():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_contract_wrapper = False
    ir.public_statement_uses_faithful_evaluator = False
    ir.sm_input_value_classes = ()
    ir.pm_input_value_classes = ()
    ir.packed_cu_contracts = ()
    ir.tensor_value_bound_contracts = ()
    ir.lineage.tsShape = [1]
    ir.lineage.tpShapes = [[1]]
    ir.sm_nodes = [Node(0, "FW_identity", [10], [900])]
    ir.pm_nodes = [Node(0, "FW_identity", [20], [901])]
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined", sm_tid=900,
        joined_pm_tid=901, full_shape=(1,),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )

    source = render_closed_public_theorem(
        ir, _synthetic_external_chain((anchor,), target), "SyntheticClosed"
    )

    assert "denote_faithful_eq_plain_of_prefix" in source
    assert "(tid := 900) (k := 1)" in source
    assert "(tid := 901) (k := 1)" in source
    assert "unfold CoarseLineageHoldsWithInit" in source
    assert "simp only [Synthetic.Generated.goal_17, List.map] at hBody ⊢" in source
    assert "rw [← hSmPlain, ← hPmPlain]" in source


def test_faithful_plain_bridge_is_model_neutral():
    source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/FaithfulPlainBridge.lean"
    ).read_text()

    assert "import denote.yoco_goals" not in source
    assert "GeneratedPatterns." not in source
    assert "foldl_faithful_eq_plain_of_no_special" in source


def test_sequence_sharded_embedding_theorem_is_dynamic_k_and_model_neutral():
    path = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/EmbeddingSequenceShard.lean"
    )
    assert path.is_file()
    source = path.read_text()
    relation_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/RelationCompiler.lean"
    ).read_text()
    assert "theorem fw_embedding_allGatherPrimDimN_dim1_shared_weight" in source
    assert "theorem ShardedRel.fw_embedding_shared_weight_dim1" in relation_source
    assert "(K b s hidden : Nat)" in source
    assert "Goal_3" not in source and "716" not in source and "565" not in source
    assert "sorry" not in source and "axiom" not in source and "False.elim" not in source


def test_public_theorem_renderer_accepts_explicit_named_contract_bundle():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_contract_wrapper = False
    ir.public_statement_contract_ref = "Synthetic.Generated.ExternalInputs"
    ir.public_statement_uses_faithful_evaluator = True
    ir.lineage.tsShape = [1]
    ir.lineage.tpShapes = [[1]]
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined", sm_tid=900,
        joined_pm_tid=901, full_shape=(1,),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )

    source = render_closed_public_theorem(
        ir, _synthetic_external_chain((anchor,), target), "SyntheticClosed"
    )

    assert "intro initSM initPM hSM hPM hInit hContract" in source
    assert "rcases hContract with ⟨hSMValues, hPMValues, hPacked_0, hBound_0⟩" in source
    assert "unfold CoarseLineageHoldsWithInitDistributedFaithfulWithContract" not in source
    assert "simpa only [SyntheticClosed_public_body_statement, InitGoalHolds] using" in source
    assert "SyntheticClosed_public_body_proof initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0 hBound_0" in source


def test_public_theorem_renderer_ignores_unneeded_uncontracted_input_classes():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_contract_wrapper = False
    ir.pm_input_value_classes = ()
    ir.packed_cu_contracts = ()
    ir.tensor_value_bound_contracts = ()
    ir.lineage.tsShape = [1]
    ir.lineage.tpShapes = [[1]]
    ir.sm_input_value_classes = (SimpleNamespace(source="x", tids=(1, 2)),)
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined", sm_tid=900,
        joined_pm_tid=901, full_shape=(1,),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )
    source = render_closed_external_initial_state(
        ir, _synthetic_external_chain((anchor,), target), "SyntheticClosed"
    )
    assert "hSMValues" not in source


def test_public_theorem_renderer_rejects_required_uncontracted_input_class():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_contract_wrapper = False
    ir.pm_input_value_classes = ()
    ir.packed_cu_contracts = ()
    ir.tensor_value_bound_contracts = ()
    ir.lineage.tsShape = [1]
    ir.lineage.tpShapes = [[1]]
    ir.sm_input_value_classes = (SimpleNamespace(source="x", tids=(1, 2)),)
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined", sm_tid=900,
        joined_pm_tid=901, full_shape=(1,),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )
    required_eq = SimpleNamespace(
        fact_id="eq_sm", kind="tensor_eq", left_side="sm", left_tid=1,
        right_side="sm", right_tid=2,
    )
    with pytest.raises(ValueError, match="contract-free public statement"):
        render_closed_external_initial_state(
            ir, _synthetic_external_chain((anchor, required_eq), target), "SyntheticClosed"
        )


def test_public_theorem_renderer_accepts_joined_indexed_stack_target():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.public_statement_uses_faithful_evaluator = True
    ir.lineage.tsShape = [24, 4, 4]
    ir.lineage.tpShapes = [[24, 4, 4]]
    target = SimpleNamespace(
        fact_id="terminal_relation", kind="joined_indexed_stack_dim1", sm_tid=900,
        pm_rank0_tid=910, pm_rank1_tid=911, joined_pm_tid=901,
        full_shape=(24, 4, 4), shard_shape=(24, 2, 4),
    )
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )
    source = render_closed_public_theorem(
        ir, _synthetic_external_chain((anchor,), target), "SyntheticClosed"
    )
    assert "using htarget.public_value" in source
    assert "= [[24, 4, 4]]" in source


def test_public_theorem_renderer_rejects_unjoined_or_nonpublic_target():
    ir = _synthetic_external_ir(tps=((0, 901),))
    ir.lineage.tsShape = [4, 4]
    ir.lineage.tpShapes = [[4, 4]]
    anchor = SimpleNamespace(
        fact_id="shape_sm", kind="tensor_shape", side="sm", tid=10, shape=(4,)
    )
    unjoined = SimpleNamespace(
        fact_id="terminal_relation", kind="ordinary", sm_tid=900,
        pm_rank0_tid=901, pm_rank1_tid=999,
        full_shape=(4, 4), shard_shape=(2, 4),
    )
    with pytest.raises(ValueError, match="joined or ordered-sharded terminal fact"):
        render_closed_public_theorem(
            ir, _synthetic_external_chain((anchor,), unjoined), "SyntheticClosed"
        )
    wrong = SimpleNamespace(
        fact_id="terminal_relation", kind="joined_ordinary", sm_tid=900,
        pm_rank0_tid=910, pm_rank1_tid=911, joined_pm_tid=999,
        full_shape=(4, 4), shard_shape=(2, 4),
    )
    with pytest.raises(ValueError, match="singleton public lineage"):
        render_closed_public_theorem(
            ir, _synthetic_external_chain((anchor,), wrong), "SyntheticClosed"
        )


def test_external_initial_state_renderer_treats_omitted_init_gather_dim_as_zero():
    ir = _synthetic_external_ir()
    ir.init_lineages[60].gatherDim = None
    gather = SimpleNamespace(
        fact_id="gather_dim0", kind="gather", sm_tid=60,
        pm_rank0_tid=61, pm_rank1_tid=62, dim=0,
        full_shape=(8, 4), shard_shape=(4, 4),
    )
    source = render_closed_external_initial_state(
        ir, _synthetic_external_chain((gather,)), "SyntheticClosed"
    )
    assert "InitGoalHolds.gather2_dim" in source


def test_shape_authority_parser_rejects_partial_or_duplicate_entries():
    with pytest.raises(ValueError, match="duplicate.*TID"):
        parser_module.parse_shapes(
            "def shapes : List (Tid × Shape) := [(1, [2]), (1, [2])]"
        )
    with pytest.raises(ValueError, match="unparsed shape authority"):
        parser_module.parse_shapes(
            "def shapes : List (Tid × Shape) := [(1, [2]), malformed]"
        )


def test_lineage_authority_parser_rejects_missing_or_misaligned_rank_metadata():
    missing = "def goal : LineageGoal := { ts := 1, tsShape := [2], tpShapes := [[2]] }"
    with pytest.raises(ValueError, match="tps"):
        parser_module.parse_lineage_block(missing, "goal")
    misaligned = (
        "def goal : LineageGoal := { ts := 1, tsShape := [2], "
        "tps := [{ rank := 0, tid := 2 }], tpShapes := [] }"
    )
    with pytest.raises(ValueError, match="cardinality"):
        parser_module.parse_lineage_block(misaligned, "goal")


def test_definition_resolution_accepts_noncomputable_graph_authority():
    source = """namespace Example.Authority
noncomputable def sm : GraphDecl := by
  refine { numRanks := 4, nodes := ?_ }
  exact []
end Example.Authority
"""
    block = parser_module._definition_from_sources("sm", source)
    assert block.startswith("noncomputable def sm")
    assert parser_module._qualified_definition_name("sm", source) == "Example.Authority.sm"


def test_input_value_classes_are_optional_only_when_public_statement_does_not_require_them():
    assert parser_module.parse_input_value_classes(
        "def unrelated := 1", name="smInputValueClasses", required=False
    ) == ()
    with pytest.raises(ValueError, match="smInputValueClasses"):
        parser_module.parse_input_value_classes(
            "def unrelated := 1", name="smInputValueClasses", required=True
        )


@pytest.mark.parametrize(
    "forbidden",
    (
        "axiom forged : False",
        "private axiom forged : False",
        "theorem forged : False := sorryAx False true",
        "unsafe def forged : Nat := 0",
        "theorem forged (h : False) : True := False.elim h",
    ),
)
def test_closed_bundle_validation_rejects_forbidden_trust_constructs(forbidden):
    bundle = {
        "Chain.lean": (forbidden + "\n").encode(),
        "Public.lean": b"theorem public_ok : True := by trivial\n",
    }
    with pytest.raises(ValueError, match="forbidden"):
        composer_module._validate_closed_bundle(
            bundle, "denote.audit.Forbidden", 2_500_000, 0
        )


@pytest.mark.parametrize("heartbeats", (0, 500_001))
def test_closed_bundle_validation_rejects_unbounded_heartbeat_budget(heartbeats):
    bundle = {
        "Chain.lean": f"set_option maxHeartbeats {heartbeats}\n".encode(),
        "Public.lean": b"theorem public_ok : True := by trivial\n",
    }
    with pytest.raises(ValueError, match="heartbeat"):
        composer_module._validate_closed_bundle(
            bundle, "denote.audit.Heartbeat", 2_500_000, 0
        )


def test_closed_bundle_kernel_failure_preserves_public_snapshot(tmp_path, monkeypatch):
    public = tmp_path / "GoalClosed"
    public.mkdir()
    (public / "sentinel.lean").write_text("old authority\n")
    bundle = {
        "Chain.lean": b"theorem chain_ok : True := by trivial\n",
        "Public.lean": b"theorem public_ok : True := by trivial\n",
    }

    def reject(compiled_bundle, candidate, *args, **kwargs):
        assert compiled_bundle is bundle
        assert candidate != public
        assert (candidate / "Chain.lean").read_bytes() == bundle["Chain.lean"]
        object_path = (
            tmp_path / ".lake/build/lib/lean/denote/audit/GoalClosed/Chain.olean"
        )
        object_path.parent.mkdir(parents=True)
        object_path.write_bytes(b"candidate object")
        return "Chain.lean", 1, "kernel rejected candidate"

    monkeypatch.setattr(emit2_module, "_compile_closed_bundle_sources", reject)
    failure = emit2_module._compile_and_publish_closed_bundle(
        bundle, public, "denote.audit.GoalClosed", project_dir=tmp_path
    )

    assert failure == ("Chain.lean", 1, "kernel rejected candidate")
    assert {path.name: path.read_text() for path in public.iterdir()} == {
        "sentinel.lean": "old authority\n"
    }
    assert not list(tmp_path.glob(".GoalClosed.staged-*"))
    assert not (
        tmp_path / ".lake/build/lib/lean/denote/audit/GoalClosed/Chain.olean"
    ).exists()


def test_axiom_audit_rejects_project_axioms_and_missing_receipts():
    target = "TrainVerify.Denote.Whole.prove_all"
    emit2_module._validate_print_axioms_output(
        f"'{target}' depends on axioms: [propext, Classical.choice, Quot.sound]",
        (target,),
    )
    with pytest.raises(ValueError, match="untrusted axioms"):
        emit2_module._validate_print_axioms_output(
            f"'{target}' depends on axioms: [TrainVerify.injected]", (target,)
        )
    with pytest.raises(ValueError, match="missing #print axioms result"):
        emit2_module._validate_print_axioms_output("", (target,))
    private_native = (
        "_private.denote.Bundle.0.Helper._native.native_decide.ax_1_2"
    )
    emit2_module._validate_print_axioms_output(
        f"'{target}' depends on axioms: [{private_native}]", (target,)
    )


def test_chunked_aggregate_axiom_receipt_is_complete_and_fail_closed():
    target = "TrainVerify.Denote.Whole.prove_all"
    valid = "\n".join([
        f"AXIOM_RECEIPT_BEGIN {target} 2",
        "AXIOM propext",
        "AXIOM _private.denote.Bundle.0.Helper._native.native_decide.ax_1_2",
        f"AXIOM_RECEIPT_END {target} 2",
    ])
    emit2_module._validate_chunked_axioms_output(valid, target)
    with pytest.raises(ValueError, match="incomplete chunked axiom receipt"):
        emit2_module._validate_chunked_axioms_output(
            valid.replace("AXIOM propext\n", ""), target
        )
    with pytest.raises(ValueError, match="untrusted axioms"):
        emit2_module._validate_chunked_axioms_output(
            valid.replace("AXIOM propext", "AXIOM TrainVerify.injected"), target
        )


def test_axiom_audit_falls_back_to_same_aggregate_collector_on_printer_overflow(
    tmp_path, monkeypatch
):
    staged = tmp_path / "staged"
    staged.mkdir()
    (staged / "Main.lean").write_text("theorem marker : True := by trivial\n")
    target = "TrainVerify.Denote.Whole.prove_all"
    calls = []

    def run(*args, **kwargs):
        source = (staged / ".AxiomAudit.lean").read_text()
        calls.append(source)
        if len(calls) == 1:
            return SimpleNamespace(
                returncode=134, stdout="", stderr="Stack overflow detected. Aborting.\n"
            )
        assert f"#trainverify_print_axioms_chunked {target}" in source
        return SimpleNamespace(
            returncode=0,
            stdout="\n".join([
                f"AXIOM_RECEIPT_BEGIN {target} 1",
                "AXIOM propext",
                f"AXIOM_RECEIPT_END {target} 1",
            ]),
            stderr="",
        )

    monkeypatch.setattr(emit2_module.subprocess, "run", run)
    assert emit2_module._audit_closed_bundle_axioms(
        staged, "denote.Whole", (target,), project_dir=tmp_path
    ) is None
    assert len(calls) == 2
    assert f"#print axioms {target}" in calls[0]
    assert not (staged / ".AxiomAudit.lean").exists()


def test_closed_bundle_axiom_audit_precedes_publication(tmp_path, monkeypatch):
    public = tmp_path / "Whole"
    bundle = {"Main.lean": b"theorem prove_all : True := by trivial\n"}
    events = []

    monkeypatch.setattr(
        emit2_module, "_compile_closed_bundle_sources",
        lambda *args, **kwargs: events.append("kernel") or None,
    )
    monkeypatch.setattr(
        emit2_module, "_audit_closed_bundle_axioms",
        lambda *args, **kwargs: events.append("axioms") or None,
        raising=False,
    )

    def publish(*args, **kwargs):
        assert events == ["kernel", "axioms"]
        events.append("publish")

    monkeypatch.setattr(emit2_module, "_publish_staged_closed_bundle", publish)
    failure = emit2_module._compile_and_publish_closed_bundle(
        bundle,
        public,
        "denote.Whole",
        project_dir=tmp_path,
        axiom_targets=("TrainVerify.Denote.Whole.prove_all",),
    )
    assert failure is None
    assert events == ["kernel", "axioms", "publish"]
