from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


def _source(step_id, *, side, rank, shape):
    return SimpleNamespace(
        step_id=step_id,
        side=side,
        node_index=-1,
        rank=rank,
        op="Source",
        input_bindings=(),
        input_shapes=(),
        output_shape=shape,
        parameters=(),
    )


def _contiguous_fixture(k=3, *, full_shape=None, shard_shape=None):
    shard_shape = shard_shape or (2, 3, 4)
    full_shape = full_shape or (2, 3 * k, 4)
    sm_input = _source("sm:9:0", side="sm", rank=0, shape=full_shape)
    pm_inputs = tuple(
        _source(f"pm:{19 + rank}:0", side="pm", rank=rank, shape=shard_shape)
        for rank in range(k)
    )
    sm_writer = SimpleNamespace(
        step_id="sm:10:0", side="sm", node_index=10, rank=0,
        op="FW_contiguous", input_bindings=(sm_input.step_id,),
        input_shapes=(full_shape,), output_shape=full_shape, parameters=(),
    )
    pm_writers = tuple(
        SimpleNamespace(
            step_id=f"pm:{30 + rank}:0", side="pm", node_index=30 + rank,
            rank=rank, op="FW_contiguous",
            input_bindings=(pm_inputs[rank].step_id,),
            input_shapes=(shard_shape,), output_shape=shard_shape, parameters=(),
        )
        for rank in range(k)
    )
    plan = SimpleNamespace(steps=(sm_input, *pm_inputs, sm_writer, *pm_writers))
    frontier = (sm_writer.step_id, *(step.step_id for step in pm_writers))
    return plan, frontier, sm_writer, pm_writers


@pytest.mark.parametrize(
    ("k", "full_shape", "shard_shape", "gather_dim"),
    [
        (3, (2, 9, 4), (2, 3, 4), 1),
        (4, (1, 8, 4, 8), (1, 2, 4, 8), 1),
    ],
)
def test_sharded_contiguous_matcher_is_dynamic_and_preserves_ordered_shapes(
    k, full_shape, shard_shape, gather_dim
):
    plan, frontier, sm_writer, pm_writers = _contiguous_fixture(
        k, full_shape=full_shape, shard_shape=shard_shape
    )

    certs, frontiers, layouts = rc.advance_k_rank_contiguous_relation_frontiers(
        plan, (frontier,), ("sharded",)
    )

    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "contiguous-sharded-k-rank"
    assert cert.rank_count == k
    assert cert.gather_dim == gather_dim
    assert cert.full_shape == full_shape
    assert cert.shard_shape == shard_shape
    assert cert.sm_step_id == sm_writer.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_writers)
    assert cert.input_fact == rc.RelationFactSpec(
        "sharded",
        ("sm:9:0", *(f"pm:{19 + rank}:0" for rank in range(k))),
        gather_dim=gather_dim,
    )
    assert cert.output_fact == rc.RelationFactSpec(
        "sharded", frontier, gather_dim=gather_dim
    )
    assert frontiers == (cert.input_fact.step_triple,)
    assert layouts == ("sharded",)


def test_sharded_contiguous_normalization_reaches_fixed_point_and_transition_is_exact_1xk():
    plan0, frontier0, sm0, pm0 = _contiguous_fixture(3)
    sm1 = SimpleNamespace(**{**sm0.__dict__, "step_id": "sm:11:0", "node_index": 11,
                             "input_bindings": (sm0.step_id,)})
    pm1 = tuple(
        SimpleNamespace(**{**step.__dict__, "step_id": f"pm:{40 + rank}:0",
                           "node_index": 40 + rank,
                           "input_bindings": (pm0[rank].step_id,)})
        for rank, step in enumerate(pm0)
    )
    plan = SimpleNamespace(steps=(*plan0.steps, sm1, *pm1))
    sink = []

    frontiers, layouts = rc.normalize_relation_frontiers(
        plan,
        ((sm1.step_id, *(step.step_id for step in pm1)),),
        ("sharded",),
        rules=("contiguous_k",),
        certificate_sink=sink,
    )

    assert frontiers == (("sm:9:0", "pm:19:0", "pm:20:0", "pm:21:0"),)
    assert layouts == ("sharded",)
    assert len(sink) == 2
    transitions = rc.build_certificate_transition_specs(plan, tuple(sink))
    assert {(item.sm_node_indices, item.pm_node_indices) for item in transitions} == {
        ((10,), (30, 31, 32)),
        ((11,), (40, 41, 42)),
    }
    assert all(item.pre_facts == (cert.input_fact,) for item, cert in zip(transitions, sink))
    assert all(item.post_facts == (cert.output_fact,) for item, cert in zip(transitions, sink))


@pytest.mark.parametrize(
    ("target", "mutation", "message"),
    [
        ("pm", {"parameters": (1,)}, "no parameters"),
        ("pm", {"input_bindings": ("pm:19:0", "pm:18:0")}, "input arity"),
        ("pm", {"input_shapes": ((2, 4, 3),)}, "declared input shape"),
        ("pm", {"output_shape": (2, 4, 3)}, "shape preserving"),
        ("sm", {"output_shape": (2, 8, 4)}, "shape preserving"),
    ],
)
def test_sharded_contiguous_matcher_fails_closed_on_inexact_authority(target, mutation, message):
    plan, frontier, sm_writer, pm_writers = _contiguous_fixture(3)
    if target == "sm":
        bad_sm = SimpleNamespace(**{**sm_writer.__dict__, **mutation})
        steps = tuple(bad_sm if step is sm_writer else step for step in plan.steps)
        bad_frontier = (bad_sm.step_id, *frontier[1:])
    else:
        bad_pm = SimpleNamespace(**{**pm_writers[0].__dict__, **mutation})
        steps = tuple(bad_pm if step is pm_writers[0] else step for step in plan.steps)
        bad_frontier = frontier

    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_contiguous_relation_frontiers(
            SimpleNamespace(steps=steps), (bad_frontier,), ("sharded",)
        )


def test_sharded_contiguous_matcher_rejects_reordered_pm_writers():
    plan, frontier, *_ = _contiguous_fixture(3)
    reordered = (frontier[0], frontier[2], frontier[1], frontier[3])
    with pytest.raises(rc.RelationCompositionError, match="ordered ranks"):
        rc.advance_k_rank_contiguous_relation_frontiers(
            plan, (reordered,), ("sharded",)
        )


def _closed_fixture(k=3):
    plan, frontier, sm_step, pm_steps = _contiguous_fixture(k)
    cert = rc.advance_k_rank_contiguous_relation_frontiers(
        plan, (frontier,), ("sharded",)
    )[0][0]
    transition = rc.build_certificate_transition_specs(plan, (cert,))[0]
    input_tids = tuple(200 + rank for rank in range(k))
    output_tids = tuple(300 + rank for rank in range(k))
    input_fact = replace(
        cert.input_fact,
        step_triple=("init:100", *(f"init:{tid}" for tid in input_tids)),
    )
    output_fact = replace(
        cert.output_fact,
        step_triple=("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))),
    )
    cert = replace(
        cert, input_fact=input_fact, output_fact=output_fact,
        sm_step_id="sm:0:0",
        pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
    )
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    pre = rc.ClosedRelationFactRecord(
        fact_id="fact_in", source=input_fact, kind="sharded", sm_tid=100,
        pm_tids=input_tids, metadata_tid=None, metadata_region_id=None,
        full_shape=cert.full_shape, shard_shape=cert.shard_shape,
        row_shard_shape=None, gather_dim=cert.gather_dim,
    )
    post = rc.ClosedRelationFactRecord(
        fact_id="fact_out", source=output_fact, kind="sharded", sm_tid=110,
        pm_tids=output_tids, metadata_tid=None, metadata_region_id=None,
        full_shape=cert.full_shape, shard_shape=cert.shard_shape,
        row_shard_shape=None, gather_dim=cert.gather_dim,
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=(pre.fact_id,))
    after = SimpleNamespace(state_id="state_post", fact_ids=(post.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(pre, post), authority_facts=(),
        states=(before, after), segments=(segment,),
    )
    sm_node = Node(0, "FW_contiguous", [100], [110], [])
    pm_nodes = [Node(rank, "FW_contiguous", [input_tids[rank]], [output_tids[rank]], [])
                for rank in range(k)]
    ir = SimpleNamespace(
        sm_nodes=[sm_node], pm_nodes=pm_nodes,
        sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticContiguous.gSM", pm_graph_ref="SyntheticContiguous.gPM",
    )
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain,
    )
    return ir, relation, segment, pre, post


def test_closed_sharded_contiguous_renderer_replays_exact_ordered_writers():
    ir, relation, segment, pre, post = _closed_fixture(k=3)

    source = composer.render_closed_segment(ir, relation, segment.segment_id)

    assert source == composer.render_closed_k_rank_contiguous_segment(
        ir, relation, segment.segment_id
    )
    assert source.count('op := "OpName.FW_contiguous"') == 2 * 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_contiguous_out") == 4
    assert "ShardedRel.fw_contiguous" in source
    assert f"[pmStore {pre.pm_tids[0]}, pmStore {pre.pm_tids[1]}, pmStore {pre.pm_tids[2]}]" in source
    assert f"[pmFinal {post.pm_tids[0]}, pmFinal {post.pm_tids[1]}, pmFinal {post.pm_tids[2]}]" in source
    assert "rankCount = 3" not in source


def test_closed_sharded_contiguous_renderer_rejects_tampered_live_writer():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    ir.pm_nodes[1].params = [7]
    with pytest.raises(ValueError, match="no parameters"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticContiguous
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_contiguous", ins := [200], outs := [300] }}, {{ rank := 1, op := "OpName.FW_contiguous", ins := [201], outs := [301] }}, {{ rank := 2, op := "OpName.FW_contiguous", ins := [202], outs := [302] }}] }}

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 4] [2, 3, 4]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 4] [2, 3, 4]
def state_pre : RelationState where
  facts := [fact_in]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticContiguous
end TrainVerify.Denote
'''


def test_generated_sharded_contiguous_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    source = _witness_source(rendered)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedShardedContiguousWitness.lean"

    assert witness.read_text(encoding="utf-8") == source
    assert "sorry" not in source
    assert "set_option maxHeartbeats 500000" in source
    assert "#print axioms segment_000000" in source
