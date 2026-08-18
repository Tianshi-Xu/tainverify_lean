from pathlib import Path
from dataclasses import replace
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


def _step(step_id, *, side, node_index, rank, op, inputs=(), input_shapes=(), shape=(), params=()):
    return SimpleNamespace(
        step_id=step_id,
        side=side,
        node_index=node_index,
        rank=rank,
        op=op,
        input_bindings=tuple(inputs),
        input_shapes=tuple(input_shapes),
        output_shape=tuple(shape),
        parameters=tuple(params),
    )


def _matcher_fixture(k=4):
    b, local_h, q, inner, m = 1, 3, 5, 7, 11
    x_full = (b, local_h * k, q, inner)
    x_shard = (b, local_h, q, inner)
    y_full = (b, local_h * k, inner, m)
    y_shard = (b, local_h, inner, m)
    out_full = (b, local_h * k, q, m)
    out_shard = (b, local_h, q, m)
    sm_x = _step("sm:1:0", side="sm", node_index=1, rank=0, op="Source", shape=x_full)
    sm_y = _step("sm:2:0", side="sm", node_index=2, rank=0, op="Source", shape=y_full)
    pm_xs = tuple(_step(f"pm:{10+r}:0", side="pm", node_index=10+r, rank=r,
                        op="Source", shape=x_shard) for r in range(k))
    pm_ys = tuple(_step(f"pm:{20+r}:0", side="pm", node_index=20+r, rank=r,
                        op="Source", shape=y_shard) for r in range(k))
    sm_matmul = _step(
        "sm:30:0", side="sm", node_index=30, rank=0, op="FW_matmul",
        inputs=(sm_x.step_id, sm_y.step_id), input_shapes=(x_full, y_full), shape=out_full,
    )
    pm_matmuls = tuple(_step(
        f"pm:{40+r}:0", side="pm", node_index=40+r, rank=r, op="FW_matmul",
        inputs=(pm_xs[r].step_id, pm_ys[r].step_id),
        input_shapes=(x_shard, y_shard), shape=out_shard,
    ) for r in range(k))
    plan = SimpleNamespace(steps=(sm_x, sm_y, *pm_xs, *pm_ys, sm_matmul, *pm_matmuls))
    frontier = (sm_matmul.step_id, *(step.step_id for step in pm_matmuls))
    return plan, frontier, (sm_x, sm_y, pm_xs, pm_ys, sm_matmul, pm_matmuls)


def test_head_axis_matcher_derives_two_ordered_dim1_sharded_inputs_dynamic_k():
    plan, frontier, parts = _matcher_fixture(k=4)
    sm_x, sm_y, pm_xs, pm_ys, sm_matmul, pm_matmuls = parts
    certs, frontiers, layouts = rc.advance_k_rank_matmul_head_axis_frontiers(
        plan, (frontier,), ("sharded",)
    )
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "matmul-head-axis-sharded-k-rank-dim1"
    assert cert.rank_count == 4
    assert cert.first_operand_fact == rc.RelationFactSpec(
        "sharded", (sm_x.step_id, *(step.step_id for step in pm_xs)), gather_dim=1
    )
    assert cert.second_operand_fact == rc.RelationFactSpec(
        "sharded", (sm_y.step_id, *(step.step_id for step in pm_ys)), gather_dim=1
    )
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=1)
    assert cert.sm_step_id == sm_matmul.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_matmuls)
    assert frontiers == (cert.first_operand_fact.step_triple, cert.second_operand_fact.step_triple)
    assert layouts == ("sharded", "sharded")


@pytest.mark.parametrize(
    ("target", "mutation", "message"),
    [
        ("pm_writer", {"rank": 9}, "ordered ranks"),
        ("pm_writer", {"parameters": (1,)}, "no parameters"),
        ("pm_writer", {"input_bindings": ("pm:11:0",)}, "input arity"),
        ("pm_writer", {"input_shapes": ((1, 3, 5, 7),)}, "input shapes"),
        ("pm_writer", {"output_shape": (1, 3, 5)}, "rank-4"),
        ("pm_x", {"output_shape": (1, 3, 5, 8)}, "shard shapes"),
        ("pm_y", {"output_shape": (1, 3, 8, 11)}, "shard shapes"),
        ("sm_x", {"output_shape": (1, 11, 5, 7)}, "symbolic rank-4"),
        ("sm_y", {"output_shape": (1, 12, 8, 11)}, "symbolic rank-4"),
        ("sm_writer", {"output_shape": (1, 12, 5, 12)}, "symbolic rank-4"),
    ],
)
def test_head_axis_matcher_fails_closed_on_arity_params_rank_and_symbolic_shapes(target, mutation, message):
    plan, frontier, parts = _matcher_fixture(k=4)
    sm_x, sm_y, pm_xs, pm_ys, sm_writer, pm_writers = parts
    victim = {
        "pm_writer": pm_writers[1], "pm_x": pm_xs[1], "pm_y": pm_ys[1],
        "sm_x": sm_x, "sm_y": sm_y, "sm_writer": sm_writer,
    }[target]
    replacement = SimpleNamespace(**{**victim.__dict__, **mutation})
    steps = tuple(replacement if step is victim else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_matmul_head_axis_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",)
        )


def test_head_axis_matcher_rejects_non_rankwise_zip_pairing():
    plan, frontier, parts = _matcher_fixture(k=4)
    *_, pm_writers = parts
    bad = SimpleNamespace(**{
        **pm_writers[1].__dict__,
        "input_bindings": (pm_writers[2].input_bindings[0], pm_writers[1].input_bindings[1]),
    })
    steps = tuple(bad if step is pm_writers[1] else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match="first-operand shards.*ordered ranks"):
        rc.advance_k_rank_matmul_head_axis_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",)
        )


def test_head_axis_fixed_point_and_transition_own_exact_one_sm_plus_k_pm_writers():
    plan, frontier, _ = _matcher_fixture(k=3)
    sink = []
    frontiers, layouts = rc.normalize_relation_frontiers(
        plan, (frontier,), ("sharded",), rules=("matmul_head_axis_k",),
        certificate_sink=sink,
    )
    assert layouts == ("sharded", "sharded")
    assert len(sink) == 1
    cert = sink[0]
    assert frontiers == (cert.first_operand_fact.step_triple, cert.second_operand_fact.step_triple)
    transition = rc.build_certificate_transition_specs(plan, tuple(sink))[0]
    assert transition.pre_facts == tuple(sorted((cert.first_operand_fact, cert.second_operand_fact)))
    assert transition.post_facts == (cert.output_fact,)
    assert transition.sm_node_indices == (30,)
    assert transition.pm_node_indices == (40, 41, 42)
    assert transition.lean_theorem.endswith("ShardedRel.fw_matmul_head_axis_rank4")



def _closed_fixture(k=3):
    plan, frontier, _ = _matcher_fixture(k)
    cert = rc.advance_k_rank_matmul_head_axis_frontiers(plan, (frontier,), ("sharded",))[0][0]
    x_sm_tid, y_sm_tid = 100, 101
    x_pm_tids = tuple(200 + rank for rank in range(k))
    y_pm_tids = tuple(210 + rank for rank in range(k))
    out_sm_tid = 110
    out_pm_tids = tuple(300 + rank for rank in range(k))
    first_fact = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{tid}" for tid in x_pm_tids)), gather_dim=1)
    second_fact = rc.RelationFactSpec("sharded", ("init:101", *(f"init:{tid}" for tid in y_pm_tids)), gather_dim=1)
    output_fact = rc.RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))), gather_dim=1)
    cert = replace(cert, first_operand_fact=first_fact, second_operand_fact=second_fact,
                   output_fact=output_fact, sm_step_id="sm:0:0",
                   pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)))
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    first = rc.ClosedRelationFactRecord("fact_x", first_fact, "sharded", x_sm_tid, x_pm_tids, None, None,
        cert.first_operand_full_shape, cert.first_operand_shard_shape, 1)
    second = rc.ClosedRelationFactRecord("fact_y", second_fact, "sharded", y_sm_tid, y_pm_tids, None, None,
        cert.second_operand_full_shape, cert.second_operand_shard_shape, 1)
    output = rc.ClosedRelationFactRecord("fact_out", output_fact, "sharded", out_sm_tid, out_pm_tids, None, None,
        cert.output_full_shape, cert.output_shard_shape, 1)
    before = SimpleNamespace(state_id="state_pre", fact_ids=(first.fact_id, second.fact_id))
    after = SimpleNamespace(state_id="state_post", fact_ids=(output.fact_id,))
    segment = SimpleNamespace(segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k), pre_state_id=before.state_id, post_state_id=after.state_id)
    chain = SimpleNamespace(complete=True, relation_facts=(first, second, output), authority_facts=(),
        states=(before, after), segments=(segment,))
    sm_node = Node(0, "FW_matmul", [x_sm_tid, y_sm_tid], [out_sm_tid], [])
    pm_nodes = [Node(rank, "FW_matmul", [x_pm_tids[rank], y_pm_tids[rank]], [out_pm_tids[rank]], [])
                for rank in range(k)]
    ir = SimpleNamespace(sm_nodes=[sm_node], pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticHeadMatmul.gSM", pm_graph_ref="SyntheticHeadMatmul.gPM")
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment, first, second, output


def test_closed_head_axis_renderer_replays_exact_ordered_zip_writers_and_theorem():
    ir, relation, segment, first, second, output = _closed_fixture(k=3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count('op := "OpName.FW_matmul"') == 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_matmul_out") == 4
    assert "ShardedRel.fw_matmul_head_axis_rank4" in source
    assert ", ".join(f"pmStore {tid}" for tid in first.pm_tids) in source
    assert ", ".join(f"pmStore {tid}" for tid in second.pm_tids) in source
    assert ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) in source
    assert "rankCount = 3" not in source


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 7}, "ordered ranks"), ({"params": [9]}, "no parameters"),
    ({"ins": [201]}, "binary"), ({"ins": [999, 211]}, "first operands"),
    ({"ins": [201, 999]}, "second operands"),
])
def test_closed_head_axis_renderer_rejects_tampered_live_writer(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.KRankMatmulHeadAxis

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticHeadMatmul
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [100, 101], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [200, 210], outs := [300] }}, {{ rank := 1, op := "OpName.FW_matmul", ins := [201, 211], outs := [301] }}, {{ rank := 2, op := "OpName.FW_matmul", ins := [202, 212], outs := [302] }}] }}

def fact_x : RelationFact := .sharded 100 [200, 201, 202] 1 [1, 9, 5, 7] [1, 3, 5, 7]
def fact_y : RelationFact := .sharded 101 [210, 211, 212] 1 [1, 9, 7, 11] [1, 3, 7, 11]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [1, 9, 5, 11] [1, 3, 5, 11]
def state_pre : RelationState where
  facts := [fact_x, fact_y]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticHeadMatmul
end TrainVerify.Denote
'''


def test_generated_head_axis_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    source = _witness_source(rendered)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankMatmulHeadAxisWitness.lean"
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert source.startswith("import denote.KRankMatmulHeadAxis")
    assert "sorry" not in source
    assert "#print axioms segment_000000" in source
