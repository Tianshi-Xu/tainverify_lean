from dataclasses import replace
from pathlib import Path
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


def _matcher_fixture(k=3):
    b, h, q, inner, local_m = 2, 4, 5, 7, 11
    x_shape = (b, h, q, inner)
    y_full_shape = (b, h, inner, local_m * k)
    y_shard_shape = (b, h, inner, local_m)
    out_full_shape = (b, h, q, local_m * k)
    out_shard_shape = (b, h, q, local_m)
    sm_x = _step("sm:1:0", side="sm", node_index=1, rank=0, op="Source", shape=x_shape)
    pm_x = _step("pm:8:0", side="pm", node_index=8, rank=0, op="Source", shape=x_shape)
    sm_y = _step("sm:2:0", side="sm", node_index=2, rank=0, op="Source", shape=y_full_shape)
    pm_ys = tuple(
        _step(f"pm:{9 + rank}:0", side="pm", node_index=9 + rank, rank=rank,
              op="Source", shape=y_shard_shape)
        for rank in range(k)
    )
    sm_matmul = _step(
        "sm:20:0", side="sm", node_index=20, rank=0, op="FW_matmul",
        inputs=(sm_x.step_id, sm_y.step_id), input_shapes=(x_shape, y_full_shape),
        shape=out_full_shape,
    )
    pm_matmuls = tuple(
        _step(
            f"pm:{30 + rank}:0", side="pm", node_index=30 + rank, rank=rank,
            op="FW_matmul", inputs=(pm_x.step_id, pm_ys[rank].step_id),
            input_shapes=(x_shape, y_shard_shape), shape=out_shard_shape,
        )
        for rank in range(k)
    )
    plan = SimpleNamespace(steps=(sm_x, pm_x, sm_y, *pm_ys, sm_matmul, *pm_matmuls))
    frontier = (sm_matmul.step_id, *(step.step_id for step in pm_matmuls))
    return plan, frontier, (sm_x, pm_x, sm_y, pm_ys, sm_matmul, pm_matmuls)


def test_output_axis_matmul_matcher_is_dynamic_and_preserves_both_ordered_upstream_facts():
    plan, frontier, parts = _matcher_fixture(k=3)
    sm_x, pm_x, sm_y, pm_ys, sm_matmul, pm_matmuls = parts

    certs, frontiers, layouts = rc.advance_k_rank_matmul_output_axis_frontiers(
        plan, (frontier,), ("sharded",)
    )

    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "matmul-output-axis-sharded-k-rank-dim3"
    assert cert.rank_count == 3
    assert cert.output_gather_dim == 3
    assert cert.first_operand_fact == rc.RelationFactSpec(
        "joined", (sm_x.step_id, pm_x.step_id)
    )
    assert cert.second_operand_fact == rc.RelationFactSpec(
        "sharded", (sm_y.step_id, *(step.step_id for step in pm_ys)), gather_dim=3
    )
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=3)
    assert cert.sm_step_id == sm_matmul.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_matmuls)
    assert frontiers == (
        cert.first_operand_fact.step_triple,
        cert.second_operand_fact.step_triple,
    )
    assert layouts == ("joined", "sharded")


@pytest.mark.parametrize(
    ("target", "mutation", "message"),
    [
        ("pm_writer", {"rank": 2}, "ordered ranks"),
        ("pm_writer", {"parameters": (1,)}, "no parameters"),
        ("pm_writer", {"input_bindings": ("pm:8:0",)}, "input arity"),
        ("pm_writer", {"input_shapes": ((2, 4, 5, 7),)}, "input shapes"),
        ("pm_writer", {"output_shape": (2, 4, 5, 10)}, "output"),
        ("pm_x", {"output_shape": (2, 4, 5)}, "joined rank-4"),
        ("pm_y", {"output_shape": (2, 4, 7, 10)}, "second operand"),
    ],
)
def test_output_axis_matmul_matcher_fails_closed_on_inexact_authority(target, mutation, message):
    plan, frontier, parts = _matcher_fixture(k=3)
    _sm_x, pm_x, _sm_y, pm_ys, _sm_matmul, pm_matmuls = parts
    victim = {"pm_writer": pm_matmuls[1], "pm_x": pm_x, "pm_y": pm_ys[1]}[target]
    replacement = SimpleNamespace(**{**victim.__dict__, **mutation})
    steps = tuple(replacement if step is victim else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_matmul_output_axis_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",)
        )


def test_output_axis_matmul_matcher_rejects_nonshared_first_operand_and_reordered_second_operand():
    plan, frontier, parts = _matcher_fixture(k=3)
    _sm_x, pm_x, _sm_y, pm_ys, _sm_matmul, pm_matmuls = parts
    other_x = SimpleNamespace(**{**pm_x.__dict__, "step_id": "pm:7:0", "node_index": 7})
    bad_writer = SimpleNamespace(**{
        **pm_matmuls[1].__dict__,
        "input_bindings": (other_x.step_id, pm_matmuls[1].input_bindings[1]),
    })
    certs, unchanged, layouts = rc.advance_k_rank_matmul_output_axis_frontiers(
        SimpleNamespace(steps=(*plan.steps, other_x, bad_writer)), (frontier,), ("sharded",)
    )
    assert certs == ()
    assert unchanged == (frontier,)
    assert layouts == ("sharded",)

    swapped = (frontier[0], frontier[2], frontier[1], frontier[3])
    with pytest.raises(rc.RelationCompositionError, match="ordered ranks"):
        rc.advance_k_rank_matmul_output_axis_frontiers(plan, (swapped,), ("sharded",))


def test_output_axis_matmul_fixed_point_and_transition_own_exact_one_plus_k_writers():
    plan, frontier, _parts = _matcher_fixture(k=4)
    sink = []
    frontiers, layouts = rc.normalize_relation_frontiers(
        plan, (frontier,), ("sharded",),
        rules=("matmul_output_axis_k",), certificate_sink=sink,
    )
    assert layouts == ("joined", "sharded")
    assert len(sink) == 1
    cert = sink[0]
    assert frontiers == (cert.first_operand_fact.step_triple, cert.second_operand_fact.step_triple)
    transition = rc.build_certificate_transition_specs(plan, tuple(sink))[0]
    assert transition.pre_facts == tuple(sorted((cert.first_operand_fact, cert.second_operand_fact)))
    assert transition.post_facts == (cert.output_fact,)
    assert transition.sm_node_indices == (20,)
    assert transition.pm_node_indices == (30, 31, 32, 33)
    assert transition.lean_theorem.endswith("ShardedRel.fw_matmul_output_axis_rank4")



def _closed_fixture(k=3):
    plan, frontier, _parts = _matcher_fixture(k)
    cert = rc.advance_k_rank_matmul_output_axis_frontiers(
        plan, (frontier,), ("sharded",)
    )[0][0]
    x_sm_tid, x_pm_tid = 100, 200
    y_sm_tid = 101
    y_pm_tids = tuple(201 + rank for rank in range(k))
    out_sm_tid = 110
    out_pm_tids = tuple(301 + rank for rank in range(k))
    first_fact = rc.RelationFactSpec("joined", ("init:100", "init:200"))
    second_fact = rc.RelationFactSpec(
        "sharded", ("init:101", *(f"init:{tid}" for tid in y_pm_tids)), gather_dim=3
    )
    output_fact = rc.RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))), gather_dim=3
    )
    cert = replace(
        cert, first_operand_fact=first_fact, second_operand_fact=second_fact,
        output_fact=output_fact, sm_step_id="sm:0:0",
        pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
    )
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    first = rc.ClosedRelationFactRecord(
        "fact_x", first_fact, "joined", x_sm_tid, (x_pm_tid,), None, None,
        cert.first_operand_shape, cert.first_operand_shape, None,
    )
    second = rc.ClosedRelationFactRecord(
        "fact_y", second_fact, "sharded", y_sm_tid, y_pm_tids, None, None,
        cert.second_operand_full_shape, cert.second_operand_shard_shape, 3,
    )
    output = rc.ClosedRelationFactRecord(
        "fact_out", output_fact, "sharded", out_sm_tid, out_pm_tids, None, None,
        cert.output_full_shape, cert.output_shard_shape, 3,
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=(first.fact_id, second.fact_id))
    after = SimpleNamespace(state_id="state_post", fact_ids=(output.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(first, second, output), authority_facts=(),
        states=(before, after), segments=(segment,),
    )
    sm_node = Node(0, "FW_matmul", [x_sm_tid, y_sm_tid], [out_sm_tid], [])
    pm_nodes = [
        Node(rank, "FW_matmul", [x_pm_tid, y_pm_tids[rank]], [out_pm_tids[rank]], [])
        for rank in range(k)
    ]
    ir = SimpleNamespace(
        sm_nodes=[sm_node], pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticMatmul.gSM", pm_graph_ref="SyntheticMatmul.gPM",
    )
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain,
    )
    return ir, relation, segment, first, second, output


def test_closed_output_axis_matmul_renderer_replays_exact_ordered_writers_and_theorem():
    ir, relation, segment, first, second, output = _closed_fixture(k=3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count('op := "OpName.FW_matmul"') == 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_matmul_out") == 4
    assert "ShardedRel.fw_matmul_output_axis_rank4" in source
    assert f"pmStore {first.pm_tids[0]}" in source
    assert ", ".join(f"pmStore {tid}" for tid in second.pm_tids) in source
    assert ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) in source
    assert "rankCount = 3" not in source


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ({"rank": 7}, "ordered ranks"),
        ({"params": [9]}, "no parameters"),
        ({"ins": [200]}, "binary"),
        ({"ins": [999, 202]}, "first operand"),
    ],
)
def test_closed_output_axis_matmul_renderer_rejects_tampered_live_writer(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.KRankMatmul

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticMatmul
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [100, 101], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [200, 201], outs := [301] }}, {{ rank := 1, op := "OpName.FW_matmul", ins := [200, 202], outs := [302] }}, {{ rank := 2, op := "OpName.FW_matmul", ins := [200, 203], outs := [303] }}] }}

def fact_x : RelationFact := .joined 100 200 [2, 4, 5, 7]
def fact_y : RelationFact := .sharded 101 [201, 202, 203] 3 [2, 4, 7, 33] [2, 4, 7, 11]
def fact_out : RelationFact := .sharded 110 [301, 302, 303] 3 [2, 4, 5, 33] [2, 4, 5, 11]
def state_pre : RelationState where
  facts := [fact_x, fact_y]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticMatmul
end TrainVerify.Denote
'''


def test_generated_output_axis_matmul_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    source = _witness_source(rendered)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankMatmulOutputAxisWitness.lean"
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert source.startswith("import denote.KRankMatmul")
    assert "sorry" not in source
    assert "#print axioms segment_000000" in source
