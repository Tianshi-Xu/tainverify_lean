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
    b, h, q, local_k, m = 2, 4, 5, 7, 11
    x_full = (b, h, q, local_k * k)
    x_shard = (b, h, q, local_k)
    y_full = (b, h, local_k * k, m)
    y_shard = (b, h, local_k, m)
    output_shape = (b, h, q, m)
    sm_x = _step("sm:1:0", side="sm", node_index=1, rank=0, op="Source", shape=x_full)
    pm_xs = tuple(
        _step(f"pm:{8 + rank}:0", side="pm", node_index=8 + rank, rank=rank,
              op="Source", shape=x_shard)
        for rank in range(k)
    )
    sm_y = _step("sm:2:0", side="sm", node_index=2, rank=0, op="Source", shape=y_full)
    pm_ys = tuple(
        _step(f"pm:{18 + rank}:0", side="pm", node_index=18 + rank, rank=rank,
              op="Source", shape=y_shard)
        for rank in range(k)
    )
    sm_matmul = _step(
        "sm:30:0", side="sm", node_index=30, rank=0, op="FW_matmul",
        inputs=(sm_x.step_id, sm_y.step_id), input_shapes=(x_full, y_full),
        shape=output_shape,
    )
    pm_matmuls = tuple(
        _step(
            f"pm:{40 + rank}:0", side="pm", node_index=40 + rank, rank=rank,
            op="FW_matmul", inputs=(pm_xs[rank].step_id, pm_ys[rank].step_id),
            input_shapes=(x_shard, y_shard), shape=output_shape,
        )
        for rank in range(k)
    )
    plan = SimpleNamespace(steps=(sm_x, *pm_xs, sm_y, *pm_ys, sm_matmul, *pm_matmuls))
    frontier = (sm_matmul.step_id, *(step.step_id for step in pm_matmuls))
    return plan, frontier, (sm_x, pm_xs, sm_y, pm_ys, sm_matmul, pm_matmuls)


def test_contraction_matmul_matcher_emits_reduction_and_ordered_dim3_dim2_inputs():
    plan, frontier, parts = _matcher_fixture(k=3)
    sm_x, pm_xs, sm_y, pm_ys, sm_matmul, pm_matmuls = parts
    certs, frontiers, layouts = rc.advance_k_rank_matmul_contraction_frontiers(
        plan, (frontier,), ("reduction",)
    )
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "matmul-contraction-reduction-k-rank"
    assert cert.rank_count == 3
    assert cert.first_operand_fact == rc.RelationFactSpec(
        "sharded", (sm_x.step_id, *(step.step_id for step in pm_xs)), gather_dim=3
    )
    assert cert.second_operand_fact == rc.RelationFactSpec(
        "sharded", (sm_y.step_id, *(step.step_id for step in pm_ys)), gather_dim=2
    )
    assert cert.output_fact == rc.RelationFactSpec("reduction", frontier)
    assert cert.sm_step_id == sm_matmul.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_matmuls)
    assert frontiers == (cert.first_operand_fact.step_triple, cert.second_operand_fact.step_triple)
    assert layouts == ("sharded", "sharded")


@pytest.mark.parametrize(
    ("target", "mutation", "message"),
    [
        ("pm_writer", {"rank": 2}, "ordered ranks"),
        ("pm_writer", {"parameters": (1,)}, "no parameters"),
        ("pm_writer", {"input_bindings": ("pm:9:0",)}, "input arity"),
        ("pm_writer", {"input_shapes": ((2, 4, 5, 7),)}, "input shapes"),
        ("pm_writer", {"output_shape": (2, 4, 5, 10)}, "output shape"),
        ("pm_x", {"output_shape": (2, 4, 5, 8)}, "first operand"),
        ("pm_y", {"output_shape": (2, 4, 8, 11)}, "second operand"),
    ],
)
def test_contraction_matmul_matcher_fails_closed_on_rank_arity_params_and_shapes(target, mutation, message):
    plan, frontier, parts = _matcher_fixture(k=3)
    _sm_x, pm_xs, _sm_y, pm_ys, _sm_matmul, pm_matmuls = parts
    victim = {"pm_writer": pm_matmuls[1], "pm_x": pm_xs[1], "pm_y": pm_ys[1]}[target]
    replacement = SimpleNamespace(**{**victim.__dict__, **mutation})
    steps = tuple(replacement if step is victim else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_matmul_contraction_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("reduction",)
        )


def test_contraction_matmul_matcher_requires_exact_rankwise_zip_pairing():
    plan, frontier, parts = _matcher_fixture(k=3)
    _sm_x, pm_xs, _sm_y, pm_ys, _sm_matmul, pm_matmuls = parts
    bad = SimpleNamespace(**{
        **pm_matmuls[1].__dict__,
        "input_bindings": (pm_xs[2].step_id, pm_ys[1].step_id),
    })
    steps = tuple(bad if step is pm_matmuls[1] else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match="rank-wise zip"):
        rc.advance_k_rank_matmul_contraction_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("reduction",)
        )


def test_contraction_matmul_fixed_point_and_transition_own_exact_one_plus_k_writers():
    plan, frontier, _ = _matcher_fixture(k=4)
    sink = []
    frontiers, layouts = rc.normalize_relation_frontiers(
        plan, (frontier,), ("reduction",), rules=("matmul_contraction_k",),
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
    assert transition.pm_node_indices == (40, 41, 42, 43)
    assert transition.lean_theorem.endswith("ShardedRel.fw_matmul_contraction_axis_rank4")


def _closed_fixture(k=3):
    plan, frontier, _ = _matcher_fixture(k)
    cert = rc.advance_k_rank_matmul_contraction_frontiers(
        plan, (frontier,), ("reduction",)
    )[0][0]
    x_sm, y_sm, out_sm = 100, 101, 110
    x_pms = tuple(200 + rank for rank in range(k))
    y_pms = tuple(210 + rank for rank in range(k))
    out_pms = tuple(300 + rank for rank in range(k))
    x_fact = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{x}" for x in x_pms)), gather_dim=3)
    y_fact = rc.RelationFactSpec("sharded", ("init:101", *(f"init:{y}" for y in y_pms)), gather_dim=2)
    out_fact = rc.RelationFactSpec("reduction", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))))
    cert = replace(cert, first_operand_fact=x_fact, second_operand_fact=y_fact,
                   output_fact=out_fact, sm_step_id="sm:0:0",
                   pm_step_ids=tuple(f"pm:{r}:0" for r in range(k)))
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    x = rc.ClosedRelationFactRecord("fact_x", x_fact, "sharded", x_sm, x_pms, None, None,
                                    cert.first_operand_full_shape, cert.first_operand_shard_shape, 3)
    y = rc.ClosedRelationFactRecord("fact_y", y_fact, "sharded", y_sm, y_pms, None, None,
                                    cert.second_operand_full_shape, cert.second_operand_shard_shape, 2)
    out = rc.ClosedRelationFactRecord("fact_out", out_fact, "reduction", out_sm, out_pms, None, None,
                                      cert.output_shape, cert.output_shape, None)
    before = SimpleNamespace(state_id="state_pre", fact_ids=(x.fact_id, y.fact_id))
    after = SimpleNamespace(state_id="state_post", fact_ids=(out.fact_id,))
    segment = SimpleNamespace(segment_id="segment_000000", transition_ids=(transition.transition_id,),
                              sm_range=(0, 1), pm_range=(0, k),
                              pre_state_id=before.state_id, post_state_id=after.state_id)
    chain = SimpleNamespace(complete=True, relation_facts=(x, y, out), authority_facts=(),
                            states=(before, after), segments=(segment,))
    sm_node = Node(0, "FW_matmul", [x_sm, y_sm], [out_sm], [])
    pm_nodes = [Node(r, "FW_matmul", [x_pms[r], y_pms[r]], [out_pms[r]], []) for r in range(k)]
    ir = SimpleNamespace(sm_nodes=[sm_node], pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
                         sm_graph_ref="SyntheticContraction.gSM", pm_graph_ref="SyntheticContraction.gPM")
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment, x, y, out


def test_closed_contraction_renderer_replays_exact_ordered_zip_and_import_boundary():
    ir, relation, segment, x, y, out = _closed_fixture(k=3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_matmul_out") == 4
    assert "ShardedRel.fw_matmul_contraction_axis_rank4" in source
    assert "List.zipWith fw_matmul" in source
    for x_tid, y_tid, out_tid in zip(x.pm_tids, y.pm_tids, out.pm_tids):
        assert f"fw_matmul (pmStore {x_tid}) (pmStore {y_tid})" in source
        assert f"pmFinal {out_tid}" in source
    family = ("matmul-contraction-reduction-k-rank",)
    assert composer._closed_segment_family_imports(family) == ("denote.KRankMatmulContractionReduction",)


def test_closed_contraction_renderer_ignores_unrelated_same_family_certificate():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    certificate = relation.certificates[0]
    unrelated = replace(
        certificate,
        output_fact=rc.RelationFactSpec(
            "reduction", ("sm:99:0", "pm:99:0", "pm:100:0", "pm:101:0")
        ),
    )
    relation.certificates = (unrelated, certificate)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert "ShardedRel.fw_matmul_contraction_axis_rank4" in source


@pytest.mark.parametrize(
    "certificates",
    [
        lambda cert: (cert, cert),
        lambda cert: (replace(cert, lean_theorem="Tampered.theorem"),),
        lambda cert: (replace(
            cert,
            first_operand_fact=cert.second_operand_fact,
            second_operand_fact=cert.first_operand_fact,
        ),),
    ],
    ids=("duplicate", "tampered-theorem", "swapped-operand-roles"),
)
def test_closed_contraction_renderer_rejects_non_unique_or_tampered_exact_certificate(certificates):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    relation.certificates = certificates(relation.certificates[0])
    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ({"rank": 7}, "ordered ranks"),
        ({"params": [9]}, "no parameters"),
        ({"ins": [201]}, "binary"),
        ({"ins": [202, 211]}, "rank-wise zip"),
        ({"outs": []}, "singleton-output"),
    ],
)
def test_closed_contraction_renderer_rejects_tampered_writer(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.KRankMatmulContractionReduction

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticContraction
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [100, 101], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [200, 210], outs := [300] }}, {{ rank := 1, op := "OpName.FW_matmul", ins := [201, 211], outs := [301] }}, {{ rank := 2, op := "OpName.FW_matmul", ins := [202, 212], outs := [302] }}] }}

def fact_x : RelationFact := .sharded 100 [200, 201, 202] 3 [2, 4, 5, 21] [2, 4, 5, 7]
def fact_y : RelationFact := .sharded 101 [210, 211, 212] 2 [2, 4, 21, 11] [2, 4, 7, 11]
def fact_out : RelationFact := .reduction 110 [300, 301, 302] [2, 4, 5, 11]
def state_pre : RelationState where
  facts := [fact_x, fact_y]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticContraction
end TrainVerify.Denote
'''


def test_generated_contraction_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    source = _witness_source(rendered)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankMatmulContractionWitness.lean"
    assert witness.read_text(encoding="utf-8") == source
    assert source.startswith("import denote.KRankMatmulContractionReduction")
    assert "sorry" not in source
    assert "#print axioms segment_000000" in source
