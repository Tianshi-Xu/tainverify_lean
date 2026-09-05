from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


def _step(step_id, *, side, node_index, rank, op, inputs=(), input_shapes=(), shape=(), params=()):
    return SimpleNamespace(
        step_id=step_id, side=side, node_index=node_index, rank=rank, op=op,
        input_bindings=tuple(inputs), input_shapes=tuple(input_shapes),
        output_shape=tuple(shape), parameters=tuple(params),
    )


def _matcher_fixture(dim, k=3):
    shard = (2, 5, 7, 11)
    full = list(shard)
    full[dim] *= k
    full = tuple(full)
    sm_in = _step("sm:1:0", side="sm", node_index=1, rank=0,
                  op="ArbitraryProducer", shape=full)
    pm_ins = tuple(
        _step(f"pm:{10+r}:0", side="pm", node_index=10+r, rank=r,
              op="DifferentUpstreamFamily", shape=shard)
        for r in range(k)
    )
    sm_out = _step("sm:30:0", side="sm", node_index=30, rank=0,
                   op="FW_softmax", inputs=(sm_in.step_id,),
                   input_shapes=(full,), shape=full)
    pm_outs = tuple(
        _step(f"pm:{40+r}:0", side="pm", node_index=40+r, rank=r,
              op="FW_softmax", inputs=(pm_ins[r].step_id,),
              input_shapes=(shard,), shape=shard)
        for r in range(k)
    )
    plan = SimpleNamespace(steps=(sm_in, *pm_ins, sm_out, *pm_outs))
    frontier = (sm_out.step_id, *(step.step_id for step in pm_outs))
    return plan, frontier, (sm_in, pm_ins, sm_out, pm_outs)


@pytest.mark.parametrize("dim", [1, 2])
def test_softmax_matcher_is_dynamic_k_axis_specific_and_producer_agnostic(dim):
    plan, frontier, parts = _matcher_fixture(dim, 3)
    sm_in, pm_ins, sm_out, pm_outs = parts
    certs, roots, layouts = rc.advance_k_rank_softmax_frontiers(
        plan, (frontier,), ("sharded",))
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == f"softmax-sharded-k-rank-dim{dim}"
    assert cert.rank_count == 3 and cert.gather_dim == dim
    assert cert.input_fact == rc.RelationFactSpec(
        "sharded", (sm_in.step_id, *(step.step_id for step in pm_ins)),
        gather_dim=dim)
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=dim)
    assert cert.sm_step_id == sm_out.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_outs)
    assert cert.lean_theorem.endswith(f"ShardedRel.fw_softmax_dim{dim}_rank4")
    assert roots == (cert.input_fact.step_triple,)
    assert layouts == ("sharded",)


@pytest.mark.parametrize(("target", "mutation", "message"), [
    ("writer", {"rank": 2}, "ordered ranks"),
    ("writer", {"parameters": (3,)}, "no parameters"),
    ("writer", {"input_bindings": ()}, "unary"),
    ("writer", {"input_shapes": ()}, "input shape"),
    ("writer", {"output_shape": (2, 5, 7)}, "rank-4"),
    ("input", {"output_shape": (2, 6, 7, 11)}, "input authority"),
])
def test_softmax_matcher_fails_closed_on_malformed_authority(target, mutation, message):
    plan, frontier, parts = _matcher_fixture(2, 3)
    _sm_in, pm_ins, _sm_out, pm_outs = parts
    victim = pm_outs[1] if target == "writer" else pm_ins[1]
    replacement = SimpleNamespace(**{**victim.__dict__, **mutation})
    steps = tuple(replacement if step is victim else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_softmax_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",))


def test_softmax_matcher_rejects_last_axis_dim3_and_cross_rank_input_reordering():
    plan, frontier, _ = _matcher_fixture(3, 3)
    assert rc.advance_k_rank_softmax_frontiers(
        plan, (frontier,), ("sharded",)) == ((), (frontier,), ("sharded",))

    plan, frontier, parts = _matcher_fixture(1, 3)
    *_, pm_outs = parts
    bad = SimpleNamespace(**{**pm_outs[1].__dict__,
        "input_bindings": (pm_outs[2].input_bindings[0],)})
    steps = tuple(bad if step is pm_outs[1] else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match="ordered input authority"):
        rc.advance_k_rank_softmax_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",))


@pytest.mark.parametrize("dim", [1, 2])
def test_softmax_fixed_point_and_transition_own_exact_one_plus_k_writers(dim):
    plan, frontier, _ = _matcher_fixture(dim, 4)
    sink = []
    roots, layouts = rc.normalize_relation_frontiers(
        plan, (frontier,), ("sharded",), rules=("softmax_k",),
        certificate_sink=sink)
    cert = sink[0]
    assert roots == (cert.input_fact.step_triple,)
    assert layouts == ("sharded",)
    transition = rc.build_certificate_transition_specs(plan, tuple(sink))[0]
    assert transition.pre_facts == (cert.input_fact,)
    assert transition.post_facts == (cert.output_fact,)
    assert transition.sm_node_indices == (30,)
    assert transition.pm_node_indices == (40, 41, 42, 43)
    assert transition.lean_theorem.endswith(f"ShardedRel.fw_softmax_dim{dim}_rank4")


def _closed_fixture(dim, k=3):
    plan, frontier, _ = _matcher_fixture(dim, k)
    cert = rc.advance_k_rank_softmax_frontiers(plan, (frontier,), ("sharded",))[0][0]
    full = cert.full_shape
    shard = cert.shard_shape
    in_sm, in_pms = 100, tuple(201+r for r in range(k))
    out_sm, out_pms = 110, tuple(301+r for r in range(k))
    input_fact = rc.RelationFactSpec(
        "sharded", ("init:100", *(f"init:{tid}" for tid in in_pms)), gather_dim=dim)
    output_fact = rc.RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))), gather_dim=dim)
    cert = replace(cert, input_fact=input_fact, output_fact=output_fact,
                   sm_step_id="sm:0:0",
                   pm_step_ids=tuple(f"pm:{r}:0" for r in range(k)))
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    before_fact = rc.ClosedRelationFactRecord(
        "fact_in", input_fact, "sharded", in_sm, in_pms, None, None,
        full, shard, dim)
    after_fact = rc.ClosedRelationFactRecord(
        "fact_out", output_fact, "sharded", out_sm, out_pms, None, None,
        full, shard, dim)
    pre = SimpleNamespace(state_id="state_pre", fact_ids=(before_fact.fact_id,))
    post = SimpleNamespace(state_id="state_post", fact_ids=(after_fact.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k),
        pre_state_id=pre.state_id, post_state_id=post.state_id)
    chain = SimpleNamespace(
        complete=True, relation_facts=(before_fact, after_fact), authority_facts=(),
        states=(pre, post), segments=(segment,))
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_softmax", [in_sm], [out_sm], [])],
        pm_nodes=[Node(r, "FW_softmax", [in_pms[r]], [out_pms[r]], []) for r in range(k)],
        sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref=f"SyntheticSoftmaxDim{dim}.gSM",
        pm_graph_ref=f"SyntheticSoftmaxDim{dim}.gPM")
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment, before_fact, after_fact


@pytest.mark.parametrize("dim", [1, 2])
def test_softmax_renderer_replays_exact_writers_and_axis_theorem(dim):
    ir, relation, segment, before, after = _closed_fixture(dim, 3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_softmax_out_g43") == 4
    assert f"ShardedRel.fw_softmax_dim{dim}_rank4" in source
    assert f"ShardedRel.fw_softmax_dim{3-dim}_rank4" not in source
    assert ", ".join(f"pmStore {tid}" for tid in before.pm_tids) in source
    assert ", ".join(f"pmFinal {tid}" for tid in after.pm_tids) in source
    assert "rankCount = 3" not in source


def test_softmax_renderer_ignores_unrelated_same_family_certificate():
    ir, relation, segment, *_ = _closed_fixture(2, 3)
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)
    exact = relation.certificates[0]
    unrelated = replace(
        exact,
        input_fact=rc.RelationFactSpec(
            "sharded", ("init:999", "init:998", "init:997", "init:996"),
            gather_dim=2,
        ),
    )
    relation.certificates = (unrelated, exact)

    assert composer.render_closed_segment(ir, relation, segment.segment_id) == expected


@pytest.mark.parametrize("mutation", ["malformed_pre", "malformed_post", "duplicate"])
def test_softmax_renderer_rejects_nonunique_exact_certificate(mutation):
    ir, relation, segment, *_ = _closed_fixture(2, 3)
    exact = relation.certificates[0]
    if mutation == "malformed_pre":
        relation.certificates = (replace(
            exact,
            input_fact=rc.RelationFactSpec(
                "sharded", ("init:999", "init:998", "init:997", "init:996"),
                gather_dim=2,
            ),
        ),)
    elif mutation == "malformed_post":
        relation.certificates = (replace(
            exact,
            output_fact=rc.RelationFactSpec(
                "sharded", ("sm:999:0", "pm:999:0", "pm:1000:0", "pm:1001:0"),
                gather_dim=2,
            ),
        ),)
    else:
        relation.certificates = (exact, exact)

    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(("field", "value"), [
    ("rule_id", "softmax-sharded-k-rank-dim1"),
    ("lean_theorem", "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_softmax_dim1_rank4"),
])
def test_softmax_renderer_rejects_tampered_axis_specific_transition_identity(field, value):
    ir, relation, segment, *_ = _closed_fixture(2, 3)
    transition = relation.transition_specs[0]
    relation.transition_specs = (replace(transition, **{field: value}),)

    with pytest.raises(ValueError, match="axis-specific theorem identity mismatch"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 7}, "ordered ranks"),
    ({"params": [9]}, "no parameters"),
    ({"ins": []}, "unary"),
    ({"ins": [999]}, "ordered input TIDs"),
])
def test_softmax_renderer_rejects_tampered_live_writers(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(2, 3)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_namespace(dim):
    ir, relation, segment, before, after = _closed_fixture(dim, 3)
    if dim == 1:
        full, shard = (2, 15, 7, 11), (2, 5, 7, 11)
    else:
        full, shard = (2, 5, 21, 11), (2, 5, 7, 11)
    cert = replace(relation.certificates[0], full_shape=full, shard_shape=shard)
    relation.certificates = (cert,)
    relation.dependent_chain_plan.relation_facts = (
        replace(before, full_shape=full, shard_shape=shard),
        replace(after, full_shape=full, shard_shape=shard),
    )
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    return f'''namespace SyntheticSoftmaxDim{dim}
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_softmax", ins := [100], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_softmax", ins := [201], outs := [301] }}, {{ rank := 1, op := "OpName.FW_softmax", ins := [202], outs := [302] }}, {{ rank := 2, op := "OpName.FW_softmax", ins := [203], outs := [303] }}] }}
def fact_in : RelationFact := .sharded 100 [201, 202, 203] {dim} {list(full)} {list(shard)}
def fact_out : RelationFact := .sharded 110 [301, 302, 303] {dim} {list(full)} {list(shard)}
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticSoftmaxDim{dim}
'''


def test_generated_softmax_witness_covers_both_dims_direct_renderer_output():
    source = f'''import denote.KRankSoftmaxGather

namespace TrainVerify.Denote
open RelationCompiler

{_witness_namespace(1)}
{_witness_namespace(2)}
end TrainVerify.Denote
'''
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankSoftmaxCompilerWitness.lean"
    assert witness.read_text(encoding="utf-8") == source
    assert source.startswith("import denote.KRankSoftmaxGather")
    assert source.count("import denote.KRankSoftmaxGather") == 1
    assert "sorry" not in source
