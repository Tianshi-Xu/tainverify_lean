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


def _matcher_fixture(axis, k=3, c=8):
    shard = (2, 4, 5, 7)
    full = list(shard)
    full[axis] *= k
    full = tuple(full)
    sm_x = _step("sm:1:0", side="sm", node_index=1, rank=0, op="Source", shape=full)
    pm_xs = tuple(_step(f"pm:{8+r}:0", side="pm", node_index=8+r, rank=r,
                        op="Source", shape=shard) for r in range(k))
    sm_div = _step("sm:30:0", side="sm", node_index=30, rank=0, op="FW_div",
                   inputs=(sm_x.step_id,), input_shapes=(full,), shape=full, params=(c,))
    pm_divs = tuple(_step(f"pm:{40+r}:0", side="pm", node_index=40+r, rank=r,
                         op="FW_div", inputs=(pm_xs[r].step_id,), input_shapes=(shard,),
                         shape=shard, params=(c,)) for r in range(k))
    plan = SimpleNamespace(steps=(sm_x, *pm_xs, sm_div, *pm_divs))
    frontier = (sm_div.step_id, *(s.step_id for s in pm_divs))
    return plan, frontier, (sm_x, pm_xs, sm_div, pm_divs)


@pytest.mark.parametrize("axis", [1, 2, 3])
def test_div_matcher_derives_axis_specific_ordered_sharded_input(axis):
    plan, frontier, parts = _matcher_fixture(axis, 3)
    sm_x, pm_xs, sm_div, pm_divs = parts
    certs, roots, layouts = rc.advance_k_rank_div_frontiers(plan, (frontier,), ("sharded",))
    cert = certs[0]
    assert cert.rule_id == f"div-sharded-k-rank-dim{axis}"
    assert cert.rank_count == 3 and cert.gather_dim == axis and cert.scalar_param == 8
    assert cert.input_fact == rc.RelationFactSpec(
        "sharded", (sm_x.step_id, *(s.step_id for s in pm_xs)), gather_dim=axis)
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=axis)
    assert cert.sm_step_id == sm_div.step_id
    assert cert.pm_step_ids == tuple(s.step_id for s in pm_divs)
    assert roots == (cert.input_fact.step_triple,)
    assert layouts == ("sharded",)
    assert cert.lean_theorem.endswith(f"ShardedRel.fw_div_dim{axis}_rank4")


@pytest.mark.parametrize(("target", "mutation", "message"), [
    ("writer", {"rank": 2}, "ordered ranks"),
    ("writer", {"parameters": ()}, "one scalar parameter"),
    ("writer", {"parameters": (8, 9)}, "one scalar parameter"),
    ("writer", {"parameters": (9,)}, "identical scalar parameter"),
    ("writer", {"input_bindings": ("pm:9:0", "pm:10:0")}, "unary"),
    ("writer", {"input_shapes": ()}, "one declared input shape"),
    ("writer", {"output_shape": (2, 4, 5)}, "rank-4"),
    ("input", {"output_shape": (2, 4, 6, 7)}, "input sharding"),
])
def test_div_matcher_fails_closed_on_exact_contract_mutations(target, mutation, message):
    plan, frontier, parts = _matcher_fixture(1, 3)
    _sm_x, pm_xs, _sm_div, pm_divs = parts
    victim = pm_divs[1] if target == "writer" else pm_xs[1]
    replacement = SimpleNamespace(**{**victim.__dict__, **mutation})
    steps = tuple(replacement if s is victim else s for s in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_div_frontiers(SimpleNamespace(steps=steps), (frontier,), ("sharded",))


def test_div_matcher_leaves_mixed_frontier_unresolved():
    plan, frontier, parts = _matcher_fixture(2, 3)
    bad = SimpleNamespace(**{**parts[3][1].__dict__, "op": "AllToAll"})
    steps = tuple(bad if s is parts[3][1] else s for s in plan.steps)
    certs, roots, layouts = rc.advance_k_rank_div_frontiers(
        SimpleNamespace(steps=steps), (frontier,), ("sharded",))
    assert certs == () and roots == (frontier,) and layouts == ("sharded",)


def test_div_matcher_rejects_non_theorem_axis_even_when_shape_reconstructs():
    plan, frontier, _ = _matcher_fixture(0, 4)
    with pytest.raises(rc.RelationCompositionError, match="dim1, dim2, or dim3"):
        rc.advance_k_rank_div_frontiers(plan, (frontier,), ("sharded",))


@pytest.mark.parametrize("axis", [1, 2, 3])
def test_div_fixed_point_and_transition_own_exact_one_plus_k_writers(axis):
    plan, frontier, _ = _matcher_fixture(axis, 4)
    sink = []
    roots, layouts = rc.normalize_relation_frontiers(
        plan, (frontier,), ("sharded",), rules=("div_k",), certificate_sink=sink)
    cert = sink[0]
    assert roots == (cert.input_fact.step_triple,) and layouts == ("sharded",)
    transition = rc.build_certificate_transition_specs(plan, tuple(sink))[0]
    assert transition.pre_facts == (cert.input_fact,)
    assert transition.post_facts == (cert.output_fact,)
    assert transition.sm_node_indices == (30,)
    assert transition.pm_node_indices == (40, 41, 42, 43)


def _closed_fixture(axis, k=3, c=8):
    plan, frontier, _ = _matcher_fixture(axis, k, c)
    cert = rc.advance_k_rank_div_frontiers(plan, (frontier,), ("sharded",))[0][0]
    x_sm, x_pms = 100, tuple(201+r for r in range(k))
    out_sm, out_pms = 110, tuple(301+r for r in range(k))
    x_fact = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{t}" for t in x_pms)), gather_dim=axis)
    out_fact = rc.RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))), gather_dim=axis)
    cert = replace(cert, input_fact=x_fact, output_fact=out_fact, sm_step_id="sm:0:0",
                   pm_step_ids=tuple(f"pm:{r}:0" for r in range(k)))
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    inp = rc.ClosedRelationFactRecord("fact_in", x_fact, "sharded", x_sm, x_pms, None, None,
        cert.full_shape, cert.shard_shape, axis)
    out = rc.ClosedRelationFactRecord("fact_out", out_fact, "sharded", out_sm, out_pms, None, None,
        cert.full_shape, cert.shard_shape, axis)
    pre = SimpleNamespace(state_id="state_pre", fact_ids=(inp.fact_id,))
    post = SimpleNamespace(state_id="state_post", fact_ids=(out.fact_id,))
    segment = SimpleNamespace(segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k), pre_state_id=pre.state_id, post_state_id=post.state_id)
    chain = SimpleNamespace(complete=True, relation_facts=(inp, out), authority_facts=(),
                            states=(pre, post), segments=(segment,))
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_div", [x_sm], [out_sm], [c])],
        pm_nodes=[Node(r, "FW_div", [x_pms[r]], [out_pms[r]], [c]) for r in range(k)],
        sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref=f"SyntheticDiv{axis}.gSM", pm_graph_ref=f"SyntheticDiv{axis}.gPM")
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment, inp, out


@pytest.mark.parametrize(("axis", "apply_lemma"), [
    (1, "applyNode_fw_div_out_g67"),
    (2, "applyNode_fw_div_out_g92"),
    (3, "applyNode_fw_div_out_g92"),
])
def test_div_renderer_replays_exact_writers_scalar_and_axis_wrapper(axis, apply_lemma):
    ir, relation, segment, inp, out = _closed_fixture(axis)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count('op := "OpName.FW_div"') == 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count(apply_lemma) == 4
    assert f"ShardedRel.fw_div_dim{axis}_rank4" in source
    assert "(c := (8 : Scalar))" in source
    assert ", ".join(f"pmStore {tid}" for tid in inp.pm_tids) in source
    assert ", ".join(f"pmFinal {tid}" for tid in out.pm_tids) in source
    assert "rankCount = 3" not in source


@pytest.mark.parametrize("k", [2, 5])
def test_div_renderer_preserves_dynamic_ordered_k_and_scalar_identity(k):
    ir, relation, segment, inp, out = _closed_fixture(2, k=k, c=13)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count('op := "OpName.FW_div"') == 1 + k
    assert source.count("foldl_faithful_middle_writer") == 1 + k
    assert source.count("(13 : Scalar)") == 2 * (1 + k) + 1
    assert ", ".join(f"pmStore {tid}" for tid in inp.pm_tids) in source
    assert ", ".join(f"pmFinal {tid}" for tid in out.pm_tids) in source


def test_div_renderer_ignores_unrelated_axis_and_same_family_certificates():
    ir, relation, segment, *_ = _closed_fixture(1, k=3)
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)
    exact = relation.certificates[0]
    _other_ir, other_relation, *_ = _closed_fixture(2, k=3)
    unrelated_axis = other_relation.certificates[0]
    unrelated_same_axis = replace(
        exact,
        input_fact=rc.RelationFactSpec(
            "sharded", ("init:999", "init:998", "init:997", "init:996"),
            gather_dim=1,
        ),
    )
    structurally_matching_foreign_class = SimpleNamespace(**exact.__dict__)
    relation.certificates = (
        unrelated_axis, unrelated_same_axis, structurally_matching_foreign_class, exact,
    )

    assert composer.render_closed_segment(ir, relation, segment.segment_id) == expected


@pytest.mark.parametrize("mutation", ["malformed", "duplicate"])
def test_div_renderer_rejects_nonunique_exact_certificate(mutation):
    ir, relation, segment, *_ = _closed_fixture(3, k=3)
    exact = relation.certificates[0]
    if mutation == "malformed":
        relation.certificates = (replace(
            exact,
            output_fact=rc.RelationFactSpec(
                "sharded", ("sm:999:0", "pm:999:0", "pm:1000:0", "pm:1001:0"),
                gather_dim=3,
            ),
        ),)
    else:
        relation.certificates = (exact, exact)

    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(("field", "value"), [
    ("rule_id", "div-sharded-k-rank-dim2"),
    ("lean_theorem", "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim2_rank4"),
])
def test_div_renderer_rejects_tampered_transition_identity(field, value):
    ir, relation, segment, *_ = _closed_fixture(1, k=3)
    relation.transition_specs = (replace(relation.transition_specs[0], **{field: value}),)
    with pytest.raises(ValueError, match="axis-specific|identity mismatch"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 7}, "ordered ranks"),
    ({"params": []}, "one scalar parameter"),
    ({"params": [9]}, "identical scalar parameter"),
    ({"ins": [202, 999]}, "unary"),
])
def test_div_renderer_rejects_tampered_live_writers(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(1)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_div_closed_module_import_mapping():
    for axis in (1, 2, 3):
        assert composer._closed_segment_family_imports(
            (f"div-sharded-k-rank-dim{axis}",)) == ("denote.KRankDivGather",)


def _witness_source(rendered, axis, k):
    if axis == 3:
        full, shard = "[1, 12, 1024, 1024]", "[1, 12, 1024, 256]"
    else:
        full = "[1, 12, 768, 64]" if axis == 2 else "[1, 36, 256, 64]"
        shard = "[1, 12, 256, 64]"
    pm_nodes = ", ".join(
        f'{{ rank := {rank}, op := "OpName.FW_div", ins := [{201 + rank}], '
        f'outs := [{301 + rank}], params := [8] }}'
        for rank in range(k)
    )
    pm_inputs = ", ".join(str(201 + rank) for rank in range(k))
    pm_outputs = ", ".join(str(301 + rank) for rank in range(k))
    return f'''import denote.KRankDivGather

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticDiv{axis}
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_div", ins := [100], outs := [110], params := [8] }}] }}
def gPM : GraphDecl := {{ numRanks := {k}, nodes := [{pm_nodes}] }}

def fact_in : RelationFact := .sharded 100 [{pm_inputs}] {axis} {full} {shard}
def fact_out : RelationFact := .sharded 110 [{pm_outputs}] {axis} {full} {shard}
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticDiv{axis}
end TrainVerify.Denote
'''


@pytest.mark.parametrize("axis", [1, 2, 3])
def test_generated_div_witness_is_direct_renderer_output(axis):
    k = 4 if axis == 3 else 3
    ir, relation, segment, *_ = _closed_fixture(axis, k=k)
    if axis == 3:
        full, shard = (1, 12, 1024, 1024), (1, 12, 1024, 256)
    else:
        full = (1, 12, 768, 64) if axis == 2 else (1, 36, 256, 64)
        shard = (1, 12, 256, 64)
    cert = relation.certificates[0]
    relation.certificates = (replace(cert, full_shape=full, shard_shape=shard),)
    records = list(relation.dependent_chain_plan.relation_facts)
    records[0] = replace(records[0], full_shape=full, shard_shape=shard)
    records[1] = replace(records[1], full_shape=full, shard_shape=shard)
    relation.dependent_chain_plan.relation_facts = tuple(records)
    source = _witness_source(
        composer.render_closed_segment(ir, relation, segment.segment_id), axis, k)
    witness = Path(__file__).parents[2] / f"trainverify/denote/GeneratedKRankDivDim{axis}CompilerWitness.lean"
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert source.count("import denote.KRankDivGather") == 1
    assert "sorry" not in source
