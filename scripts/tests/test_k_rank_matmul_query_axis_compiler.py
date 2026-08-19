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


def _matcher_fixture(k=3):
    b, h, local_q, inner, m = 2, 4, 5, 7, 11
    x_full = (b, h, local_q * k, inner)
    x_local = (b, h, local_q, inner)
    y_shape = (b, h, inner, m)
    out_full = (b, h, local_q * k, m)
    out_local = (b, h, local_q, m)
    sm_x = _step("sm:1:0", side="sm", node_index=1, rank=0, op="Source", shape=x_full)
    pm_xs = tuple(_step(f"pm:{8+r}:0", side="pm", node_index=8+r, rank=r,
                        op="Source", shape=x_local) for r in range(k))
    sm_y = _step("sm:2:0", side="sm", node_index=2, rank=0, op="Source", shape=y_shape)
    pm_y = _step("pm:20:0", side="pm", node_index=20, rank=0, op="AllGather", shape=y_shape)
    sm_mm = _step("sm:30:0", side="sm", node_index=30, rank=0, op="FW_matmul",
                  inputs=(sm_x.step_id, sm_y.step_id), input_shapes=(x_full, y_shape), shape=out_full)
    pm_mms = tuple(_step(f"pm:{40+r}:0", side="pm", node_index=40+r, rank=r,
                         op="FW_matmul", inputs=(pm_xs[r].step_id, pm_y.step_id),
                         input_shapes=(x_local, y_shape), shape=out_local) for r in range(k))
    plan = SimpleNamespace(steps=(sm_x, *pm_xs, sm_y, pm_y, sm_mm, *pm_mms))
    frontier = (sm_mm.step_id, *(s.step_id for s in pm_mms))
    return plan, frontier, (sm_x, pm_xs, sm_y, pm_y, sm_mm, pm_mms)


def test_query_axis_matcher_derives_ordered_dim2_x_and_actual_joined_shared_y():
    plan, frontier, parts = _matcher_fixture(3)
    sm_x, pm_xs, sm_y, pm_y, sm_mm, pm_mms = parts
    certs, roots, layouts = rc.advance_k_rank_matmul_query_axis_frontiers(
        plan, (frontier,), ("sharded",))
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "matmul-query-axis-sharded-k-rank-dim2"
    assert cert.rank_count == 3 and cert.output_gather_dim == 2
    assert cert.first_operand_fact == rc.RelationFactSpec(
        "sharded", (sm_x.step_id, *(s.step_id for s in pm_xs)), gather_dim=2)
    assert cert.second_operand_fact == rc.RelationFactSpec(
        "joined", (sm_y.step_id,), joined_pm_step=pm_y.step_id)
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=2)
    assert cert.sm_step_id == sm_mm.step_id
    assert cert.pm_step_ids == tuple(s.step_id for s in pm_mms)
    assert roots == (
        cert.first_operand_fact.step_triple,
        (cert.second_operand_fact.step_triple[0], cert.second_operand_fact.joined_pm_step),
    )
    assert layouts == ("sharded", "joined")


@pytest.mark.parametrize(("target", "mutation", "message"), [
    ("writer", {"rank": 2}, "ordered ranks"),
    ("writer", {"parameters": (1,)}, "no parameters"),
    ("writer", {"input_bindings": ("pm:9:0",)}, "input arity"),
    ("writer", {"input_shapes": ((2, 4, 5, 7),)}, "input shapes"),
    ("writer", {"output_shape": (2, 4, 5)}, "rank-4"),
    ("x", {"output_shape": (2, 4, 6, 7)}, "first operand"),
    ("y", {"output_shape": (2, 4, 8, 11)}, "second operand"),
])
def test_query_axis_matcher_fails_closed_on_exact_contract_mutations(target, mutation, message):
    plan, frontier, parts = _matcher_fixture(3)
    _sm_x, pm_xs, _sm_y, pm_y, _sm_mm, pm_mms = parts
    victim = {"writer": pm_mms[1], "x": pm_xs[1], "y": pm_y}[target]
    replacement = SimpleNamespace(**{**victim.__dict__, **mutation})
    steps = tuple(replacement if s is victim else s for s in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_matmul_query_axis_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",))


def test_query_axis_matcher_requires_every_pm_writer_to_reference_same_y():
    plan, frontier, parts = _matcher_fixture(3)
    _sm_x, _pm_xs, _sm_y, pm_y, _sm_mm, pm_mms = parts
    other_y = SimpleNamespace(**{**pm_y.__dict__, "step_id": "pm:21:0", "node_index": 21})
    bad = SimpleNamespace(**{**pm_mms[1].__dict__,
        "input_bindings": (pm_mms[1].input_bindings[0], other_y.step_id)})
    certs, roots, layouts = rc.advance_k_rank_matmul_query_axis_frontiers(
        SimpleNamespace(steps=(*plan.steps, other_y, bad)), (frontier,), ("sharded",))
    assert certs == () and roots == (frontier,) and layouts == ("sharded",)


def test_query_axis_fixed_point_and_transition_own_exact_one_plus_k_writers():
    plan, frontier, _ = _matcher_fixture(4)
    sink = []
    roots, layouts = rc.normalize_relation_frontiers(
        plan, (frontier,), ("sharded",), rules=("matmul_query_axis_k",), certificate_sink=sink)
    cert = sink[0]
    assert roots == (
        cert.first_operand_fact.step_triple,
        (cert.second_operand_fact.step_triple[0], cert.second_operand_fact.joined_pm_step),
    )
    assert layouts == ("sharded", "joined")
    transition = rc.build_certificate_transition_specs(plan, tuple(sink))[0]
    assert transition.pre_facts == tuple(sorted((cert.first_operand_fact, cert.second_operand_fact)))
    assert transition.post_facts == (cert.output_fact,)
    assert transition.sm_node_indices == (30,)
    assert transition.pm_node_indices == (40, 41, 42, 43)
    assert transition.lean_theorem.endswith("ShardedRel.fw_matmul_query_axis_rank4")


def _closed_fixture(k=3):
    plan, frontier, _ = _matcher_fixture(k)
    cert = rc.advance_k_rank_matmul_query_axis_frontiers(plan, (frontier,), ("sharded",))[0][0]
    x_sm, x_pms, y_sm, y_pm = 100, tuple(201+r for r in range(k)), 101, 250
    out_sm, out_pms = 110, tuple(301+r for r in range(k))
    x_fact = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{t}" for t in x_pms)), gather_dim=2)
    y_fact = rc.RelationFactSpec(
        "joined", ("init:101",), joined_pm_step="init:250"
    )
    out_fact = rc.RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))), gather_dim=2)
    cert = replace(cert, first_operand_fact=x_fact, second_operand_fact=y_fact, output_fact=out_fact,
                   sm_step_id="sm:0:0", pm_step_ids=tuple(f"pm:{r}:0" for r in range(k)))
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    x = rc.ClosedRelationFactRecord("fact_x", x_fact, "sharded", x_sm, x_pms, None, None,
        cert.first_operand_full_shape, cert.first_operand_shard_shape, 2)
    y = rc.ClosedRelationFactRecord("fact_y", y_fact, "joined", y_sm, (), None, None,
        cert.second_operand_shape, cert.second_operand_shape, None, joined_pm_tid=y_pm)
    out = rc.ClosedRelationFactRecord("fact_out", out_fact, "sharded", out_sm, out_pms, None, None,
        cert.output_full_shape, cert.output_shard_shape, 2)
    pre = SimpleNamespace(state_id="state_pre", fact_ids=(x.fact_id, y.fact_id))
    post = SimpleNamespace(state_id="state_post", fact_ids=(out.fact_id,))
    segment = SimpleNamespace(segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k), pre_state_id=pre.state_id, post_state_id=post.state_id)
    chain = SimpleNamespace(complete=True, relation_facts=(x, y, out), authority_facts=(),
                            states=(pre, post), segments=(segment,))
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_matmul", [x_sm, y_sm], [out_sm], [])],
        pm_nodes=[Node(r, "FW_matmul", [x_pms[r], y_pm], [out_pms[r]], []) for r in range(k)],
        sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticQuery.gSM", pm_graph_ref="SyntheticQuery.gPM")
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment, x, y, out


def test_query_axis_closed_module_imports_checked_query_axis_theorem():
    assert composer._closed_segment_family_imports(
        ("matmul-query-axis-sharded-k-rank-dim2",)
    ) == ("denote.KRankMatmulQueryAxis",)


def test_query_axis_renderer_replays_exact_writers_shared_y_and_checked_theorem():
    ir, relation, segment, x, y, out = _closed_fixture(3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count('op := "OpName.FW_matmul"') == 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_matmul_out") == 4
    assert "ShardedRel.fw_matmul_query_axis_rank4" in source
    assert ", ".join(f"pmStore {tid}" for tid in x.pm_tids) in source
    assert source.count(f"pmStore {y.joined_pm_tid}") >= 4
    assert ", ".join(f"pmFinal {tid}" for tid in out.pm_tids) in source
    assert "rankCount = 3" not in source


def test_query_axis_renderer_ignores_unrelated_same_family_certificate_byte_exactly():
    ir, relation, segment, *_ = _closed_fixture(3)
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)
    exact = relation.certificates[0]
    unrelated = replace(
        exact,
        first_operand_fact=rc.RelationFactSpec(
            "sharded", ("init:999", "init:991", "init:992", "init:993"), gather_dim=2
        ),
    )
    relation.certificates = (unrelated, exact)

    assert composer.render_closed_segment(ir, relation, segment.segment_id) == expected


@pytest.mark.parametrize("tamper", ["class", "rule", "theorem", "left", "right", "post", "roles", "duplicate"])
def test_query_axis_renderer_fails_closed_on_every_exact_selector_axis(tamper):
    ir, relation, segment, *_ = _closed_fixture(3)
    exact = relation.certificates[0]
    if tamper == "class":
        malformed = SimpleNamespace(**exact.__dict__)
    elif tamper == "rule":
        malformed = replace(exact, rule_id="unrelated-rule")
    elif tamper == "theorem":
        malformed = replace(exact, lean_theorem="TrainVerify.Denote.unchecked")
    elif tamper == "left":
        malformed = replace(exact, first_operand_fact=replace(
            exact.first_operand_fact, step_triple=("sm:99:0", "pm:99:0")
        ))
    elif tamper == "right":
        malformed = replace(exact, second_operand_fact=replace(
            exact.second_operand_fact, step_triple=("sm:98:0",), joined_pm_step="pm:98:0"
        ))
    elif tamper == "post":
        malformed = replace(exact, output_fact=replace(
            exact.output_fact, step_triple=("sm:97:0", "pm:97:0")
        ))
    elif tamper == "roles":
        malformed = replace(
            exact,
            first_operand_fact=exact.second_operand_fact,
            second_operand_fact=exact.first_operand_fact,
        )
    else:
        relation.certificates = (exact, exact)
        malformed = None
    if malformed is not None:
        relation.certificates = (malformed,)

    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize("k", [2, 4])
def test_query_axis_renderer_derives_dynamic_ordered_k_and_exact_shared_tid(k):
    ir, relation, segment, first, second, output = _closed_fixture(k)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)

    assert source.count('op := "OpName.FW_matmul"') == 1 + k
    assert source.count("foldl_faithful_middle_writer") == 1 + k
    assert ", ".join(f"pmStore {tid}" for tid in first.pm_tids) in source
    assert source.count(f"pmStore {second.joined_pm_tid}") >= 1 + k
    assert ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) in source


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 7}, "ordered ranks"),
    ({"params": [9]}, "no parameters"),
    ({"ins": [202]}, "binary"),
    ({"ins": [202, 999]}, "shared second operand"),
])
def test_query_axis_renderer_rejects_tampered_live_writers(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(3)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.KRankMatmulQueryAxis

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticQuery
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [100, 101], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_matmul", ins := [201, 250], outs := [301] }}, {{ rank := 1, op := "OpName.FW_matmul", ins := [202, 250], outs := [302] }}, {{ rank := 2, op := "OpName.FW_matmul", ins := [203, 250], outs := [303] }}] }}

def fact_x : RelationFact := .sharded 100 [201, 202, 203] 2 [1, 12, 768, 1024] [1, 12, 256, 1024]
def fact_y : RelationFact := .joined 101 250 [1, 12, 1024, 64]
def fact_out : RelationFact := .sharded 110 [301, 302, 303] 2 [1, 12, 768, 64] [1, 12, 256, 64]
def state_pre : RelationState where facts := [fact_x, fact_y]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticQuery
end TrainVerify.Denote
'''


def test_generated_query_axis_witness_is_direct_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(3)
    # Replace only fixture shape authority through the fixture itself, never post-edit generated Lean.
    cert = relation.certificates[0]
    relation.certificates = (replace(cert,
        first_operand_full_shape=(1, 12, 768, 1024), first_operand_shard_shape=(1, 12, 256, 1024),
        second_operand_shape=(1, 12, 1024, 64), output_full_shape=(1, 12, 768, 64),
        output_shard_shape=(1, 12, 256, 64)),)
    records = list(relation.dependent_chain_plan.relation_facts)
    records[0] = replace(records[0], full_shape=(1, 12, 768, 1024), shard_shape=(1, 12, 256, 1024))
    records[1] = replace(records[1], full_shape=(1, 12, 1024, 64), shard_shape=(1, 12, 1024, 64))
    records[2] = replace(records[2], full_shape=(1, 12, 768, 64), shard_shape=(1, 12, 256, 64))
    relation.dependent_chain_plan.relation_facts = tuple(records)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    source = _witness_source(rendered)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankMatmulQueryAxisCompilerWitness.lean"
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert source.startswith("import denote.KRankMatmulQueryAxis")
    assert source.count("import denote.KRankMatmulQueryAxis") == 1
    assert "sorry" not in source
