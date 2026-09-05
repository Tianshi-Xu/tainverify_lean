from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


def _step(step_id, *, side, node_index, rank, op, inputs=(), shape=()):
    return SimpleNamespace(
        step_id=step_id, side=side, node_index=node_index, rank=rank, op=op,
        input_bindings=tuple(inputs), input_shapes=(), output_shape=tuple(shape),
        parameters=(),
    )


def _matcher_fixture(k=3):
    shard, full = (2, 4, 5), (2, 4 * k, 5)
    sm_inputs = (
        _step("sm:1:0", side="sm", node_index=1, rank=0, op="Source", shape=full),
        _step("sm:2:0", side="sm", node_index=2, rank=0, op="Source", shape=full),
    )
    pm_inputs = tuple(tuple(
        _step(f"pm:{10 * argument + rank}:0", side="pm", node_index=10 * argument + rank,
              rank=rank, op="Source", shape=shard)
        for rank in range(k)) for argument in range(2))
    sm_add = _step("sm:30:0", side="sm", node_index=30, rank=0, op="FW_add",
                   inputs=tuple(step.step_id for step in sm_inputs), shape=full)
    pm_adds = tuple(_step(
        f"pm:{40 + rank}:0", side="pm", node_index=40 + rank, rank=rank, op="FW_add",
        inputs=(pm_inputs[0][rank].step_id, pm_inputs[1][rank].step_id), shape=shard,
    ) for rank in range(k))
    plan = SimpleNamespace(steps=(*sm_inputs, *pm_inputs[0], *pm_inputs[1], sm_add, *pm_adds))
    frontier = (sm_add.step_id, *(step.step_id for step in pm_adds))
    return plan, frontier, sm_inputs, pm_inputs, sm_add, pm_adds


def test_add_matcher_certificate_preserves_dynamic_rank_and_operand_order():
    plan, frontier, sm_inputs, pm_inputs, sm_add, pm_adds = _matcher_fixture(k=4)
    certs, roots, layouts = rc.advance_k_rank_add_relation_frontiers(
        plan, (frontier,), ("sharded",))
    cert = certs[0]
    assert cert.rule_id == "add-sharded-k-rank"
    assert cert.rank_count == 4 and cert.gather_dim == 1
    assert cert.input_facts == tuple(rc.RelationFactSpec(
        "sharded", (sm_inputs[arg].step_id, *(step.step_id for step in pm_inputs[arg])),
        gather_dim=1) for arg in range(2))
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=1)
    assert cert.sm_step_id == sm_add.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_adds)
    assert roots == tuple(fact.step_triple for fact in cert.input_facts)
    assert layouts == ("sharded", "sharded")
    assert cert.lean_theorem == "TrainVerify.Denote.fw_add_allGather_dim_K"


def _closed_fixture(k=3):
    plan, frontier, *_ = _matcher_fixture(k)
    cert = rc.advance_k_rank_add_relation_frontiers(plan, (frontier,), ("sharded",))[0][0]
    a_sm, b_sm, out_sm = 100, 110, 120
    a_pms = tuple(200 + rank for rank in range(k))
    b_pms = tuple(210 + rank for rank in range(k))
    out_pms = tuple(300 + rank for rank in range(k))
    a_spec = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{x}" for x in a_pms)), gather_dim=1)
    b_spec = rc.RelationFactSpec("sharded", ("init:110", *(f"init:{x}" for x in b_pms)), gather_dim=1)
    out_spec = rc.RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))), gather_dim=1)
    cert = replace(cert, input_facts=(a_spec, b_spec), output_fact=out_spec,
                   sm_step_id="sm:0:0", pm_step_ids=tuple(f"pm:{r}:0" for r in range(k)))
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    full, shard = (2, 4 * k, 5), (2, 4, 5)
    a = rc.ClosedRelationFactRecord("fact_a", a_spec, "sharded", a_sm, a_pms,
                                    None, None, full, shard, 1)
    b = rc.ClosedRelationFactRecord("fact_b", b_spec, "sharded", b_sm, b_pms,
                                    None, None, full, shard, 1)
    out = rc.ClosedRelationFactRecord("fact_out", out_spec, "sharded", out_sm, out_pms,
                                      None, None, full, shard, 1)
    before = SimpleNamespace(state_id="state_pre", fact_ids=(a.fact_id, b.fact_id))
    after = SimpleNamespace(state_id="state_post", fact_ids=(out.fact_id,))
    segment = SimpleNamespace(segment_id="segment_000004", transition_ids=(transition.transition_id,),
                              sm_range=(0, 1), pm_range=(0, k),
                              pre_state_id=before.state_id, post_state_id=after.state_id)
    chain = SimpleNamespace(complete=True, relation_facts=(a, b, out), authority_facts=(),
                            states=(before, after), segments=(segment,))
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_add", [a_sm, b_sm], [out_sm], [])],
        pm_nodes=[Node(rank, "FW_add", [a_pms[rank], b_pms[rank]], [out_pms[rank]], [])
                  for rank in range(k)],
        sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticAdd.gSM", pm_graph_ref="SyntheticAdd.gPM",
    )
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,),
                               dependent_chain_plan=chain)
    return ir, relation, segment, a, b, out


def test_add_renderer_uses_exact_certificate_ordered_inputs_and_one_plus_k_writers():
    ir, relation, segment, a, b, out = _closed_fixture(k=3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_add2_out") == 4
    assert "fw_add_allGather_dim_K" in source
    assert f"[pmFinal {a.pm_tids[0]}, pmFinal {a.pm_tids[1]}, pmFinal {a.pm_tids[2]}]" in source
    assert f"[pmFinal {b.pm_tids[0]}, pmFinal {b.pm_tids[1]}, pmFinal {b.pm_tids[2]}]" in source
    assert f"[pmFinal {out.pm_tids[0]}, pmFinal {out.pm_tids[1]}, pmFinal {out.pm_tids[2]}]" in source
    assert "rankCount = 3" not in source


def test_add_renderer_recovers_certificate_roles_when_transition_pre_facts_are_reordered():
    ir, relation, segment, a, b, *_ = _closed_fixture(k=3)
    transition = relation.transition_specs[0]
    reordered = replace(transition, pre_facts=tuple(reversed(transition.pre_facts)))
    reordered_relation = SimpleNamespace(
        **{**relation.__dict__, "transition_specs": (reordered,)}
    )

    source = composer.render_closed_segment(ir, reordered_relation, segment.segment_id)

    assert f"[pmFinal {a.pm_tids[0]}, pmFinal {a.pm_tids[1]}, pmFinal {a.pm_tids[2]}]" in source
    assert f"[pmFinal {b.pm_tids[0]}, pmFinal {b.pm_tids[1]}, pmFinal {b.pm_tids[2]}]" in source


def test_add_renderer_selects_one_exact_certificate_and_rejects_duplicates():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    exact = relation.certificates[0]
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)

    unrelated = replace(exact, input_facts=tuple(reversed(exact.input_facts)))
    with_unrelated = SimpleNamespace(
        **{**relation.__dict__, "certificates": (unrelated, exact)}
    )
    assert composer.render_closed_segment(ir, with_unrelated, segment.segment_id) == expected

    duplicate = SimpleNamespace(
        **{**relation.__dict__, "certificates": (exact, exact)}
    )
    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_segment(ir, duplicate, segment.segment_id)


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 9}, "ordered ranks"),
    ({"ins": [211, 201]}, "operand order"),
    ({"ins": [201, 999]}, "ordered relation TIDs"),
    ({"params": [1]}, "no parameters"),
])
def test_add_renderer_rejects_tampered_or_misaligned_rank_inputs(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    for key, value in mutation.items():
        setattr(ir.pm_nodes[1], key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_add_closed_module_registers_exact_theorem_import():
    assert composer._closed_segment_family_imports(
        ("add-sharded-k-rank",),
        ("TrainVerify.Denote.fw_add_allGather_dim_K",),
    ) == ("denote.KRankAddGather",)


def _witness_source(rendered, k):
    pm_nodes = ", ".join(
        f'{{ rank := {rank}, op := "OpName.FW_add", ins := [{200 + rank}, {210 + rank}], outs := [{300 + rank}] }}'
        for rank in range(k))
    return f'''import denote.KRankAddGather
import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticAdd
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] }}] }}
def gPM : GraphDecl := {{ numRanks := {k}, nodes := [{pm_nodes}] }}

def fact_a : RelationFact := .sharded 100 [{', '.join(str(200+r) for r in range(k))}] 1 [2, {4*k}, 5] [2, 4, 5]
def fact_b : RelationFact := .sharded 110 [{', '.join(str(210+r) for r in range(k))}] 1 [2, {4*k}, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 120 [{', '.join(str(300+r) for r in range(k))}] 1 [2, {4*k}, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_a, fact_b]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

{rendered}
#print axioms segment_000004
end
end SyntheticAdd
end TrainVerify.Denote
'''


def test_generated_add_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    source = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id), 3)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankAddCompilerWitness.lean"
    assert witness.read_text(encoding="utf-8") == source
    assert source.count("import denote.KRankAddGather") == 1
    assert "sorry" not in source
