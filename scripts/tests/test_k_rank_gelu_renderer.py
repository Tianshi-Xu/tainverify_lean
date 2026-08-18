from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


RULE = "gelu-sharded-k-rank"
THEOREM = "TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq"


def _closed_fixture(k=3, gather_dim=1):
    input_tids = tuple(200 + rank for rank in range(k))
    output_tids = tuple(300 + rank for rank in range(k))
    shard = (2, 4, 5)
    full = list(shard)
    full[gather_dim] *= k
    full = tuple(full)
    input_spec = rc.RelationFactSpec(
        "sharded", ("init:100", *(f"init:{tid}" for tid in input_tids)),
        gather_dim=gather_dim,
    )
    output_spec = rc.RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))),
        gather_dim=gather_dim,
    )
    cert = rc.KRankLocalRelationCertificate(
        rule_id=RULE, op="FW_gelu", rank_count=k, gather_dim=gather_dim,
        input_fact=input_spec, output_fact=output_spec, sm_step_id="sm:0:0",
        pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
        external_tids=(), external_shapes=(), lean_theorem=THEOREM,
    )
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    pre = rc.ClosedRelationFactRecord(
        "fact_in", input_spec, "sharded", 100, input_tids, None, None,
        full, shard, gather_dim,
    )
    post = rc.ClosedRelationFactRecord(
        "fact_out", output_spec, "sharded", 110, output_tids, None, None,
        full, shard, gather_dim,
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=(pre.fact_id,))
    after = SimpleNamespace(state_id="state_post", fact_ids=(post.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000051", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k), pre_state_id=before.state_id,
        post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(pre, post), authority_facts=(),
        states=(before, after), segments=(segment,),
    )
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_gelu", [100], [110], [])],
        pm_nodes=[Node(rank, "FW_gelu", [input_tids[rank]], [output_tids[rank]], [])
                  for rank in range(k)],
        sm_graph_ref="SyntheticGelu.gSM", pm_graph_ref="SyntheticGelu.gPM",
    )
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain,
    )
    return ir, relation, segment, cert, transition, pre, post


def test_gelu_typed_certificate_has_exact_rule_theorem_and_empty_external_authority():
    _ir, _relation, _segment, cert, transition, pre, post = _closed_fixture(k=4)
    assert type(cert) is rc.KRankLocalRelationCertificate
    assert (cert.rule_id, cert.op, cert.rank_count) == (RULE, "FW_gelu", 4)
    assert cert.lean_theorem == THEOREM
    assert cert.external_tids == cert.external_shapes == ()
    assert transition.pre_facts == (pre.source,)
    assert transition.post_facts == (post.source,)


@pytest.mark.parametrize("k", (2, 3, 5))
def test_gelu_renderer_owns_exact_one_plus_dynamic_ordered_k_writers(k):
    ir, relation, segment, _cert, _transition, pre, post = _closed_fixture(k=k)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count(": NodeDecl :=") == 1 + k
    assert source.count("foldl_faithful_unary_middle_writer") == 1 + k
    assert source.count("applyNode_fw_gelu_out") == 1 + k
    assert THEOREM in source
    assert "[" + ", ".join(f"pmStore {tid}" for tid in pre.pm_tids) + "].length" in source
    assert "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]" in source
    assert f"rankCount = {k}" not in source


def test_gelu_renderer_selects_exact_transition_certificate_and_rejects_duplicates():
    ir, relation, segment, cert, *_ = _closed_fixture(k=3)
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)
    unrelated = replace(
        cert,
        input_fact=rc.RelationFactSpec(
            "sharded", ("sm:99:0", "pm:99:0", "pm:100:0"), gather_dim=1,
        ),
    )
    with_unrelated = SimpleNamespace(**{**relation.__dict__, "certificates": (unrelated, cert)})
    assert composer.render_closed_segment(ir, with_unrelated, segment.segment_id) == expected

    for certificates in ((unrelated,), (cert, cert)):
        broken = SimpleNamespace(**{**relation.__dict__, "certificates": certificates})
        with pytest.raises(ValueError, match="one exact typed certificate"):
            composer.render_closed_segment(ir, broken, segment.segment_id)


@pytest.mark.parametrize(("field", "value", "message"), [
    ("rule_id", "gelu-lookalike", "theorem identity"),
    ("lean_theorem", "TrainVerify.Denote.fake_gelu", "theorem identity"),
])
def test_gelu_renderer_rejects_tampered_transition_identity(field, value, message):
    ir, relation, segment, _cert, transition, *_ = _closed_fixture(k=3)
    broken_transition = replace(transition, **{field: value})
    broken = SimpleNamespace(**{**relation.__dict__, "transition_specs": (broken_transition,)})
    with pytest.raises(ValueError, match=message):
        composer.render_closed_k_rank_gelu_segment(ir, broken, segment.segment_id)


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 9}, "ordered ranks"),
    ({"op": "FW_sigmoid"}, "unary singleton-output FW_gelu"),
    ({"ins": [999]}, "ordered relation TIDs"),
    ({"outs": [999]}, "ordered relation TIDs"),
    ({"params": [1]}, "no parameters"),
    ({"ins": [201, 202]}, "unary singleton-output FW_gelu"),
])
def test_gelu_renderer_rejects_malformed_or_tampered_pm_writer(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    for field, value in mutation.items():
        setattr(ir.pm_nodes[1], field, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_gelu_renderer_rejects_shape_or_state_framing_tampering():
    ir, relation, segment, _cert, _transition, pre, post = _closed_fixture(k=3)
    malformed_post = replace(post, shard_shape=(2, 4, 6))
    chain = SimpleNamespace(**{
        **relation.dependent_chain_plan.__dict__, "relation_facts": (pre, malformed_post),
    })
    with pytest.raises(ValueError, match="relation metadata"):
        composer.render_closed_segment(
            ir, SimpleNamespace(**{**relation.__dict__, "dependent_chain_plan": chain}),
            segment.segment_id,
        )

    bad_after = SimpleNamespace(state_id="state_post", fact_ids=(post.fact_id, "unproved"))
    chain = SimpleNamespace(**{
        **relation.dependent_chain_plan.__dict__,
        "states": (relation.dependent_chain_plan.states[0], bad_after),
    })
    with pytest.raises(ValueError, match="unproved fact"):
        composer.render_closed_segment(
            ir, SimpleNamespace(**{**relation.__dict__, "dependent_chain_plan": chain}),
            segment.segment_id,
        )


def test_gelu_renderer_rejects_duplicate_materialized_fact_or_state_ids():
    ir, relation, segment, _cert, _transition, pre, post = _closed_fixture(k=3)
    for field, values, message in (
        ("relation_facts", (pre, post, post), "duplicate relation fact source"),
        ("states", (*relation.dependent_chain_plan.states, relation.dependent_chain_plan.states[1]),
         "duplicate relation state id"),
    ):
        chain = SimpleNamespace(**{**relation.dependent_chain_plan.__dict__, field: values})
        broken = SimpleNamespace(**{**relation.__dict__, "dependent_chain_plan": chain})
        with pytest.raises(ValueError, match=message):
            composer.render_closed_segment(ir, broken, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticGelu
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }}, {{ rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }}, {{ rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }}] }}

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 12, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

{rendered}
#print axioms segment_000051
end
end SyntheticGelu
end TrainVerify.Denote
'''


def test_generated_gelu_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    source = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankGeluRendererWitness.lean"
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert source.count("import denote.RelationCompiler") == 1
    assert "sorry" not in source


def test_gelu_closed_bundle_registers_theorem_import_boundary():
    assert composer._closed_segment_family_imports((RULE,), (THEOREM,)) == ()
