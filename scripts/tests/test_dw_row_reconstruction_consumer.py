"""Real Goal 107 shared-writer regression; no Lean execution or file writes."""
from dataclasses import replace
from functools import lru_cache
from pathlib import Path

import pytest

from trainverify.bridge_emitter import parser, relation_compiler as rc
from trainverify.bridge_emitter.composer import (
    _typed_certificate_digest, render_closed_segment,
)
from trainverify.bridge_emitter.proof_compiler import build_default_registry, compile_proof_plan

RULE = "bw-linear-dw-output-row-sharded-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dw_row_allGather_rank3"
SEGMENT = "segment_000350"


@lru_cache(maxsize=1)
def base_fixture():
    """Compile the real legacy authority, never a replacement graph/premise."""
    with pytest.MonkeyPatch.context() as patch:
        patch.setattr(parser, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
        patch.setattr(parser, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
        patch.setattr(parser, "GEN_FILE", "GeneratedData.lean")
        patch.setattr(parser, "MOD_PREFIX", "denote.gpt_ly4_regen")
        ir = parser.load_goal_ir(107, str(Path(parser.__file__).resolve().parents[2]))
    relation = rc.compile_relation_plan(ir, compile_proof_plan(ir, build_default_registry()))
    segment = next(s for s in relation.dependent_chain_plan.segments if s.segment_id == SEGMENT)
    assert len(segment.transition_ids) == 5
    return ir, relation


def six_transition_fixture():
    ir, relation = base_fixture()
    chain = relation.dependent_chain_plan
    segment = next(s for s in chain.segments if s.segment_id == SEGMENT)
    lt = next(t for t in relation.transition_specs if t.transition_id in segment.transition_ids
              and t.rule_id == "bw-linear-dx-row-reduction-k-rank")
    lc = next(c for c in relation.certificates if type(c) is rc.KRankBWLinearDxCertificate
              and _typed_certificate_digest(c) == lt.certificate_digest)
    output = rc.RelationFactSpec("sharded", (f"sm:{lt.sm_node_indices[0]}:1",
        *(f"pm:{i}:1" for i in lt.pm_node_indices)), gather_dim=0)
    cert = rc.KRankBWLinearDwShardedCertificate(RULE, 4, *lc.input_facts, output,
        output.step_triple[0], output.step_triple[1:], THEOREM)
    transition = rc.CertificateTransitionSpec("transition_dw_row_consumer", RULE,
        tuple(sorted(lc.input_facts)), (output,), lt.sm_node_indices, lt.pm_node_indices,
        THEOREM, certificate_digest=_typed_certificate_digest(cert))
    record = rc.ClosedRelationFactRecord("fact_dw_row_consumer", output, "sharded",
        ir.sm_nodes[lt.sm_node_indices[0]].outs[1],
        tuple(ir.pm_nodes[i].outs[1] for i in lt.pm_node_indices), None, None,
        (32, 32), (8, 32), gather_dim=0)
    segment = replace(segment, transition_ids=(segment.transition_ids[0], transition.transition_id,
                                               *segment.transition_ids[1:]))
    chain = replace(chain, relation_facts=(*chain.relation_facts, record),
        states=tuple(replace(s, fact_ids=(*s.fact_ids, record.fact_id))
                     if s.state_id == segment.post_state_id else s for s in chain.states),
        segments=tuple(segment if s.segment_id == SEGMENT else s for s in chain.segments))
    return ir, replace(relation, dependent_chain_plan=chain,
        certificates=(*relation.certificates, cert), transition_specs=(*relation.transition_specs, transition))


def test_five_transition_base_renders():
    ir, relation = base_fixture()
    source = render_closed_segment(ir, relation, SEGMENT)
    assert "private def segment_000350:ClosedDepSegmentCertificate" in source
    assert "hDwComm" not in source


def test_six_transition_shared_dw_renders():
    ir, relation = six_transition_fixture()
    assert ir is base_fixture()[0]
    base_chain = base_fixture()[1].dependent_chain_plan
    chain = relation.dependent_chain_plan
    segment = next(s for s in chain.segments if s.segment_id == SEGMENT)
    assert next(s for s in chain.states if s.state_id == segment.pre_state_id) == next(
        s for s in base_chain.states if s.state_id == segment.pre_state_id)
    source = render_closed_segment(ir, relation, SEGMENT)
    assert THEOREM + " 4 1 8 8 32" in source
    assert "List.zipWith" in source
    assert "hGradChunk" not in source
    assert "bw_linear_dw_split_dim2_4_g119" not in source
    assert "have houtD:fact_dw_row_consumer.Holds" in source
    # Only the two final-store definitions own execution. Writer helper proofs
    # mention that same fold repeatedly; counting every textual mention is wrong.
    baseline = render_closed_segment(*base_fixture(), SEGMENT)
    assert source.splitlines()[:4] == baseline.splitlines()[:4]
    assert source.count("@[irreducible] private def") == 2


def mutate_certificate(relation, **changes):
    old = relation.certificates[-1]
    cert = replace(old, **changes)
    old_t = relation.transition_specs[-1]
    transition = replace(old_t, pre_facts=tuple(sorted((cert.gradient_fact, cert.activation_fact,
        cert.weight_fact))), post_facts=(cert.output_fact,), certificate_digest=_typed_certificate_digest(cert))
    chain = relation.dependent_chain_plan
    chain = replace(chain, relation_facts=tuple(replace(r, source=cert.output_fact)
        if r.source == old.output_fact else r for r in chain.relation_facts))
    return replace(relation, certificates=(*relation.certificates[:-1], cert),
        transition_specs=(*relation.transition_specs[:-1], transition), dependent_chain_plan=chain)


@pytest.mark.parametrize("mutation", ["record_axis", "source_axis", "digest", "writer", "rank", "roles"])
def test_malformed_dw_rejected(mutation):
    ir, relation = six_transition_fixture()
    if mutation == "record_axis":
        chain = relation.dependent_chain_plan
        relation = replace(relation, dependent_chain_plan=replace(chain,
            relation_facts=(*chain.relation_facts[:-1], replace(chain.relation_facts[-1], gather_dim=1))))
    elif mutation == "source_axis":
        relation = mutate_certificate(relation, output_fact=replace(relation.certificates[-1].output_fact, gather_dim=1))
    elif mutation == "digest":
        relation = replace(relation, transition_specs=(*relation.transition_specs[:-1],
            replace(relation.transition_specs[-1], certificate_digest="invalid")))
    elif mutation == "writer":
        relation = mutate_certificate(relation, sm_step_id="sm:0:1")
    elif mutation == "rank":
        relation = mutate_certificate(relation, rank_count=3)
    else:
        cert = relation.certificates[-1]
        relation = mutate_certificate(relation, gradient_fact=cert.weight_fact, weight_fact=cert.gradient_fact)
    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, SEGMENT)


def witness_source():
    """Return exact six-transition conditional frame source; never write Lean.

    This is a local pre-state -> post-state certificate over the original GPT
    graph declarations, not an external-initial-state or whole-model theorem.
    """
    from types import SimpleNamespace
    from trainverify.bridge_emitter.composer import render_closed_relation_declarations

    ir, relation = six_transition_fixture()
    chain = relation.dependent_chain_plan
    segment = next(s for s in chain.segments if s.segment_id == SEGMENT)
    states = tuple(s for s in chain.states if s.state_id in
                   (segment.pre_state_id, segment.post_state_id))
    live = {fid for s in states for fid in s.fact_ids}
    # Internal produced-and-consumed facts need declarations too, but are not
    # additional pre-state assumptions.
    used_sources = {f for t in relation.transition_specs
                    if t.transition_id in segment.transition_ids
                    for f in (*t.pre_facts, *t.post_facts)}
    live.update(f.fact_id for f in chain.relation_facts if f.source in used_sources)
    # A declaration-only view: preserve every live fact and the exact anchor.
    universe = SimpleNamespace(complete=True, states=states, anchor_fact=chain.anchor_fact,
        relation_facts=tuple(f for f in chain.relation_facts if f.fact_id in live),
        authority_facts=tuple(f for f in chain.authority_facts if f.fact_id in live))
    namespace = "DwRowReconstructionConsumer"
    declarations = render_closed_relation_declarations(universe, namespace)
    imports = (ir.public_statement_module, "denote.KRankBWLinearDxRow",
               "denote.KRankBWLinearDwRowGeneral")
    return ("\n".join("import " + module for module in imports) + "\n" + declarations
        + f"\nnamespace TrainVerify.Denote.{namespace}\nnoncomputable section\n"
        + render_closed_segment(ir, relation, SEGMENT)
        + f"\n#print axioms {SEGMENT}\nend\nend TrainVerify.Denote.{namespace}\n")


def test_witness_returns_exact_conditional_frame_source():
    source = witness_source()
    assert source == witness_source()
    assert render_closed_segment(*six_transition_fixture(), SEGMENT) in source
    assert "import denote.KRankBWLinearDwRowGeneral" in source
    assert "fact_dw_row_consumer : RelationFact" in source
    assert "sorry" not in source
