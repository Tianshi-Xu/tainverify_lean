"""Generator-owned positive local-linear / multi-gather fixtures (Python only)."""
from dataclasses import replace
from types import SimpleNamespace

import pytest

from scripts.tests.test_k_rank_local_linear_allgather_atomic_renderer import (
    _fixture, GATHER_RULE, GATHER_THEOREM,
)
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter.mixed_local_linear_allgather_renderer import (
    render_closed_k_rank_local_linear_allgather_segment as render,
)


def fixture(*, k=2, local_count=1, gather_count=2, intermediate=False):
    """Independent prior multiref projections, with gathers between rank writers."""
    ir, relation, segment = _fixture(k=k, count=local_count)
    chain = relation.dependent_chain_plan
    # Keep all local rank writers, then interleave independent gathers.
    old_pm = ir.pm_nodes
    ir.pm_nodes = [n for n in old_pm if n.op != "AllGatherPrim"]
    certs = list(relation.certificates[:-1])
    records = list(chain.relation_facts[:-1])
    for g, cert in enumerate(certs):
        steps = tuple(f"pm:{ir.pm_nodes.index(old_pm[int(s.split(':')[1])])}:0" for s in cert.pm_step_ids)
        post = replace(cert.output_fact, step_triple=(cert.output_fact.step_triple[0], *steps))
        certs[g] = replace(cert, pm_step_ids=steps, output_fact=post)
        records[2*g+1] = replace(records[2*g+1], source=post)
    # Prefix SM and PM multiref nodes authenticate non-initial shared sources.
    sm_prefix = [Node(0, "FW_multiref", [90], [100 + q for q in range(local_count + gather_count)], [])]
    pm_prefix = [Node(r, "FW_multiref", [190+r], [200+g*10+r for g in range(local_count+gather_count)], []) for r in range(k)]
    # Move all existing references by the prefix length.
    def shift(ref):
        side, idx, out = ref.split(":")
        return f"{side}:{int(idx)+(1 if side == 'sm' else k)}:{out}"
    for g, cert in enumerate(certs):
        pre = replace(cert.input_fact, step_triple=(f"sm:0:{g}", *(f"pm:{r}:{g}" for r in range(k))))
        post = replace(cert.output_fact, step_triple=tuple(shift(s) for s in cert.output_fact.step_triple))
        certs[g] = replace(cert, input_fact=pre, output_fact=post, sm_step_id=shift(cert.sm_step_id), pm_step_ids=tuple(shift(s) for s in cert.pm_step_ids))
        records[2*g] = replace(records[2*g], source=pre)
        records[2*g+1] = replace(records[2*g+1], source=post)
    ir.sm_nodes = sm_prefix + ir.sm_nodes
    ir.pm_nodes = pm_prefix + ir.pm_nodes
    before = list(chain.states[0].fact_ids)
    for g in range(gather_count):
        q = local_count + g
        if intermediate and g == 0:
            pre_record = records[1]
        else:
            pre = rc.RelationFactSpec("sharded", (f"sm:0:{q}", *(f"pm:{r}:{q}" for r in range(k))), gather_dim=1)
            pre_record = rc.ClosedRelationFactRecord(f"gather_input_{g}", pre, "sharded", 100+q, tuple(200+q*10+r for r in range(k)), None, None, (2,3*k,5), (2,3,5), 1)
            records.append(pre_record)
            before.append(pre_record.fact_id)
        pos = len(ir.pm_nodes) if intermediate else k + 1 + g
        ir.pm_nodes.insert(pos, Node(0, "AllGatherPrim", list(pre_record.pm_tids), [900+g], [1]))
        # Insertion shifts all already materialized PM output references.
        def bump(ref):
            p = ref.split(":")
            return f"pm:{int(p[1])+1}:{p[2]}" if p[0] == "pm" and int(p[1]) >= pos else ref
        def bump_fact(f):
            return replace(f, step_triple=tuple(bump(s) for s in f.step_triple), joined_pm_step=bump(f.joined_pm_step) if f.joined_pm_step else f.joined_pm_step)
        records = [replace(r, source=bump_fact(r.source)) for r in records]
        updated = []
        for c in certs:
            changes = dict(input_fact=bump_fact(c.input_fact), output_fact=bump_fact(c.output_fact))
            if isinstance(c, rc.KRankLocalRelationCertificate):
                changes['pm_step_ids'] = tuple(bump(s) for s in c.pm_step_ids)
            else:
                changes['pm_allgather_step'] = bump(c.pm_allgather_step)
            updated.append(replace(c, **changes))
        certs = updated
        pre_record = next(r for r in records if r.fact_id == pre_record.fact_id)
        post = rc.RelationFactSpec("joined", (pre_record.source.step_triple[0],), joined_pm_step=f"pm:{pos}:0")
        certs.append(rc.KRankAllGatherReconstructionCertificate(GATHER_RULE, k, 1, pre_record.full_shape, pre_record.shard_shape, pre_record.source, post, f"pm:{pos}:0", GATHER_THEOREM))
        records.append(rc.ClosedRelationFactRecord(f"joined_{g}", post, "joined", pre_record.sm_tid, (), None, None, pre_record.full_shape, pre_record.full_shape, joined_pm_tid=900+g))
    relation.certificates = tuple(certs)
    relation.transition_specs = rc.build_certificate_transition_specs(SimpleNamespace(), tuple(certs))
    segment.transition_ids = tuple(t.transition_id for t in relation.transition_specs)
    segment.sm_range = (1, len(ir.sm_nodes))
    segment.pm_range = (k, len(ir.pm_nodes))
    chain.relation_facts = tuple(records)
    chain.states[0].fact_ids = tuple(before)
    chain.states[1].fact_ids = tuple([f"output_{g}" for g in range(local_count)] + [f"joined_{g}" for g in range(gather_count)])
    return ir, relation, segment


def witness_source(*, k=2, local_count=1, gather_count=2, intermediate=False):
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    ir, relation, segment = fixture(k=k, local_count=local_count, gather_count=gather_count, intermediate=intermediate)
    namespace = "GeneratedLocalLinearMultiGatherWitness"
    ir.sm_graph_ref = f"TrainVerify.Denote.{namespace}.smGraph"
    ir.pm_graph_ref = f"TrainVerify.Denote.{namespace}.pmGraph"
    return "\n".join((render_closed_relation_declarations(relation.dependent_chain_plan, namespace), f"namespace TrainVerify.Denote.{namespace}", "noncomputable section", f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := [{', '.join(_node_text(n) for n in ir.sm_nodes)}] }}", f"private def pmGraph : GraphDecl := {{ numRanks := {k}, nodes := [{', '.join(_node_text(n) for n in ir.pm_nodes)}] }}", render(ir, relation, segment.segment_id), f"#print axioms {segment.segment_id}", "end", f"end TrainVerify.Denote.{namespace}", ""))


def test_stale_prior_writer_rejected_with_valid_frame_partition():
    ir,relation,segment=fixture()
    assert render(ir,relation,segment.segment_id)
    # Rebind only the local writer after inserting a prior overwrite. The
    # component footprint stays exact, but the gather source is now stale.
    ir.sm_nodes.insert(1,Node(0,'FW_contiguous',[101],[101],[]))
    cert=relation.certificates[0]
    old=cert.output_fact
    new=replace(old,step_triple=('sm:2:0',*old.step_triple[1:]))
    relation.certificates=(replace(cert,sm_step_id='sm:2:0',output_fact=new),*relation.certificates[1:])
    chain=relation.dependent_chain_plan
    chain.relation_facts=tuple(replace(r,source=new) if r.source==old else r for r in chain.relation_facts)
    relation.transition_specs=rc.build_certificate_transition_specs(SimpleNamespace(),relation.certificates)
    segment.transition_ids=tuple(t.transition_id for t in relation.transition_specs)
    segment.sm_range=(2,3)
    with pytest.raises(ValueError,match='latest writer'):
        render(ir,relation,segment.segment_id)


def test_production_dispatch_multi_gather():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,relation,segment=fixture()
    assert render_closed_segment(ir,relation,segment.segment_id)==render(ir,relation,segment.segment_id)


@pytest.mark.parametrize('i,case',list(enumerate([(2,1,2,False),(3,2,1,True),(4,2,3,False),(2,1,2,True)])))
def test_checked_in_multi_gather_exact_bytes(i,case):
    from pathlib import Path
    k,n,m,t=case
    expected=Path(__file__).resolve().parents[2]/'trainverify'/'denote'/f'GeneratedLocalMultiGather{i}.lean'
    assert expected.read_text()==witness_source(k=k,local_count=n,gather_count=m,intermediate=t)


@pytest.mark.parametrize('k', [2, 4])
def test_positive_multi_gather(k):
    ir, relation, segment = fixture(k=k)
    assert [n.op for n in ir.pm_nodes[slice(*segment.pm_range)]][:3] == ["FW_linear", "AllGatherPrim", "AllGatherPrim"]
    text = render(ir, relation, segment.segment_id)
    assert text.count(GATHER_THEOREM) == 2
    assert text.count('let smFinal :=') == text.count('let pmFinal :=') == 1
    assert 'joined_0.Holds' in text and 'joined_1.Holds' in text


@pytest.mark.parametrize("tamper", ["axis", "resolved-tid", "rank", "order", "anchor", "late-write", "duplicate"])
def test_mutations_fail_closed(tamper):
    ir, relation, segment = fixture()
    chain = relation.dependent_chain_plan
    if tamper == "axis":
        old = relation.certificates[-1].input_fact
        new = replace(old, gather_dim=0)
        relation.certificates = tuple(replace(c, input_fact=new) if c.input_fact == old else c for c in relation.certificates)
        chain.relation_facts = tuple(replace(r, source=new) if r.source == old else r for r in chain.relation_facts)
        # Coherently regenerate transition identity: digest agreement isn't authority.
        relation.transition_specs = rc.build_certificate_transition_specs(SimpleNamespace(), relation.certificates)
        segment.transition_ids = tuple(t.transition_id for t in relation.transition_specs)
    elif tamper == "resolved-tid":
        r = next(r for r in chain.relation_facts if r.fact_id == "gather_input_1")
        chain.relation_facts = tuple(replace(x, sm_tid=999) if x == r else x for x in chain.relation_facts)
        joined = next(r for r in chain.relation_facts if r.fact_id == "joined_1")
        chain.relation_facts = tuple(replace(x, sm_tid=999) if x == joined else x for x in chain.relation_facts)
    elif tamper == "rank":
        ir.pm_nodes[-1].rank = 0
    elif tamper == "order":
        segment.transition_ids = tuple(reversed(segment.transition_ids))
    elif tamper == "anchor":
        chain.anchor_fact.tid = ir.sm_nodes[-1].outs[0]
    elif tamper == "late-write":
        ir.pm_nodes[-1].outs = [ir.pm_nodes[0].outs[2]]
    else:
        relation.certificates += (relation.certificates[-1],)
    with pytest.raises(ValueError):
        render(ir, relation, segment.segment_id)


@pytest.mark.parametrize("k,n,m,intermediate", [(2,1,1,False), (3,2,1,True), (4,2,3,False), (2,1,2,True)])
def test_counts_and_generator(k,n,m,intermediate):
    text = witness_source(k=k, local_count=n, gather_count=m, intermediate=intermediate)
    assert text == witness_source(k=k, local_count=n, gather_count=m, intermediate=intermediate)
    assert text.count(GATHER_THEOREM) == m
    assert "sorry" not in text


def test_original_backend_bytes_unchanged():
    import subprocess
    source = subprocess.check_output(["git", "show", "38366919:trainverify/bridge_emitter/mixed_local_linear_allgather_renderer.py"], text=True)
    scope = {"__name__": "trainverify.bridge_emitter._baseline", "__package__": "trainverify.bridge_emitter"}
    exec(source, scope)
    for count in (1,2):
        ir, relation, segment = _fixture(k=3, count=count)
        assert render(ir, relation, segment.segment_id) == scope["render_closed_k_rank_local_linear_allgather_segment"](ir, relation, segment.segment_id)
