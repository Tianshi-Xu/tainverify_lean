from dataclasses import replace
import importlib.util
import pytest
from scripts.tests.unflatten_output_linear_witness import renderer_fixture,witness_source
from trainverify.bridge_emitter import composer


def render(ir,rel,sid):
    if importlib.util.find_spec('trainverify.bridge_emitter.unflatten_output_linear_renderer') is None:
        return composer.render_closed_segment(ir,rel,sid)
    from trainverify.bridge_emitter.unflatten_output_linear_renderer import render_closed_unflatten_output_linear_segment
    return render_closed_unflatten_output_linear_segment(ir,rel,sid)


def test_actual_family_baseline():
    ir,rel,sid=renderer_fixture()
    assert tuple(t.rule_id for t in rel.transition_specs)==('fw-view-unflatten-sequence-sharded-k-rank','linear-output-sharded-k-rank','linear-output-sharded-k-rank')
    assert [t.sm_node_indices for t in rel.transition_specs]==[(2,),(0,),(1,)]
    source=render(ir,rel,sid)
    assert source.count('ClosedDepSegmentCertificate')==1
    assert source.count('@[irreducible] private def')==2
    assert source.count('applyNode_fw_view_out')==3
    assert source.count('applyNode_fw_linear_out')==6

@pytest.mark.parametrize('k',(2,3,4))
@pytest.mark.parametrize('counts',((1,2),(2,1),(2,3)))
def test_dynamic_interleaved_tuples(k,counts):
    ir,rel,sid=renderer_fixture(k,b=3,s=2,n=4,d=5,unflatten_count=counts[0],linear_count=counts[1])
    src=render(ir,rel,sid)
    assert src.count('applyNode_fw_view_out')==counts[0]*(k+1)
    assert src.count('applyNode_fw_linear_out')==counts[1]*(k+1)
    assert src.count('RelationState.Holds.fold_frame')==1
    assert src.count('@[irreducible] private def')==2
    # Tuple order is not graph execution order and does not change bytes.
    rel.transition_specs=tuple(reversed(rel.transition_specs))
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=tuple(reversed(seg.transition_ids))),)
    assert render(ir,rel,sid)==src


@pytest.mark.parametrize('mutation',('rank','params','roles','axis','source','rank_order','protected','anchor','duplicate','missing','dependency','range'))
def test_coherent_negative_after_valid(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel,sid=renderer_fixture(3)
    assert render(ir,rel,sid)
    chain=rel.dependent_chain_plan
    if mutation=='rank':ir.pm_nodes[0].rank=2
    elif mutation=='params':ir.sm_nodes[2].params[-1]+=1
    elif mutation=='roles':ir.sm_nodes[0].ins.reverse()
    elif mutation in ('axis','source'):
        old=chain.relation_facts[0]
        source=replace(old.source,gather_dim=2) if mutation=='axis' else replace(old.source,step_triple=('init:99999',*old.source.step_triple[1:]))
        chain.relation_facts=(replace(old,source=source,gather_dim=2 if mutation=='axis' else old.gather_dim),*chain.relation_facts[1:])
        c=replace(rel.certificates[0],input_fact=source)
        rel.certificates=(c,*rel.certificates[1:])
        rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=(source,),certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    elif mutation=='rank_order':
        c=rel.certificates[0];t=rel.transition_specs[0]
        c=replace(c,pm_step_ids=tuple(reversed(c.pm_step_ids)))
        rel.certificates=(c,*rel.certificates[1:])
        rel.transition_specs=(replace(t,pm_node_indices=tuple(reversed(t.pm_node_indices)),certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    elif mutation in ('protected','anchor'):
        from trainverify.bridge_emitter.parser import Node
        side='pm' if mutation=='protected' else 'sm'
        nodes=ir.pm_nodes if side=='pm' else ir.sm_nodes
        nodes.append(Node(0,'FW_view',[997],[998 if side=='pm' else 999],[1]))
        seg=chain.segments[0];bounds=(0,len(nodes))
        chain.segments=(replace(seg,**{side+'_range':bounds}),)
    elif mutation=='duplicate':rel.certificates=(*rel.certificates,rel.certificates[0])
    elif mutation=='missing':rel.certificates=rel.certificates[1:]
    elif mutation=='dependency':chain.states=(replace(chain.states[0],fact_ids=tuple(f for f in chain.states[0].fact_ids if f!='x0')),chain.states[1])
    else:chain.segments=(replace(chain.segments[0],pm_range=(0,2)),)
    with pytest.raises(ValueError):render(ir,rel,sid)


def test_sm_pm_numeric_tid_overlap_is_valid():
    ir,rel,sid=renderer_fixture()
    assert render(ir,rel,sid)
    # SM and PM are separate stores: reusing a PM output's number on SM
    # does not overwrite that PM tensor.
    view=rel.certificates[0];linear=rel.certificates[1]
    records=rel.dependent_chain_plan.relation_facts
    view_record=next(r for r in records if r.source==view.output_fact)
    linear_record=next(r for r in records if r.source==linear.output_fact)
    tid=linear_record.pm_tids[0]
    ir.sm_nodes[int(view.sm_step_id.split(':')[1])].outs=[tid]
    rel.dependent_chain_plan.relation_facts=tuple(replace(r,sm_tid=tid) if r==view_record else r for r in records)
    assert render(ir,rel,sid)


@pytest.mark.parametrize('suffix,kwargs',[
    ('0',dict(k=1,unflatten_count=1,linear_count=1)),
    ('1',dict(k=2,unflatten_count=1,linear_count=2)),
    ('2',dict(k=3,unflatten_count=2,linear_count=1)),
    ('3',dict(k=4,unflatten_count=2,linear_count=3)),
    ('Overlap',dict(overlap_ids=True)),
])
def test_kernel_witness_exact_bytes(suffix,kwargs):
    from pathlib import Path
    file=Path(__file__).resolve().parents[2]/'trainverify'/'denote'/f'GeneratedUnflattenOutput{suffix}.lean'
    assert file.read_text()==witness_source(**kwargs)


def test_exact_witness_api():
    source=witness_source(k=3,b=2,s=3,n=2,d=5,unflatten_count=2,linear_count=2)
    assert source==witness_source(k=3,b=2,s=3,n=2,d=5,unflatten_count=2,linear_count=2)
    assert '#print axioms segment_000000' in source
    assert 'sorry' not in source and 'axiom ' not in source
    assert 'import denote.KRankViewUnflatten' in source

@pytest.mark.parametrize('k',(2,4))
def test_previous_frame_inputs(k):
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel,sid=renderer_fixture(k)
    chain=rel.dependent_chain_plan
    inp=chain.relation_facts[0]
    ir.sm_nodes.insert(0,Node(0,'FW_view',[777], [inp.sm_tid],list(inp.full_shape)))
    ir.pm_nodes[:0]=[Node(r,'FW_view',[777+r],[tid],list(inp.shard_shape)) for r,tid in enumerate(inp.pm_tids)]
    def shift(ref):
        side,*parts=ref.split(':')
        if side=='init':return ref
        return f'{side}:{int(parts[0])+(1 if side=="sm" else k)}:{parts[1]}'
    sources={}
    for record in chain.relation_facts:
        f=record.source
        sources[f]=replace(f,step_triple=tuple(map(shift,f.step_triple)))
    sources[inp.source]=replace(inp.source,step_triple=('sm:0:0',*(f'pm:{r}:0' for r in range(k))))
    chain.relation_facts=tuple(replace(r,source=sources[r.source]) for r in chain.relation_facts)
    certs=[];ts=[]
    for c,t in zip(rel.certificates,rel.transition_specs):
        fields={'input_fact':sources[c.input_fact]} if t.rule_id.startswith('fw-view') else {'activation_fact':sources[c.activation_fact],'weight_fact':sources[c.weight_fact]}
        c=replace(c,**fields,output_fact=sources[c.output_fact],sm_step_id=shift(c.sm_step_id),pm_step_ids=tuple(map(shift,c.pm_step_ids)))
        certs.append(c)
        ts.append(replace(t,pre_facts=tuple(sorted(sources[f] for f in t.pre_facts)),post_facts=tuple(sources[f] for f in t.post_facts),sm_node_indices=tuple(i+1 for i in t.sm_node_indices),pm_node_indices=tuple(i+k for i in t.pm_node_indices),certificate_digest=_typed_certificate_digest(c)))
    rel.certificates=tuple(certs);rel.transition_specs=tuple(ts)
    seg=chain.segments[0]
    chain.segments=(replace(seg,sm_range=(1,len(ir.sm_nodes)),pm_range=(k,len(ir.pm_nodes))),)
    assert render(ir,rel,sid).count('ClosedDepSegmentCertificate')==1
