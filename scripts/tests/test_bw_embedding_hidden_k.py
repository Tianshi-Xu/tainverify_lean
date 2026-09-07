from types import SimpleNamespace
from dataclasses import replace
from pathlib import Path
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal


def matcher_fixture(k=2,b=1,s=16,v=256,d=32):
    full_g,local_g=(b,s,d*k),(b,s,d)
    full_w,local_w=(v,d*k),(v,d)
    ids=(b,s)
    sm=SimpleNamespace(step_id='sm:0:0',side='sm',rank=0,op='BW_embedding',
        input_bindings=('sm:g:0','init:2','init:3'),input_shapes=(full_g,ids,full_w),
        output_shape=full_w,parameters=())
    pms=tuple(SimpleNamespace(step_id=f'pm:{r}:0',side='pm',rank=r,op='BW_embedding',
        input_bindings=(f'pm:g:{r}','init:2',f'init:{100+r}'),
        input_shapes=(local_g,ids,local_w),output_shape=local_w,parameters=()) for r in range(k))
    weight=LineageGoal(3,list(full_w),[(r,100+r) for r in range(k)],[list(local_w) for _ in range(k)],gatherDim=1)
    ir=SimpleNamespace(pm_num_ranks=k,init_lineages={
        2:LineageGoal(2,list(ids),[(0,2)],[list(ids)]),3:weight})
    plan=SimpleNamespace(steps=(sm,*pms))
    return plan,ir,(sm.step_id,*(p.step_id for p in pms))


def normalize(plan,ir,frontier):
    sink=[]
    result=rc.normalize_relation_frontiers(plan,(frontier,),('sharded',),
        rules=('bw_embedding_hidden_k','bw_embedding_vocab_k'),goal_ir=ir,certificate_sink=sink)
    return sink,result


@pytest.mark.parametrize('dims',[(2,1,16,256,32),(4,1,16,256,16),(3,2,5,13,7),(1,3,2,11,5)])
def test_hidden_backward_embedding_preserves_value_roles(dims):
    plan,ir,frontier=matcher_fixture(*dims)
    certs,(frontiers,layouts)=normalize(plan,ir,frontier)
    assert len(certs)==1
    c=certs[0]
    assert c.rule_id=='bw-embedding-hidden-sharded-k-rank'
    assert c.gradient_fact.gather_dim==2
    assert c.weight_fact.gather_dim==c.output_fact.gather_dim==1
    assert c.ids_fact.step_triple==('init:2','init:2')
    assert c.gradient_fact.step_triple==('sm:g:0',*(f'pm:g:{r}' for r in range(dims[0])))
    assert set(frontiers)=={c.gradient_fact.step_triple,c.ids_fact.step_triple,c.weight_fact.step_triple}


@pytest.mark.parametrize('mutation',['rank','world','gradient','weight','output','ids-shape',
    'ids-value','ids-lineage','weight-order','weight-axis','weight-lineage-shape','offset','arity'])
def test_hidden_embedding_rejects_invalid_authority(mutation):
    plan,ir,f=matcher_fixture(3,2,5,13,7)
    assert normalize(plan,ir,f)[0]
    sm,*pms=plan.steps
    if mutation=='rank':pms[-1].rank=0
    elif mutation=='world':ir.pm_num_ranks=4
    elif mutation=='gradient':pms[-1].input_shapes=((2,6,7),*pms[-1].input_shapes[1:])
    elif mutation=='weight':pms[-1].input_shapes=(*pms[-1].input_shapes[:2],(14,7))
    elif mutation=='output':pms[-1].output_shape=(13,8)
    elif mutation=='ids-shape':sm.input_shapes=(sm.input_shapes[0],(1,10),sm.input_shapes[2])
    elif mutation=='ids-value':pms[-1].input_bindings=(pms[-1].input_bindings[0],'init:99',pms[-1].input_bindings[2])
    elif mutation=='ids-lineage':ir.init_lineages[2].tps=[(0,99)]
    elif mutation=='weight-order':ir.init_lineages[3].tps.reverse()
    elif mutation=='weight-axis':ir.init_lineages[3].gatherDim=0
    elif mutation=='weight-lineage-shape':
        ir.init_lineages[3].tsShape=[14,21];ir.init_lineages[3].tpShapes=[[14,7]]*3
    elif mutation=='offset':pms[-1].parameters=(1,)
    else:pms[-1].input_bindings=pms[-1].input_bindings[:2]
    with pytest.raises(rc.RelationCompositionError):normalize(plan,ir,f)



@pytest.mark.parametrize('dims',[(1,3,2,11,5),(2,1,16,256,32),(3,2,5,13,7),(4,1,16,256,16),(5,2,3,17,11)])
def test_hidden_renderer_and_top_level_dispatch(dims):
    from scripts.tests.bw_embedding_hidden_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel,sid=renderer_fixture(*dims)
    rel.dependent_chain_plan.complete=True
    src=render_closed_segment(ir,rel,sid)
    assert 'bw_embedding_hidden_allGather_rank3' in src
    assert src.count('private def segment_000000_sm_final')==1
    assert src.count('private def segment_000000_pm_final')==1


@pytest.mark.parametrize('mutation',['source-axis','record-axis','rank','ids','parameter','clobber','dimension','duplicate'])
def test_hidden_renderer_rejects_coherent_mutations(mutation):
    from scripts.tests.bw_embedding_hidden_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.bw_embedding_hidden_renderer import render_closed_k_rank_bw_embedding_hidden_segment as render
    ir,rel,sid=renderer_fixture(3,2,5,13,7)
    assert render(ir,rel,sid)
    c=rel.certificates[0]
    if mutation=='source-axis':
        old=c.output_fact;new=replace(old,gather_dim=0)
        c=replace(c,output_fact=new)
        rel.certificates=(c,)
        rel.transition_specs=(replace(rel.transition_specs[0],post_facts=(new,),certificate_digest=_typed_certificate_digest(c)),)
        rel.dependent_chain_plan.relation_facts=tuple(replace(r,source=new) if r.source==old else r for r in rel.dependent_chain_plan.relation_facts)
    elif mutation=='record-axis':
        rel.dependent_chain_plan.relation_facts=tuple(replace(r,gather_dim=0) if r.source==c.output_fact else r for r in rel.dependent_chain_plan.relation_facts)
    elif mutation=='rank':ir.pm_nodes[3].rank=0
    elif mutation=='ids':ir.pm_nodes[3].ins[1]=99
    elif mutation=='parameter':ir.pm_nodes[3].params=[0]
    elif mutation=='clobber':ir.pm_nodes[0].outs=[ir.pm_nodes[1].ins[0]]
    elif mutation=='duplicate':rel.certificates=(c,c)
    else:
        c=replace(c,shard_hidden=8);rel.certificates=(c,)
        rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(c)),)
    with pytest.raises(ValueError):render(ir,rel,sid)


def combined_witness_source():
    from scripts.tests.bw_embedding_hidden_witness import witness_source
    sources=[witness_source(*dims) for dims in [(1,3,2,11,5),(2,1,16,256,32),(3,2,5,13,7),(4,1,16,256,16),(5,2,3,17,11)]]
    imports=list(dict.fromkeys(l for src in sources for l in src.splitlines() if l.startswith('import ')))
    return '\n'.join(imports)+'\n'+'\n'.join('\n'.join(l for l in src.splitlines() if not l.startswith('import ')) for src in sources)+'\n'


def test_hidden_checked_in_witness_matches_generator():
    p=Path(__file__).resolve().parents[2]/'trainverify/denote/GeneratedBWEmbeddingHiddenWitness.lean'
    assert p.read_text()==combined_witness_source()


def test_hidden_renderer_accepts_parser_omitted_empty_params():
    from scripts.tests.bw_embedding_hidden_witness import renderer_fixture
    from trainverify.bridge_emitter.bw_embedding_hidden_renderer import render_closed_k_rank_bw_embedding_hidden_segment as render
    ir,rel,sid=renderer_fixture()
    for node in (*ir.sm_nodes,*ir.pm_nodes):
        if node.op=='BW_embedding':node.params=None
    assert render(ir,rel,sid)


def test_hidden_renderer_preserves_public_anchor():
    from scripts.tests.bw_embedding_hidden_witness import renderer_fixture
    from trainverify.bridge_emitter.bw_embedding_hidden_renderer import render_closed_k_rank_bw_embedding_hidden_segment as render
    ir,rel,sid=renderer_fixture()
    chain=rel.dependent_chain_plan
    chain.anchor_fact=rc.ClosedTensorShapeFactRecord('public_anchor','sm',1,(1,16,64),1)
    chain.states=tuple(replace(st,fact_ids=st.fact_ids+('public_anchor',)) for st in chain.states)
    assert render(ir,rel,sid)
    ir.sm_nodes[0].outs=[1]
    with pytest.raises(ValueError,match='overwrites'):render(ir,rel,sid)
