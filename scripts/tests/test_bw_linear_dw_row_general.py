from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter.parser import LineageGoal
from trainverify.bridge_emitter import relation_compiler as rc


def matcher_fixture(k=2,b=1,s=16,o=32,i=64):
    fullg,localg,xshape=(b,s,o*k),(b,s,o),(b,s,i)
    fullw,localw=(o*k,i),(o,i)
    sm=SimpleNamespace(step_id='sm:0:1',side='sm',rank=0,op='BW_linear',output_projection='.2',parameters=(),
        input_bindings=('sm:g:0','sm:x:0','init:3'),input_shapes=(fullg,xshape,fullw),output_shape=fullw)
    pms=tuple(SimpleNamespace(step_id=f'pm:{r}:1',side='pm',rank=r,op='BW_linear',output_projection='.2',parameters=(),
        input_bindings=(f'pm:g:{r}','pm:x:0',f'init:{100+r}'),input_shapes=(localg,xshape,localw),output_shape=localw) for r in range(k))
    ir=SimpleNamespace(pm_num_ranks=k,init_lineages={3:LineageGoal(3,list(fullw),[(r,100+r) for r in range(k)],[list(localw)]*k,gatherDim=0)})
    return SimpleNamespace(steps=(sm,*pms)),ir,(sm.step_id,*(p.step_id for p in pms))


@pytest.mark.parametrize('dims',[(2,1,16,32,64),(4,1,16,16,64),(3,2,5,7,11),(1,3,2,5,13)])
def test_row_dw_general_matcher(dims):
    plan,ir,f=matcher_fixture(*dims)
    certs,_,_=rc.advance_k_rank_bw_linear_dw_sharded_frontiers(plan,ir,(f,),('sharded',))
    assert len(certs)==1
    c=certs[0]
    assert c.rule_id=='bw-linear-dw-output-row-sharded-k-rank'
    assert c.lean_theorem=='TrainVerify.Denote.bw_linear_dw_row_allGather_rank3'
    assert c.gradient_fact.gather_dim==2 and c.output_fact.gather_dim==0


@pytest.mark.parametrize('mutation',['rank','world','params','shared-x','weight-order','weight-shape','g-shape','x-shape'])
def test_row_dw_rejects_mismatched_authority(mutation):
    plan,ir,f=matcher_fixture(3,2,5,7,11)
    sm,*pms=plan.steps
    if mutation=='rank':pms[-1].rank=0
    elif mutation=='world':ir.pm_num_ranks=2
    elif mutation=='params':pms[-1].parameters=(1,)
    elif mutation=='shared-x':pms[-1].input_bindings=(pms[-1].input_bindings[0],'pm:x:1',pms[-1].input_bindings[2])
    elif mutation=='weight-order':ir.init_lineages[3].tps=list(reversed(ir.init_lineages[3].tps))
    elif mutation=='weight-shape':ir.init_lineages[3].tpShapes=[[7,12]]*3
    elif mutation=='g-shape':sm.input_shapes=((2,5,22),*sm.input_shapes[1:])
    else:sm.input_shapes=(sm.input_shapes[0],(3,5,11),sm.input_shapes[2])
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dw_sharded_frontiers(plan,ir,(f,),('sharded',))


def test_row_dw_generic_registry_and_compound_dispatch():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_compound_renderer
    rule='bw-linear-dw-output-row-sharded-k-rank'
    spec=rc.get_closed_rule_spec(rule)
    assert spec is not None
    assert 'TrainVerify.Denote.bw_linear_dw_row_allGather_rank3' in spec.lean_theorems
    for extras in (('bw-linear-dx-row-reduction-k-rank',),
                   ('bw-linear-dx-row-reduction-k-rank','allreduce-reconstruction-k-rank'),
                   ('bw-linear-dx-row-reduction-k-rank','bw-view-joined')):
        assert select_compound_renderer((rule,*extras))=='bw_linear_dual_renderer:render_closed_k_rank_bw_linear_dual_segment'


@pytest.mark.parametrize('k',[1,2,3,4,5])
@pytest.mark.parametrize('with_dx,tail',[(False,None),(True,None),(False,'allreduce'),(True,'allreduce'),(False,'view'),(True,'view')])
def test_row_dw_render_matrix(k,with_dx,tail):
    from scripts.tests.bw_linear_dw_row_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(k,2,5,7,11,with_dx=with_dx,tail=tail)
    source=render_closed_segment(ir,rel,'segment_000000')
    assert f'bw_linear_dw_row_allGather_rank3 {k} 2 5 7 11' in source
    assert source.count('private def segment_000000_sm_final')==1
    assert source.count('private def segment_000000_pm_final')==1


@pytest.mark.parametrize('mutation',['world','rank','source-axis','record-shape','shared-x','params','duplicate'])
def test_row_dw_renderer_rejects_mutation(mutation):
    from dataclasses import replace
    from scripts.tests.bw_linear_dw_row_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=renderer_fixture(3,2,5,7,11,with_dx=True)
    assert render_closed_segment(ir,rel,'segment_000000')
    if mutation=='world':ir.pm_num_ranks=2
    elif mutation=='rank':ir.pm_nodes[-1].rank=0
    elif mutation=='source-axis':
        old=rel.certificates[0].gradient_fact;new=replace(old,gather_dim=1)
        c=replace(rel.certificates[0],gradient_fact=new)
        rel.certificates=(c,*rel.certificates[1:])
        t=rel.transition_specs[0]
        rel.transition_specs=(replace(t,pre_facts=tuple(sorted(new if f==old else f for f in t.pre_facts)),certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    elif mutation=='record-shape':
        rel.dependent_chain_plan.relation_facts=tuple(replace(r,full_shape=(99,11)) if r.fact_id=='fact_dw' else r for r in rel.dependent_chain_plan.relation_facts)
    elif mutation=='shared-x':ir.pm_nodes[-1].ins[1]=999
    elif mutation=='params':ir.pm_nodes[-1].params=[1]
    else:rel.certificates=(*rel.certificates,rel.certificates[0])
    with pytest.raises(ValueError):render_closed_segment(ir,rel,'segment_000000')


WITNESS_CASES=[(1,False,None),(2,True,None),(3,False,'allreduce'),
               (4,True,'allreduce'),(5,False,'view'),(3,True,'view')]


def case_witness_sources():
    from scripts.tests.bw_linear_dw_row_witness import witness_source
    return {f'GeneratedBWLinearDwRowCase{n}.lean':witness_source(k,2,5,7,11,with_dx=dx,tail=tail)
            for n,(k,dx,tail) in enumerate(WITNESS_CASES)}


def test_row_dw_checked_in_witness_sources():
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]/'trainverify/denote'
    for name,src in case_witness_sources().items():
        assert (root/name).read_text()==src
