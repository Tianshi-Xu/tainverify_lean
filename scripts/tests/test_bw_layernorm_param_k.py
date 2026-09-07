from dataclasses import replace
from pathlib import Path
import pytest
from scripts.tests.test_k_rank_bw_layernorm import matcher_fixture as dx_fixture
from trainverify.bridge_emitter import relation_compiler as rc


def matcher_fixture(k=2,b=1,s=8,d=64,projection='.2.1'):
    plan,ir,_=dx_fixture(k,b,s,d)
    ir.pm_num_ranks=k
    idx=1 if projection=='.2.1' else 2
    for step in plan.steps:
        step.step_id=step.step_id.rsplit(':',1)[0]+f':{idx}'
        step.output_projection=projection
        step.output_shape=(d,)
    return plan,ir,tuple(step.step_id for step in plan.steps)


@pytest.mark.parametrize('dims',[(2,1,8,64),(4,1,4,64),(3,2,5,7),(1,3,2,5)])
@pytest.mark.parametrize('projection',['.2.1','.2.2'])
def test_layernorm_parameter_reduction_generic(dims,projection):
    plan,ir,f=matcher_fixture(*dims,projection)
    certs,_,_=rc.advance_k_rank_bw_layernorm_param_reduction_frontiers(plan,ir,(f,),('reduction',))
    assert len(certs)==1
    c=certs[0];name='dgamma' if projection=='.2.1' else 'dbeta'
    assert c.rule_id==f'bw-layernorm-{name}-sequence-reduction-k-rank'
    assert c.lean_theorem==f'TrainVerify.Denote.bw_layernorm_{name}_sequence_reduction_rank3'
    assert c.gradient_fact.gather_dim==c.activation_fact.gather_dim==1
    assert c.output_fact.layout=='reduction'


@pytest.mark.parametrize('mutation',['rank','world','shape','gamma-shape','gamma-value','params','projection'])
def test_layernorm_param_rejects_mismatched_authority(mutation):
    plan,ir,f=matcher_fixture(3,2,5,7)
    assert rc.advance_k_rank_bw_layernorm_param_reduction_frontiers(plan,ir,(f,),('reduction',))[0]
    sm,*pms=plan.steps
    if mutation=='rank':pms[-1].rank=0
    elif mutation=='world':ir.pm_num_ranks=4
    elif mutation=='shape':pms[-1].input_shapes=((2,6,7),*pms[-1].input_shapes[1:])
    elif mutation=='gamma-shape':ir.init_lineages[700].tsShape=[8];ir.init_lineages[700].tpShapes=[[8]]
    elif mutation=='gamma-value':pms[-1].input_bindings=(*pms[-1].input_bindings[:2],'init:999',pms[-1].input_bindings[3])
    elif mutation=='params':pms[-1].parameters=(1,)
    else:pms[-1].output_projection='.2.2'
    if mutation=='projection':
        assert not rc.advance_k_rank_bw_layernorm_param_reduction_frontiers(plan,ir,(f,),('reduction',))[0]
    else:
        with pytest.raises(rc.RelationCompositionError):rc.advance_k_rank_bw_layernorm_param_reduction_frontiers(plan,ir,(f,),('reduction',))


@pytest.mark.parametrize('projection',['.2.1','.2.2'])
def test_parameter_width_one_keeps_scalar_reduction_authority(projection):
    plan,ir,f=matcher_fixture(3,2,5,1,projection)
    cert=rc.advance_k_rank_bw_layernorm_param_reduction_frontiers(plan,ir,(f,),('reduction',))[0][0]
    assert cert.gamma_fact.layout==cert.beta_fact.layout=='reduction'


CASES=[(1,2,3,7,('dgamma',)),(2,1,8,64,('dbeta',)),(3,2,3,7,('dgamma','dbeta')),
       (4,1,4,64,('dx','dgamma','dbeta')),(5,2,3,7,('dx','dgamma')),
       (2,3,2,5,('dx','dbeta')),(3,2,3,1,('dx','dgamma','dbeta'))]


@pytest.mark.parametrize('case',CASES)
def test_parameter_projection_subsets_render(case):
    from scripts.tests.bw_layernorm_param_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel,sid=renderer_fixture(*case)
    src=render_closed_segment(ir,rel,sid)
    for name in case[-1]:
        if name!='dx':assert f'bw_layernorm_{name}_sequence_reduction_rank3' in src
    assert src.count('private def segment_000000_sm_final')==1
    assert src.count('private def segment_000000_pm_final')==1
    assert 'rw [hfinal, hout_nodes]' not in src


@pytest.mark.parametrize('mutation',['source-axis','record-shape','rank','gamma-value','params','anchor-clobber','projection'])
def test_parameter_renderer_rejects_coherent_mutation(mutation):
    from scripts.tests.bw_layernorm_param_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel,sid=renderer_fixture(3,2,3,7,('dgamma','dbeta'))
    assert render_closed_segment(ir,rel,sid)
    c=rel.certificates[0]
    if mutation=='source-axis':
        old=c.gradient_fact;new=replace(old,gather_dim=2)
        rel.certificates=tuple(replace(z,gradient_fact=new) for z in rel.certificates)
        rel.transition_specs=tuple(replace(t,pre_facts=tuple(sorted(new if f==old else f for f in t.pre_facts)),certificate_digest=_typed_certificate_digest(z)) for t,z in zip(rel.transition_specs,rel.certificates))
        rel.dependent_chain_plan.relation_facts=tuple(replace(f,source=new) if f.source==old else f for f in rel.dependent_chain_plan.relation_facts)
    elif mutation=='record-shape':
        rel.dependent_chain_plan.relation_facts=tuple(replace(f,shard_shape=(8,)) if f.source==c.output_fact else f for f in rel.dependent_chain_plan.relation_facts)
    elif mutation=='rank':ir.pm_nodes[3].rank=0
    elif mutation=='gamma-value':ir.pm_nodes[3].ins[2]=99
    elif mutation=='params':ir.pm_nodes[3].params=[1]
    elif mutation=='anchor-clobber':ir.sm_nodes[0].outs=[rel.dependent_chain_plan.anchor_fact.tid]
    else:
        c=replace(c,projection='.2.2');rel.certificates=(c,*rel.certificates[1:])
        rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    with pytest.raises(ValueError):render_closed_segment(ir,rel,sid)


def case_witness_sources():
    from scripts.tests.bw_layernorm_param_witness import witness_source
    return {f'GeneratedBWLayernormParamCase{index}.lean': witness_source(*case)
            for index, case in enumerate(CASES)}


def combined_witness_source():
    return ''.join(f'import denote.{Path(name).stem}\n' for name in case_witness_sources())


def test_param_checked_in_witness():
    root=Path(__file__).resolve().parents[2]/'trainverify/denote'
    assert (root/'GeneratedBWLayernormParamWitness.lean').read_text()==combined_witness_source()
    for name, source in case_witness_sources().items():
        assert (root/name).read_text()==source


def test_writer_transport_is_abstracted_once_per_segment():
    from scripts.tests.bw_layernorm_param_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel,sid=renderer_fixture(4,1,4,64,('dx','dgamma','dbeta'))
    source=render_closed_segment(ir,rel,sid)
    helper=f'{sid}_four_input_middle_writer'
    assert source.count(f'private theorem {helper}')==1
    assert source.count(f'exact {helper} ')==len(rel.certificates)*(1+ir.pm_num_ranks)
    assert source.count('exact hprefix.trans (congrArg')==1
