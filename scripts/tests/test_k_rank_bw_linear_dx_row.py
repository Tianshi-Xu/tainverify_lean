from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal


def matcher_fixture(k=3, b=2, s=5, o=7, i=11):
    gradient, piece, activation, weight = (b,s,k*o), (b,s,o), (b,s,i), (k*o,i)
    sm=SimpleNamespace(step_id='sm:0:0',op='BW_linear',side='sm',rank=0,
        output_projection='.1',parameters=(),input_bindings=('sm:g','sm:x','init:300'),
        input_shapes=(gradient,activation,weight),output_shape=activation)
    pms=tuple(SimpleNamespace(step_id=f'pm:{r}:0',op='BW_linear',side='pm',rank=r,
        output_projection='.1',parameters=(),input_bindings=(f'pm:g:{r}','pm:x',f'init:{400+r}'),
        input_shapes=(piece,activation,(o,i)),output_shape=activation) for r in range(k))
    ir=SimpleNamespace(pm_num_ranks=k,init_lineages={300:LineageGoal(300,list(weight),
        [(r,400+r) for r in range(k)],[list((o,i)) for _ in range(k)],gatherDim=0)})
    return SimpleNamespace(steps=(sm,*pms)),ir,(sm.step_id,*(x.step_id for x in pms))


def renderer_fixture(k=3,b=2,s=5,o=7,i=11):
    from dataclasses import replace
    from scripts.tests.test_k_rank_bw_sum import _bw_linear_dx_renderer_fixture
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=_bw_linear_dx_renderer_fixture(k)
    g,x,w,out=rel.dependent_chain_plan.relation_facts
    rel.dependent_chain_plan.relation_facts=(
        replace(g,full_shape=(b,s,k*o),shard_shape=(b,s,o)),
        replace(x,full_shape=(b,s,i),shard_shape=(b,s,i)),
        replace(w,full_shape=(k*o,i),shard_shape=(o,i)),
        replace(out,full_shape=(b,s,i),shard_shape=(b,s,i)))
    c=replace(rel.certificates[0],lean_theorem='TrainVerify.Denote.bw_linear_dx_row_reduction_rank3')
    t=replace(rel.transition_specs[0],lean_theorem=c.lean_theorem,certificate_digest=_typed_certificate_digest(c))
    rel.certificates=(c,);rel.transition_specs=(t,)
    rel.dependent_chain_plan.authority_facts=()
    rel.dependent_chain_plan.anchor_fact=None
    rel.dependent_chain_plan.complete=True
    return ir,rel


def test_row_renderer_accepts_general_dimensions():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture()
    source=render_closed_segment(ir,rel,'segment_000000')
    assert 'bw_linear_dx_row_reduction_rank3 3 2 5 7 11' in source


def dual_renderer_fixture():
    from scripts.tests.bw_linear_dw_row_witness import renderer_fixture
    return renderer_fixture(4,1,8,8,32,with_dx=True)


def test_row_dual_renderer_consumes_generic_dx_identity():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=dual_renderer_fixture()
    assert 'bw_linear_dx_row_reduction_rank3 4 1 8 8 32' in render_closed_segment(ir,rel,'segment_000000')


def dual_witness_source():
    from scripts.tests.bw_linear_dw_row_witness import witness_source
    return witness_source(4,1,8,8,32,with_dx=True)


def witness_source(*args):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_dx_renderer import render_closed_k_rank_bw_linear_dx_segment
    ir,rel=renderer_fixture(*args)
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_dx_segment).replace(
        'SyntheticBWLayernorm','SyntheticBWLinearRow').replace(
        'SyntheticBWLinearDx','SyntheticBWLinearRow').replace(
        'import denote.KRankBWLayernorm','import denote.KRankBWLinearDxRow')


def test_row_checked_in_witnesses_match_generator():
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]/'trainverify/denote'
    assert (root/'GeneratedBWLinearDxRowWitness.lean').read_text()==witness_source()
    assert (root/'GeneratedBWLinearRowDualWitness.lean').read_text()==dual_witness_source()


def test_row_reduction_binds_weight_lineage_shapes_to_operator():
    plan,ir,frontier=matcher_fixture(3,1,8,32,32)
    ir.init_lineages[300].tsShape=[96,64]
    ir.init_lineages[300].tpShapes=[[32,64]]*3
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(frontier,),('reduction',))


@pytest.mark.parametrize('dims',[(2,1,16,32,64),(4,1,16,16,64),(3,2,5,7,11),(1,3,2,1,4),(5,2,1,3,2)])
def test_row_reduction_dimensions_are_not_a_shape_lookup(dims):
    plan,ir,frontier=matcher_fixture(*dims)
    certs,_,_=rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(frontier,),('reduction',))
    cert=certs[0]
    assert cert.rule_id=='bw-linear-dx-row-reduction-k-rank'
    assert cert.lean_theorem=='TrainVerify.Denote.bw_linear_dx_row_reduction_rank3'
    assert cert.rank_count==dims[0]
    assert cert.input_facts[0].gather_dim==2
    assert cert.input_facts[2].gather_dim==0
