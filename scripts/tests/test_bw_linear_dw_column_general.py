from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from scripts.tests.test_k_rank_bw_linear_dx_column import matcher_fixture as dx_fixture


def matcher_fixture(k=2,b=1,s=16,o=64,i=32):
    plan,ir,_=dx_fixture(k,o,i,b=b,s=s)
    ir.pm_num_ranks=k
    for step in plan.steps:
        step.step_id=step.step_id.rsplit(':',1)[0]+':1'
        step.output_projection='.2'
        step.output_shape=step.input_shapes[2]
    return plan,ir,tuple(step.step_id for step in plan.steps)


@pytest.mark.parametrize('args',[(2,1,16,64,32),(4,1,16,64,16),(3,2,5,7,11),(1,3,2,1,4),(5,2,1,3,2)])
def test_column_dw_general_domain(args):
    plan,ir,f=matcher_fixture(*args)
    cs,fs,ls=rc.advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan,ir,(f,),('sharded',))
    assert len(cs)==1
    c=cs[0]
    assert c.lean_theorem=='TrainVerify.Denote.bw_linear_dw_column_allGather_rank3'
    assert c.gradient_fact.layout=='joined'
    assert c.activation_fact.gather_dim==2
    assert c.weight_fact.gather_dim==c.output_fact.gather_dim==1
    assert c.output_fact.step_triple==f


def test_column_dw_header_authority():
    plan,ir,f=matcher_fixture()
    ir.pm_num_ranks=3
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan,ir,(f,),('sharded',))
