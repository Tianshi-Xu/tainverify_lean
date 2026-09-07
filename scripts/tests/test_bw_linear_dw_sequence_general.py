from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter.parser import LineageGoal
from trainverify.bridge_emitter import relation_compiler as rc


def matcher_fixture(k=2, b=1, s=8, o=64, i=64):
    fullg, fullx, w = (b,s*k,o), (b,s*k,i), (o,i)
    sm = SimpleNamespace(step_id='sm:0:1',side='sm',rank=0,op='BW_linear',
        output_projection='.2',parameters=(),input_bindings=('sm:g:0','sm:x:0','init:3'),
        input_shapes=(fullg,fullx,w),output_shape=w)
    pms = tuple(SimpleNamespace(step_id=f'pm:{r}:1',side='pm',rank=r,op='BW_linear',
        output_projection='.2',parameters=(),input_bindings=(f'pm:g:{r}',f'pm:x:{r}','init:3'),
        input_shapes=((b,s,o),(b,s,i),w),output_shape=w) for r in range(k))
    ir = SimpleNamespace(pm_num_ranks=k, init_lineages={3:LineageGoal(3,list(w),[(0,3)],[list(w)],gatherDim=0)})
    return SimpleNamespace(steps=(sm,*pms)), ir, (sm.step_id,*(p.step_id for p in pms))


@pytest.mark.parametrize('dims', [(2,1,8,64,64),(4,1,4,64,64),(3,2,5,7,11),(1,3,2,5,13)])
def test_sequence_dw_general_matcher(dims):
    plan, ir, frontier = matcher_fixture(*dims)
    certs, rewritten, layouts = rc.advance_k_rank_bw_linear_dw_reduction_frontiers(plan,ir,(frontier,),('reduction',))
    assert len(certs) == 1
    c = certs[0]
    assert c.rule_id == 'bw-linear-dw-sequence-reduction-k-rank'
    assert c.lean_theorem == 'TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3'
    assert c.rank_count == dims[0] and c.shard_dim == 1
    assert c.gradient_fact.gather_dim == c.activation_fact.gather_dim == 1
    assert c.weight_fact.step_triple == ('init:3','init:3')
    assert c.output_fact.step_triple == frontier and c.output_fact.layout == 'reduction'
    assert rewritten == (c.gradient_fact.step_triple,c.activation_fact.step_triple,c.weight_fact.step_triple)
    assert layouts == ('sharded','sharded','sharded')


@pytest.mark.parametrize('mutation', ['rank', 'world', 'params', 'shared-weight',
    'weight-tids', 'weight-axis', 'weight-full-shape', 'weight-local-shape',
    'g-shape', 'x-shape', 'output-shape', 'zero', 'indivisible'])
def test_sequence_dw_rejects_bad_authority(mutation):
    plan, ir, f = matcher_fixture(3,2,5,7,11)
    assert rc.advance_k_rank_bw_linear_dw_reduction_frontiers(plan,ir,(f,),('reduction',))[0]
    sm, *pms = plan.steps
    if mutation == 'rank': pms[-1].rank = 0
    elif mutation == 'world': ir.pm_num_ranks = 2
    elif mutation == 'params': pms[-1].parameters = (1,)
    elif mutation == 'shared-weight': pms[-1].input_bindings = (*pms[-1].input_bindings[:2],'init:4')
    elif mutation == 'weight-tids': ir.init_lineages[3].tps = [(0,4)]
    elif mutation == 'weight-axis': ir.init_lineages[3].gatherDim = 1
    elif mutation == 'weight-full-shape': ir.init_lineages[3].tsShape = [7,12]
    elif mutation == 'weight-local-shape': ir.init_lineages[3].tpShapes = [[7,12]]
    elif mutation == 'g-shape': pms[-1].input_shapes = ((2,5,8),*pms[-1].input_shapes[1:])
    elif mutation == 'x-shape': pms[-1].input_shapes = (pms[-1].input_shapes[0],(2,6,11),pms[-1].input_shapes[2])
    elif mutation == 'output-shape': pms[-1].output_shape = (7,12)
    elif mutation == 'zero': sm.input_shapes = ((0,15,7),(0,15,11),(7,11))
    else: sm.input_shapes = ((2,16,7),(2,16,11),(7,11))
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dw_reduction_frontiers(plan,ir,(f,),('reduction',))


def test_sequence_dw_registry_and_compound_routes():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_compound_renderer
    rule = 'bw-linear-dw-sequence-reduction-k-rank'
    spec = rc.get_closed_rule_spec(rule)
    assert spec.lean_theorems == ('TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3',)
    assert spec.lean_imports == ('denote.KRankBWLinearDwSequenceGeneral',)
    assert select_compound_renderer(('bw-linear-dx-sequence-sharded-k-rank',rule)) == 'bw_linear_dw_sequence_renderer:render_closed_bw_linear_dw_sequence_segment'
