from types import SimpleNamespace
import pytest
from scripts.tests.test_k_rank_bw_linear_dx_column import matcher_fixture as dx_matcher_fixture
from trainverify.bridge_emitter import relation_compiler as rc

RULE = "bw-linear-dw-input-column-sharded-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dw_input_allGatherPrimDimN_dim2_rank3"


def matcher_fixture(k=3,o=7,d=5):
    plan,ir,_=dx_matcher_fixture(k,o,d)
    for step in plan.steps:
        step.step_id=step.step_id.rsplit(":",1)[0]+":1"
        step.output_projection=".2"
        step.output_shape=step.input_shapes[2]
    return plan,ir,tuple(step.step_id for step in plan.steps)


@pytest.mark.parametrize("k,o,d",((3,7,5),(1,1,1),(4,7,5),(5,3,1),(4,32,8),(4,128,8),(4,32,32)))
def test_dw_column_matcher_positive_widths(k,o,d):
    plan,ir,frontier=matcher_fixture(k,o,d)
    certs,frontiers,layouts=rc.advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan,ir,(frontier,),("sharded",))
    assert frontiers[0]==("sm:g:0","pm:g:shared")
    assert layouts==("joined","sharded","sharded")
    assert len(certs)==1
    c=certs[0]
    assert (c.rule_id,c.lean_theorem,c.rank_count)==(RULE,THEOREM,k)
    assert c.activation_fact.gather_dim==2
    assert c.weight_fact.gather_dim==c.output_fact.gather_dim==1


@pytest.mark.parametrize("mutation",("row-axis-singleton","sequence","rank2"))
def test_dw_column_preserves_other_families(mutation):
    plan,ir,frontier=matcher_fixture(1)
    if mutation=="row-axis-singleton": ir.init_lineages[700].gatherDim=0
    elif mutation=="sequence":
        for s in plan.steps:
            g,x,w=s.input_shapes;s.input_shapes=((1,4,g[-1]),(1,4,x[-1]),w)
    else:
        for s in plan.steps:
            g,x,w=s.input_shapes;s.input_shapes=(g[1:],x[1:],w)
    certs,frontiers,layouts=rc.advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan,ir,(frontier,),("sharded",))
    assert not certs
    assert frontiers==(frontier,) and layouts==("sharded",)


@pytest.mark.parametrize("mutation",("rank","params","shared-gradient","full-gradient","local-weight","lineage-shape","lineage-ranks","arity"))
def test_dw_column_rejects_inconsistent_candidate(mutation):
    plan,ir,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="rank": pms[1].rank=0
    elif mutation=="params": pms[1].parameters=(1,)
    elif mutation=="shared-gradient": pms[1].input_bindings=("pm:other",*pms[1].input_bindings[1:])
    elif mutation=="full-gradient": sm.input_shapes=((1,8,6),*sm.input_shapes[1:])
    elif mutation=="local-weight": pms[1].input_shapes=(*pms[1].input_shapes[:2],(6,5))
    elif mutation=="lineage-shape": ir.init_lineages[700].tsShape=[6,15]
    elif mutation=="lineage-ranks": ir.init_lineages[700].tps=[(2,701),(1,702),(0,703)]
    else: pms[1].input_shapes=()
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan,ir,(f,),("sharded",))


@pytest.mark.parametrize("o,d",((0,5),(7,0),(-1,5),(7,-1)))
def test_dw_column_rejects_nonpositive(o,d):
    plan,ir,f=matcher_fixture(3,o,d)
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan,ir,(f,),("sharded",))


def witness_source(k=3,o=7,d=5,with_view=False):
    from scripts.tests.test_k_rank_bw_linear_dx_column import dual_fixture,with_view_fixture
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=with_view_fixture(True) if with_view else dual_fixture(k,o,d)
    return (fixture_source(ir,rel,render_closed_segment)
        .replace("SyntheticBWLayernorm","SyntheticBWLinearDwColumn")
        .replace("SyntheticBWLinearDxColumn","SyntheticBWLinearDwColumn")
        .replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDxColumn\nimport denote.KRankBWLinearDwColumn"))


def test_dw_column_committed_witness_matches_renderer():
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]
    assert (root/"trainverify/denote/GeneratedKRankBWLinearDwColumnWitness.lean").read_text()==witness_source()


def test_dw_column_selects_incremental_gates():
    from scripts.incremental_test_selector import select_gates
    gates=select_gates(("trainverify/denote/KRankBWLinearDwColumn.lean",),family="k-rank-bw-linear-dx-column")
    assert not gates.full_python
    assert "scripts/tests/test_k_rank_bw_linear_dw_column.py" in gates.pytest_nodes
    assert "denote.KRankBWLinearDwColumn" in gates.lean_modules
