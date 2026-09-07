from dataclasses import replace
import pytest
from scripts.tests.bw_linear_dw_column_general_witness import CASES,THEOREM,renderer_fixture,render,witness_source
from trainverify.bridge_emitter.composer import _typed_certificate_digest


@pytest.mark.parametrize("case",CASES)
@pytest.mark.parametrize("dual",(False,True))
@pytest.mark.parametrize("with_view",(False,True))
def test_general_column_positive(case,dual,with_view):
    ir,rel=renderer_fixture(*case,dual=dual,sparse=True,with_view=with_view)
    source=render(ir,rel,"segment_000000")
    assert f"{THEOREM} {' '.join(map(str,case))}" in source
    assert "(by decide) (by decide) (by decide) (by decide) (by decide)" in source
    assert "FW_neg" in source
    assert source.count("private def segment_000000_sm_final")==1
    assert source.count("private def segment_000000_pm_final")==1
    assert "input_allGatherPrimDimN" not in source


@pytest.mark.parametrize("dual",(False,True))
@pytest.mark.parametrize("mutation",("axis","rank","roles","future","stale","frame","params","anchor"))
def test_rejects_coherent_mutations(dual,mutation):
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter import relation_compiler as rc
    ir,rel=renderer_fixture(3,2,5,7,11,dual=dual,sparse=True)
    assert THEOREM in render(ir,rel,"segment_000000")
    chain=rel.dependent_chain_plan
    g,x,w=chain.relation_facts[:3]
    c=rel.certificates[-1]
    if mutation=="rank": ir.pm_num_ranks=2
    elif mutation=="roles": c=replace(c,activation_fact=w.source,weight_fact=x.source)
    elif mutation=="params": ir.pm_nodes[0].params=()
    elif mutation=="frame": ir.pm_nodes[1].outs=[x.pm_tids[0]]
    elif mutation=="anchor":
        anchor=rc.ClosedTensorShapeFactRecord("anchor","sm",9011,(1,),9011)
        chain.anchor_fact=anchor
        chain.authority_facts=()
        chain.states=tuple(replace(s,fact_ids=(*s.fact_ids,"anchor")) for s in chain.states)
    else:
        if mutation=="axis": xf=replace(x.source,gather_dim=1)
        else:
            ir.pm_nodes.append(Node(0,"FW_neg",[9008],[x.pm_tids[0]],[]))
            xf=replace(x.source,step_triple=(x.source.step_triple[0],f"pm:{len(ir.pm_nodes)-1}:0",*x.source.step_triple[2:]))
            if mutation=="stale":
                ir.pm_nodes[1].outs=[x.pm_tids[1]]
                xf=x.source
        chain.relation_facts=tuple(replace(r,source=xf,gather_dim=xf.gather_dim) if r.fact_id==x.fact_id else r for r in chain.relation_facts)
        c=replace(c,activation_fact=xf)
        if dual:
            dc=replace(rel.certificates[0],input_facts=(g.source,xf,w.source))
            rel.certificates=(dc,c)
            rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=tuple(sorted(dc.input_facts)),certificate_digest=_typed_certificate_digest(dc)),rel.transition_specs[-1])
    rel.certificates=(*rel.certificates[:-1],c)
    rel.transition_specs=(*rel.transition_specs[:-1],replace(rel.transition_specs[-1],pre_facts=tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),certificate_digest=_typed_certificate_digest(c)))
    with pytest.raises(ValueError):render(ir,rel,"segment_000000")


@pytest.mark.parametrize("b,s",((2,8),(1,16),(3,12)))
def test_mixed_consumer(b,s):
    from scripts.tests.bw_linear_dw_column_general_witness import mixed_witness_source
    source=mixed_witness_source(b,s)
    assert f"{THEOREM} 4 {b} {s} 7 8" in source
    assert f"bw_linear_3d_snd_shape {b} {s} 7 8" in source
    assert "allGatherPrimDimN_allToAllPrimWithDims_ofFn" in source


@pytest.mark.parametrize("dual",(False,True))
def test_none_params_and_retained_anchor(dual):
    from trainverify.bridge_emitter import relation_compiler as rc
    ir,rel=renderer_fixture(dual=dual,sparse=True)
    chain=rel.dependent_chain_plan
    chain.anchor_fact=rc.ClosedTensorShapeFactRecord("anchor","sm",9999,(1,),9999)
    chain.authority_facts=()
    chain.states=tuple(replace(s,fact_ids=(*s.fact_ids,"anchor")) for s in chain.states)
    for n in (*ir.sm_nodes,*ir.pm_nodes):
        if n.op=="BW_linear":n.params=None
    assert THEOREM in render(ir,rel,"segment_000000")


@pytest.mark.parametrize("mutation",("rank","future","roles","frame"))
def test_mixed_rejects_coherent_authority(mutation):
    from scripts.tests.bw_linear_dw_column_general_witness import mixed_renderer_fixture
    from trainverify.bridge_emitter.bw_linear_gather_view_alltoall_renderer import render_closed_bw_linear_gather_view_alltoall_segment as mixed_render
    from trainverify.bridge_emitter.parser import Node
    ir,rel=mixed_renderer_fixture()
    assert THEOREM in mixed_render(ir,rel,"segment_000000")
    c=rel.certificates[1]
    if mutation=="rank":ir.pm_num_ranks=3
    elif mutation=="roles":c=replace(c,activation_fact=c.weight_fact,weight_fact=c.activation_fact)
    elif mutation=="frame":ir.pm_nodes[4].outs=[2000]
    else:
        x=rel.dependent_chain_plan.relation_facts[1]
        ir.pm_nodes.append(Node(0,"FW_neg",[8000],[2000],[]))
        xf=replace(x.source,step_triple=(x.source.step_triple[0],"pm:10:0",*x.source.step_triple[2:]))
        c=replace(c,activation_fact=xf)
        dc=replace(rel.certificates[0],input_facts=(c.gradient_fact,xf,c.weight_fact))
        rel.certificates=(dc,*rel.certificates[1:])
        rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=tuple(sorted(dc.input_facts)),certificate_digest=_typed_certificate_digest(dc)),*rel.transition_specs[1:])
        rel.dependent_chain_plan.relation_facts=tuple(replace(r,source=xf) if r.fact_id==x.fact_id else r for r in rel.dependent_chain_plan.relation_facts)
    rel.certificates=(rel.certificates[0],c,*rel.certificates[2:])
    rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],pre_facts=tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[2:])
    with pytest.raises(ValueError):mixed_render(ir,rel,"segment_000000")


def test_generator_is_deterministic():
    assert witness_source()==witness_source()
    assert "import denote.KRankBWLinearDwColumnGeneral" in witness_source()
