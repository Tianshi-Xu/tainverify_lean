"""Rank3→rank4 view transport reuses the inverse of checked flattening."""
from dataclasses import replace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from scripts.tests.test_k_rank_bw_view_flatten import matcher_fixture as flat_matcher, renderer_fixture as flat_renderer


def matcher_fixture(k=2,b=1,s=8,n=4,d=16,axis=1,backward=False):
    plan,f=flat_matcher(k,b,s,n,d,axis=axis)
    for step in plan.steps:
        old_in=step.input_shapes[0];old_out=step.output_shape
        step.op="BW_view" if backward else "FW_view"
        step.output_shape=old_in;step.parameters=old_in
        step.input_shapes=(old_out,old_in) if backward else (old_out,)
        if not backward:step.input_bindings=step.input_bindings[:1]
    return plan,f


@pytest.mark.parametrize("axis",(1,2))
@pytest.mark.parametrize("case",((2,1,8,4,16),(4,1,4,4,16),(3,2,5,3,7)))
def test_unflatten_matcher(case,axis):
    plan,f=matcher_fixture(*case,axis=axis)
    certs,_,_=rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))
    assert len(certs)==1
    assert certs[0].rule_id==f"fw-view-unflatten-{'sequence' if axis==1 else 'head'}-sharded-k-rank"
    assert certs[0].input_fact.gather_dim==axis


def renderer_fixture(axis=1,backward=False):
    ir,rel=flat_renderer(axis=axis)
    inp,out=rel.dependent_chain_plan.relation_facts
    records=(replace(inp,full_shape=out.full_shape,shard_shape=out.shard_shape),replace(out,full_shape=inp.full_shape,shard_shape=inp.shard_shape))
    for i,node in enumerate(ir.sm_nodes):
        node.op="BW_view" if backward else "FW_view";node.params=list(records[1].full_shape)
        if not backward:node.ins=node.ins[:1]
    for node in ir.pm_nodes:
        node.op="BW_view" if backward else "FW_view";node.params=list(records[1].shard_shape)
        if not backward:node.ins=node.ins[:1]
    c=rel.certificates[0]
    rule=c.rule_id.replace("flatten","unflatten")
    if not backward:rule=rule.replace("bw-view","fw-view")
    c=replace(c,rule_id=rule,lean_theorem=f"TrainVerify.Denote.fw_view_unflatten_allGather_dim{axis}_rank3")
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    rel.certificates=(c,);rel.transition_specs=(replace(rel.transition_specs[0],rule_id=rule,lean_theorem=c.lean_theorem,certificate_digest=_typed_certificate_digest(c)),)
    rel.dependent_chain_plan.relation_facts=records
    return ir,rel


@pytest.mark.parametrize("axis",(1,2))
@pytest.mark.parametrize("backward",(False,True))
def test_unflatten_renderer(axis,backward):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(axis,backward)
    src=render_closed_segment(ir,rel,"segment_000000")
    assert f"fw_view_unflatten_allGather_dim{axis}_rank3" in src
    assert ("applyNode_bw_view_out" if backward else "applyNode_fw_view_out") in src


@pytest.mark.parametrize("mutation",("params","shape","axis","rank"))
def test_unflatten_rejects_malformed(mutation):
    plan,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="params":pms[0].parameters=(1,8,4,15)
    elif mutation=="shape":pms[0].input_shapes=((1,8,63),)
    elif mutation=="axis":sm.output_shape=(1,8,8,16)
    else:pms[1].rank=0
    with pytest.raises(rc.RelationCompositionError):rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))


def witness_source():
    from trainverify.bridge_emitter.composer import render_closed_segment
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    sources=[]
    for axis in (1,2):
        for bw in (False,True):
            ir,rel=renderer_fixture(axis,bw)
            src=fixture_source(ir,rel,render_closed_segment).replace("SyntheticBWLayernorm","SyntheticBWSum").replace("import denote.KRankBWLayernorm","import denote.KRankViewUnflatten")
            sources.append(src.replace("SyntheticBWSum",f"ViewUnflattenA{axis}BW{int(bw)}"))
    imports=list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


def test_unflatten_checked_in_witness():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedViewUnflattenWitness.lean"
    assert path.read_text()==witness_source()
