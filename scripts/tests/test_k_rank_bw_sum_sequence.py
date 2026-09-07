"""Sequence-axis BW_sum inferred from ordered graph shapes, not model IDs."""
from dataclasses import replace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from scripts.tests.test_k_rank_bw_sum import _fixture, _renderer_fixture

RULE = "bw-sum-scalar-broadcast-dim1-k-rank"
THEOREM = "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3"


def matcher_fixture(k=3,b=2,s=5,h=7):
    plan,ir,f,_,_=_fixture(k)
    full=(b,s*k,h);shard=(b,s,h)
    for n in plan.steps:
        shape=full if n.side=="sm" else shard
        n.input_shapes=((1,),shape);n.output_shape=shape
    return plan,ir,f


@pytest.mark.parametrize("case",((2,1,8,256),(4,1,4,256),(3,2,5,7),(5,3,1,2)))
def test_sequence_sum_matcher_derives_axis(case):
    plan,ir,f=matcher_fixture(*case)
    certs,frontiers,layouts=rc.advance_k_rank_bw_sum_frontiers(plan,ir,(f,),("sharded",))
    assert len(certs)==1
    c=certs[0]
    assert (c.rule_id,c.lean_theorem,c.rank_count,c.gather_dim)==(RULE,THEOREM,case[0],1)
    assert c.activation_fact.gather_dim==c.output_fact.gather_dim==1
    assert layouts==("reduction","sharded")


def renderer_fixture(k=3,b=2,s=5,h=7):
    ir,rel=_renderer_fixture(k)
    c=rel.certificates[0]
    x=replace(c.activation_fact,gather_dim=1);out=replace(c.output_fact,gather_dim=1)
    c=replace(c,rule_id=RULE,lean_theorem=THEOREM,gather_dim=1,activation_fact=x,output_fact=out)
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    tr=replace(rel.transition_specs[0],rule_id=RULE,lean_theorem=THEOREM,
        pre_facts=(c.gradient_fact,x),post_facts=(out,),certificate_digest=_typed_certificate_digest(c))
    g,xr,yr=rel.dependent_chain_plan.relation_facts
    rel.dependent_chain_plan.relation_facts=(g,
        replace(xr,source=x,full_shape=(b,s*k,h),shard_shape=(b,s,h),gather_dim=1),
        replace(yr,source=out,full_shape=(b,s*k,h),shard_shape=(b,s,h),gather_dim=1))
    rel.certificates=(c,);rel.transition_specs=(tr,)
    rel.dependent_chain_plan.complete=True
    rel.dependent_chain_plan.states=tuple(replace(st,state_id=f"state_{i:06d}") for i,st in enumerate(rel.dependent_chain_plan.states))
    rel.dependent_chain_plan.segments=(replace(rel.dependent_chain_plan.segments[0],pre_state_id="state_000000",post_state_id="state_000001"),)
    return ir,rel


def test_sequence_sum_registered_renderer():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture()
    source=render_closed_segment(ir,rel,"segment_000000")
    assert THEOREM in source
    assert "allGatherPrimDimN 1 3 0" in source
    assert source.count("private theorem segment_000000_hPmWriter")==3


@pytest.mark.parametrize("mutation",("rank","gradient","batch","two-axes","shape","params"))
def test_sequence_sum_rejects_inconsistent_authority(mutation):
    plan,ir,f=matcher_fixture()
    sm,*pm=plan.steps
    if mutation=="rank": pm[1].rank=0
    elif mutation=="gradient": pm[1].input_bindings=("init:901",pm[1].input_bindings[1])
    elif mutation=="batch": sm.output_shape=(3,15,7)
    elif mutation=="two-axes": sm.output_shape=(2,15,21)
    elif mutation=="shape": pm[1].input_shapes=((1,),(2,4,7))
    elif mutation=="params": pm[0].parameters=(1,)
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_sum_frontiers(plan,ir,(f,),("sharded",))


def witness_source():
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.composer import render_closed_segment
    sources=[]
    for n,case in enumerate(((2,1,8,256),(4,1,4,256),(3,2,5,7),(5,3,1,2))):
        ir,rel=renderer_fixture(*case)
        src=fixture_source(ir,rel,render_closed_segment).replace("SyntheticBWLayernorm","SyntheticBWSum").replace("import denote.KRankBWLayernorm","import denote.KRankBWSumSequence")
        sources.append(src.replace("SyntheticBWSum",f"BWSumSequenceCase{n}"))
    imports=list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


def test_sequence_sum_checked_in_witness():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedBWSumSequenceWitness.lean"
    assert path.read_text()==witness_source()
