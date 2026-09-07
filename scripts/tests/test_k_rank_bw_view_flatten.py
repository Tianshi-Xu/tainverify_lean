from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc

RULE="bw-view-flatten-sequence-sharded-k-rank"
THEOREM="TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3"


def matcher_fixture(k=3,b=2,s=5,n=4,d=7,*,axis=1):
    steps=[]
    for side,ranks in (("sm",range(1)),("pm",range(k))):
        for r in ranks:
            seq=s*k if side=="sm" and axis==1 else s
            heads=n*k if side=="sm" and axis==2 else n
            shape=(b,seq,heads,d);out=(b,seq,heads*d)
            steps.append(SimpleNamespace(step_id=f"{side}:{r}:0",side=side,rank=r,op="BW_view",parameters=out,
                input_bindings=(f"{side}:g:{r}",f"{side}:x:{r}"),input_shapes=(shape,out),output_shape=out))
    return SimpleNamespace(steps=tuple(steps)),tuple(st.step_id for st in steps)


@pytest.mark.parametrize("case",((2,1,8,4,16),(4,1,4,4,16),(3,2,5,3,7),(1,3,2,1,4),(5,2,1,2,3)))
def test_bw_view_flatten_sequence_matcher(case):
    plan,f=matcher_fixture(*case)
    certs,frontiers,layouts=rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))
    assert len(certs)==1
    c=certs[0]
    assert (c.rule_id,c.rank_count,c.lean_theorem)==(RULE,case[0],THEOREM)
    assert c.input_fact.gather_dim==c.output_fact.gather_dim==1
    assert len(frontiers)==1 and layouts==("sharded",)
    assert frontiers[0]==tuple(s.input_bindings[0] for s in plan.steps)


@pytest.mark.parametrize("mutation",("rank","params","aux-shape","per-rank-shape","full-shape"))
def test_bw_view_flatten_rejects_malformed(mutation):
    plan,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="rank": pms[1].rank=0
    elif mutation=="params": pms[0].parameters=(2,5,27)
    elif mutation=="aux-shape": pms[1].input_shapes=(pms[1].input_shapes[0],(2,4,28))
    elif mutation=="per-rank-shape": pms[1].input_shapes=((2,4,4,7),pms[1].input_shapes[1])
    else: sm.input_shapes=((2,14,4,7),sm.input_shapes[1])
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))


def renderer_fixture(k=3,b=2,s=5,n=3,d=7,*,axis=1):
    from dataclasses import replace
    from scripts.tests.test_k_rank_bw_sum_sequence import renderer_fixture as base
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=base(k,b,s,n*d)
    _,inp,out=rel.dependent_chain_plan.relation_facts
    full_in=(b,s*k,n,d) if axis==1 else (b,s,n*k,d)
    full_out=(b,s*k,n*d) if axis==1 else (b,s,n*k*d)
    inp=replace(inp,source=replace(inp.source,gather_dim=axis),gather_dim=axis,full_shape=full_in,shard_shape=(b,s,n,d))
    out=replace(out,source=replace(out.source,gather_dim=axis),gather_dim=axis,full_shape=full_out)
    rule=RULE if axis==1 else "bw-view-flatten-head-sharded-k-rank"
    theorem=THEOREM if axis==1 else "TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3"
    c=rc.KRankBWViewFlattenCertificate(rule,k,inp.source,out.source,"sm:0:0",tuple(f"pm:{r}:0" for r in range(k)),theorem)
    rel.certificates=(c,)
    tr=replace(rel.transition_specs[0],rule_id=rule,lean_theorem=theorem,pre_facts=(inp.source,),post_facts=(out.source,),certificate_digest=_typed_certificate_digest(c))
    rel.transition_specs=(tr,)
    chain=rel.dependent_chain_plan
    chain.relation_facts=(inp,out)
    chain.states=tuple(replace(st,fact_ids=tuple(f for f in st.fact_ids if f!="fact_g")) for st in chain.states)
    ir.sm_nodes=[Node(0,"BW_view",[inp.sm_tid,800],[out.sm_tid],list(out.full_shape))]
    ir.pm_nodes=[Node(r,"BW_view",[inp.pm_tids[r],8000+r],[out.pm_tids[r]],list(out.shard_shape)) for r in range(k)]
    return ir,rel


def test_bw_view_flatten_registered_renderer():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture()
    src=render_closed_segment(ir,rel,"segment_000000")
    assert THEOREM in src
    assert "fw_view [2, 15, 21]" in src
    assert src.count("private theorem segment_000000_hPmWriter")==3


@pytest.mark.parametrize("case",((2,1,16,2,16),(4,1,16,1,16),(3,2,5,2,7)))
def test_bw_view_flatten_head_axis_matcher(case):
    plan,f=matcher_fixture(*case,axis=2)
    certs,_,_=rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))
    assert len(certs)==1
    assert certs[0].rule_id=="bw-view-flatten-head-sharded-k-rank"
    assert certs[0].input_fact.gather_dim==certs[0].output_fact.gather_dim==2


def test_bw_view_flatten_head_renderer():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(axis=2)
    src=render_closed_segment(ir,rel,"segment_000000")
    assert "fw_view_allGatherPrimDimN_dim2_rank4_to_rank3" in src
    assert "allGatherPrimDimN 2 3 0" in src


def witness_source(axes=(1,2)):
    from trainverify.bridge_emitter.composer import render_closed_segment
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    sources=[]
    cases=((2,1,8,4,16),(4,1,4,4,16),(3,2,5,3,7),(1,3,2,1,4),(5,2,1,2,3))
    for axis in axes:
        for j,case in enumerate(cases):
            ir,rel=renderer_fixture(*case,axis=axis)
            src=fixture_source(ir,rel,render_closed_segment).replace("SyntheticBWLayernorm","SyntheticBWSum").replace("import denote.KRankBWLayernorm","import denote.KRankViewFlatten")
            sources.append(src.replace("SyntheticBWSum",f"ViewFlattenA{axis}Case{j}"))
    imports=list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


@pytest.mark.parametrize("axis",(1,2))
@pytest.mark.parametrize("mutation",("axis","params","pairing","type","digest","shape"))
def test_bw_view_flatten_renderer_authority_mutations(axis,mutation):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=renderer_fixture(axis=axis)
    c=rel.certificates[0]
    if mutation=="axis":
        fact=rel.dependent_chain_plan.relation_facts[0]
        rel.dependent_chain_plan.relation_facts=(replace(fact,gather_dim=3),rel.dependent_chain_plan.relation_facts[1])
    elif mutation=="params": ir.pm_nodes[0].params=[2,5,20]
    elif mutation=="pairing": c=replace(c,pm_step_ids=tuple(reversed(c.pm_step_ids)))
    elif mutation=="type": c=SimpleNamespace(**c.__dict__)
    elif mutation=="shape":
        fact=rel.dependent_chain_plan.relation_facts[0]
        rel.dependent_chain_plan.relation_facts=(replace(fact,full_shape=(2,14,3,7)),rel.dependent_chain_plan.relation_facts[1])
    rel.certificates=(c,)
    if mutation!="type":
        rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="wrong" if mutation=="digest" else _typed_certificate_digest(c)),)
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


def test_bw_view_flatten_checked_in_witness_matches_generator():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedBWViewFlattenWitness.lean"
    assert path.read_text()==witness_source()
