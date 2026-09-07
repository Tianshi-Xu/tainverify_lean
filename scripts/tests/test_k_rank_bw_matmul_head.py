from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc

RULE="bw-matmul-head-sharded-k-rank"


def matcher_fixture(k=3,b=2,h=2,q=5,n=7,m=11,slot=0):
    steps=[]
    for side,ranks in (("sm",range(1)),("pm",range(k))):
        for r in ranks:
            heads=h*k if side=="sm" else h
            shapes=((b,heads,q,m),(b,heads,q,n),(b,heads,n,m))
            steps.append(SimpleNamespace(step_id=f"{side}:{r}:{slot}",side=side,rank=r,op="BW_matmul",
                parameters=(),input_bindings=tuple(f"{side}:{v}:{r}" for v in ("g","x","y")),
                input_shapes=shapes,output_shape=shapes[1 if slot==0 else 2],output_projection=f".{slot+1}"))
    return SimpleNamespace(steps=tuple(steps)),tuple(s.step_id for s in steps)


@pytest.mark.parametrize("case",((2,1,2,16,16,16),(4,1,1,16,16,16),(3,2,2,5,7,11),(5,3,2,1,2,3)))
@pytest.mark.parametrize("slot",(0,1))
def test_bw_matmul_head_generic_matcher(case,slot):
    plan,f=matcher_fixture(*case,slot)
    certs,frontiers,layouts=rc.advance_k_rank_bw_matmul_frontiers(plan,(f,),("sharded",))
    assert len(certs)==1
    c=certs[0]
    assert c.rule_id==RULE and c.rank_count==case[0]
    assert c.projection==f".{slot+1}"
    assert c.output_fact.gather_dim==1
    assert all(f.gather_dim==1 for f in c.input_facts)
    assert layouts==("sharded",)*3


@pytest.mark.parametrize("mutation",("rank","params","projection","input-shape","output-shape","batch"))
def test_bw_matmul_head_rejects_malformed(mutation):
    plan,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="rank": pms[1].rank=0
    elif mutation=="params": sm.parameters=(1,)
    elif mutation=="projection": pms[1].output_projection=".2"
    elif mutation=="input-shape": pms[1].input_shapes=((2,2,5,10),*pms[1].input_shapes[1:])
    elif mutation=="output-shape": pms[1].output_shape=(2,2,5,6)
    else: sm.input_shapes=((3,6,5,11),*sm.input_shapes[1:])
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_matmul_frontiers(plan,(f,),("sharded",))


def renderer_fixture(k=3,b=2,h=2,q=5,n=7,m=11,projections=(".1",".2")):
    from dataclasses import replace
    from scripts.tests.test_k_rank_bw_matmul_query import renderer_fixture as base
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=base(k=k,b=b,h=h,q=q,n=n,m=m,projections=projections)
    chain=rel.dependent_chain_plan
    g,x,y,*outputs=chain.relation_facts
    shapes=((b,h*k,q,m),(b,h*k,q,n),(b,h*k,n,m))
    shards=((b,h,q,m),(b,h,q,n),(b,h,n,m))
    ins=[]
    for i,r in enumerate((g,x,y)):
        refs=(r.source.step_triple[0],*(f"pm:{('g','x','y')[i]}:{rank}" for rank in range(k)))
        source=rc.RelationFactSpec("sharded",refs,gather_dim=1)
        tids=tuple((1000,2000,3000)[i]+rank for rank in range(k))
        ins.append(replace(r,source=source,kind="sharded",full_shape=shapes[i],shard_shape=shards[i],gather_dim=1,pm_tids=tids,joined_pm_tid=None))
    certs=[];trs=[];outs=[]
    for c,tr,r in zip(rel.certificates,rel.transition_specs,outputs):
        idx=1 if c.projection==".1" else 2
        source=replace(c.output_fact,layout="sharded",gather_dim=1)
        th="TrainVerify.Denote.bw_matmul_fst_head_gather_rank4" if idx==1 else "TrainVerify.Denote.bw_matmul_snd_head_gather_rank4"
        c=replace(c,rule_id=RULE,family="head-sharded",input_facts=tuple(r.source for r in ins),output_fact=source,lean_theorem=th)
        tr=replace(tr,rule_id=RULE,pre_facts=tuple(sorted(c.input_facts)),post_facts=(source,),lean_theorem=th,certificate_digest=_typed_certificate_digest(c))
        certs.append(c);trs.append(tr);outs.append(replace(r,source=source,kind="sharded",gather_dim=1,full_shape=shapes[idx],shard_shape=shards[idx]))
    chain.relation_facts=tuple(ins+outs);rel.certificates=tuple(certs);rel.transition_specs=tuple(trs)
    for rank,node in enumerate(ir.pm_nodes): node.ins[2]=ins[2].pm_tids[rank]
    return ir,rel


def test_bw_matmul_head_registered_renderer():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture()
    source=render_closed_segment(ir,rel,"segment_000000")
    assert "bw_matmul_fst_head_gather_rank4" in source
    assert "bw_matmul_snd_head_gather_rank4" in source
    assert "allGatherPrimDimN 1 3" in source


def witness_source():
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.composer import render_closed_segment
    cases=({"k":2,"b":1,"h":2,"q":16,"n":16,"m":16},
           {"k":3},{"k":4,"b":1,"h":1,"q":16,"n":16,"m":16},
           {"k":5,"projections":(".1",)},{"k":5,"projections":(".2",)})
    sources=[]
    for i,kw in enumerate(cases):
        ir,rel=renderer_fixture(**kw)
        src=fixture_source(ir,rel,render_closed_segment,pm_num_ranks=kw["k"]).replace("SyntheticBWLayernorm","SyntheticBWMatmulQuery").replace("import denote.KRankBWLayernorm","import denote.KRankBWMatmulHead")
        sources.append(src.replace("SyntheticBWMatmulQuery",f"MatmulHeadCase{i}"))
    imports=list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


@pytest.mark.parametrize("mutation",("axis","digest","pairing","projection","params","shape"))
def test_head_renderer_rejects_coherent_mutations(mutation):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=renderer_fixture()
    c=rel.certificates[0]
    if mutation=="axis":
        g,*rest=rel.dependent_chain_plan.relation_facts
        rel.dependent_chain_plan.relation_facts=(replace(g,gather_dim=2),*rest)
    elif mutation=="pairing": c=replace(c,pm_step_ids=tuple(reversed(c.pm_step_ids)))
    elif mutation=="projection": c=replace(c,projection=".2")
    elif mutation=="params": ir.pm_nodes[1].params=[1]
    elif mutation=="shape":
        g,*rest=rel.dependent_chain_plan.relation_facts
        rel.dependent_chain_plan.relation_facts=(replace(g,full_shape=(2,5,5,11)),*rest)
    rel.certificates=(c,*rel.certificates[1:])
    rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="wrong" if mutation=="digest" else _typed_certificate_digest(c)),*rel.transition_specs[1:])
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


def test_head_checked_in_witness_matches_generator():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedBWMatmulHeadWitness.lean"
    assert path.read_text()==witness_source()


def test_head_rejects_source_axis_record_mismatch():
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=renderer_fixture(projections=(".1",))
    c=rel.certificates[0]
    changed=replace(c.output_fact,gather_dim=2)
    c=replace(c,output_fact=changed)
    rel.certificates=(c,)
    rel.transition_specs=(replace(rel.transition_specs[0],post_facts=(changed,),certificate_digest=_typed_certificate_digest(c)),)
    rel.dependent_chain_plan.relation_facts=tuple(replace(r,source=changed) if r.source==rel.dependent_chain_plan.relation_facts[-1].source else r for r in rel.dependent_chain_plan.relation_facts)
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")
