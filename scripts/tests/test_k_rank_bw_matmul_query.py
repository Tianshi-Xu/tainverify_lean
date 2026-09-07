"""Generic query-axis BW_matmul matcher, renderer and Lean witness generators."""
from dataclasses import replace
from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc

RULES = ("bw-matmul-fst-query-sharded-k-rank", "bw-matmul-snd-contraction-reduction-k-rank")
THEOREMS = ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4",
            "TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4")


def matcher_fixture(k=3, b=2, h=3, q=5, n=7, m=11, projection=".1"):
    slot = int(projection[1:]) - 1
    full = ((b,h,q*k,m), (b,h,q*k,n), (b,h,n,m))
    local = ((b,h,q,m), (b,h,q,n), (b,h,n,m))
    sm = SimpleNamespace(step_id=f"sm:0:{slot}", op="BW_matmul", side="sm", rank=0,
        output_projection=projection, parameters=(), input_bindings=("sm:g", "sm:x", "sm:y"),
        input_shapes=full, output_shape=full[slot+1])
    pms = tuple(SimpleNamespace(step_id=f"pm:{r}:{slot}", op="BW_matmul", side="pm", rank=r,
        output_projection=projection, parameters=(), input_bindings=(f"pm:g:{r}", f"pm:x:{r}", "pm:y"),
        input_shapes=local, output_shape=local[slot+1]) for r in range(k))
    return SimpleNamespace(steps=(sm,*pms)), (sm.step_id, *(p.step_id for p in pms))


@pytest.mark.parametrize("case", [(1,1,1,1,1,1), (2,1,4,8,16,7), (3,2,3,5,7,11), (4,1,4,2,8,8), (5,3,2,1,3,2)])
@pytest.mark.parametrize("projection,layout,slot", [(".1","sharded",0),(".2","reduction",1)])
def test_generic_matcher(case, projection, layout, slot):
    plan, frontier = matcher_fixture(*case, projection=projection)
    certs, frontiers, layouts = rc.advance_k_rank_bw_matmul_frontiers(plan, (frontier,), (layout,))
    assert len(certs) == 1
    c = certs[0]
    assert type(c) is rc.KRankBWMatmulCertificate
    assert (c.rule_id,c.lean_theorem,c.rank_count) == (RULES[slot],THEOREMS[slot],case[0])
    assert tuple(f.layout for f in c.input_facts) == ("sharded","sharded","joined")
    assert tuple(f.gather_dim for f in c.input_facts) == (2,2,None)
    assert c.output_fact.gather_dim == (2 if slot == 0 else None)
    assert layouts == ("sharded","sharded","joined")
    assert frontiers[-1] == ("sm:y","pm:y")


@pytest.mark.parametrize("mutation", ["rank", "sm-rank", "params", "projection", "shared-y", "arity", "tensor-rank", "g", "x", "y", "output", "zero"])
def test_matcher_rejects_malformed(mutation):
    plan, f = matcher_fixture()
    sm, *pms = plan.steps
    p = pms[1]
    if mutation == "rank": p.rank = 0
    elif mutation == "sm-rank": sm.rank = 1
    elif mutation == "params": p.parameters = (1,)
    elif mutation == "projection": p.output_projection = ".2"
    elif mutation == "shared-y": p.input_bindings = (*p.input_bindings[:2], "pm:other")
    elif mutation == "arity": p.input_shapes = p.input_shapes[:2]
    elif mutation == "tensor-rank": p.input_shapes = (p.input_shapes[0][:3], *p.input_shapes[1:])
    elif mutation in ("g", "x", "y"):
        a = ("g", "x", "y").index(mutation)
        shapes = list(p.input_shapes); shapes[a] = (*shapes[a][:3], 99); p.input_shapes = tuple(shapes)
    elif mutation == "output": p.output_shape = (2,3,5,99)
    elif mutation == "zero":
        plan, f = matcher_fixture(b=0)
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_matmul_frontiers(plan, (f,), ("sharded",))


def renderer_fixture(k=3, b=2, h=3, q=5, n=7, m=11, projections=(".1", ".2"), view=False):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    certs = []
    for projection in projections:
        plan, f = matcher_fixture(k,b,h,q,n,m,projection)
        cs,_,_ = rc.advance_k_rank_bw_matmul_frontiers(plan,(f,),("sharded" if projection==".1" else "reduction",))
        certs.extend(cs)
    gf,xf,yf = certs[0].input_facts
    records = [rc.ClosedRelationFactRecord("fact_g",gf,"sharded",100,tuple(1000+r for r in range(k)),None,None,(b,h,q*k,m),(b,h,q,m),gather_dim=2),
        rc.ClosedRelationFactRecord("fact_x",xf,"sharded",200,tuple(2000+r for r in range(k)),None,None,(b,h,q*k,n),(b,h,q,n),gather_dim=2),
        rc.ClosedRelationFactRecord("fact_y",yf,"joined",300,(),None,None,(b,h,n,m),(b,h,n,m),joined_pm_tid=3000)]
    for c in certs:
        slot=int(c.projection[1:])-1
        full,local=((b,h,q*k,n),(b,h,q,n)) if slot==0 else ((b,h,n,m),(b,h,n,m))
        records.append(rc.ClosedRelationFactRecord(f"fact_out{slot}",c.output_fact,c.output_fact.layout,
            400+slot,tuple((4000 if slot==0 else 5000)+r for r in range(k)),None,None,
            full,local,gather_dim=c.output_fact.gather_dim))
    transitions = [rc.CertificateTransitionSpec(f"transition_{i:06d}",c.rule_id,tuple(sorted(c.input_facts)),
        (c.output_fact,),(0,),tuple(range(k)),c.lean_theorem,certificate_digest=_typed_certificate_digest(c)) for i,c in enumerate(certs)]
    sm_nodes=[Node(0,"BW_matmul",[100,200,300],[400,401],[])]
    pm_nodes=[Node(r,"BW_matmul",[1000+r,2000+r,3000],[4000+r,5000+r],[]) for r in range(k)]
    inputs=["fact_g","fact_x","fact_y"];outputs=[r.fact_id for r in records[3:]]
    if view:
        vi=rc.RelationFactSpec("joined",("sm:vi",),joined_pm_step="pm:vi")
        vo=rc.RelationFactSpec("joined",("sm:1:0",),joined_pm_step=f"pm:{k}:0")
        vc=rc.JoinedBWViewCertificate("bw-view-joined",(b,h,n,m),(b,h,n*m),vi,vo,"sm:1:0",f"pm:{k}:0","TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view")
        certs.append(vc)
        transitions.append(rc.CertificateTransitionSpec("transition_view",vc.rule_id,(vi,),(vo,),(1,),(k,),vc.lean_theorem,certificate_digest=_typed_certificate_digest(vc)))
        records.extend((rc.ClosedRelationFactRecord("fact_vi",vi,"joined",600,(),None,None,vc.input_shape,vc.input_shape,joined_pm_tid=6000),
            rc.ClosedRelationFactRecord("fact_vo",vo,"joined",700,(),None,None,vc.target_shape,vc.target_shape,joined_pm_tid=7000)))
        inputs.append("fact_vi");outputs.append("fact_vo")
        sm_nodes.append(Node(0,"BW_view",[600,601],[700],list(vc.target_shape)))
        pm_nodes.extend(Node(r,"BW_view",[6000,6001],[7000],list(vc.target_shape)) for r in range(k))
    states=(rc.ClosedRelationStateRecord("state_000000",tuple(inputs)),rc.ClosedRelationStateRecord("state_000001",tuple(inputs+outputs)))
    seg=rc.ClosedDependentSegmentRecord("segment_000000","component_000000",states[0].state_id,states[1].state_id,
        tuple(t.transition_id for t in transitions),(0,len(sm_nodes)),(0,len(pm_nodes)))
    return SimpleNamespace(sm_nodes=sm_nodes,pm_nodes=pm_nodes,sm_graph_ref="SyntheticBWMatmulQuery.smGraph",pm_graph_ref="SyntheticBWMatmulQuery.pmGraph"), SimpleNamespace(
        certificates=tuple(certs),transition_specs=tuple(transitions),dependent_chain_plan=SimpleNamespace(complete=True,
            relation_facts=tuple(records),states=states,segments=(seg,)))


@pytest.mark.parametrize("k",[1,2,3,4,5])
@pytest.mark.parametrize("projections,view",[((".1",),False),((".2",),False),((".1",".2"),False),((".2",".1"),True)])
def test_renderer_single_pair_optional_view(k,projections,view):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(k,projections=projections,view=view)
    source=render_closed_segment(ir,rel,"segment_000000")
    assert source.count("private def segment_000000_sm_final") == 1
    assert source.count("private def segment_000000_pm_final") == 1
    for p in projections:
        assert THEOREMS[int(p[1:])-1] in source
        assert f"private theorem segment_000000_semantic_{'fst' if p=='.1' else 'snd'}" in source
    assert "bw_matmul_snd_split_dW_g197" not in source
    assert "[1, 4, 8, 8]" not in source
    assert "sorry" not in source and "axiom " not in source


@pytest.mark.parametrize("mutation", ["type", "digest", "rank", "footprint", "projection", "family", "operands", "shape", "axis", "params", "shared-y", "node-rank", "extra-output", "retained-written", "view-params"])
def test_renderer_rejects_payload_mutations(mutation):
    from trainverify.bridge_emitter.composer import render_closed_segment, _typed_certificate_digest
    ir,rel=renderer_fixture(view=mutation=="view-params")
    c=rel.certificates[0];t=rel.transition_specs[0]
    if mutation=="type": c=SimpleNamespace(**c.__dict__)
    elif mutation=="digest": t=replace(t,certificate_digest="0"*64)
    elif mutation=="rank": c=replace(c,rank_count=2)
    elif mutation=="footprint": c=replace(c,pm_step_ids=tuple(reversed(c.pm_step_ids)))
    elif mutation=="projection": c=replace(c,projection=".2")
    elif mutation=="family": c=replace(c,family="batch-sharded")
    elif mutation=="operands": c=replace(c,input_facts=(c.input_facts[1],c.input_facts[0],c.input_facts[2]))
    elif mutation in ("shape","axis"):
        fs=rel.dependent_chain_plan.relation_facts
        bad=replace(fs[0],full_shape=(2,3,99,11)) if mutation=="shape" else replace(fs[0],gather_dim=1)
        rel.dependent_chain_plan.relation_facts=(bad,*fs[1:])
    elif mutation=="params": ir.pm_nodes[1].params=[1]
    elif mutation=="shared-y": ir.pm_nodes[1].ins[2]=999
    elif mutation=="node-rank": ir.pm_nodes[1].rank=0
    elif mutation=="extra-output":
        before,after=rel.dependent_chain_plan.states
        rel.dependent_chain_plan.states=(before,replace(after,fact_ids=(*after.fact_ids,"unproved")))
    elif mutation=="retained-written":
        # A coherent joined boundary can still be overwritten by an unselected slot.
        # A renderer must fail before emitting an impossible fold_frame proof.
        ir.sm_nodes[0].outs[1]=300
        # Drop snd projection so only the live y input is overwritten.
        rel.certificates=rel.certificates[:1];rel.transition_specs=rel.transition_specs[:1]
        seg=rel.dependent_chain_plan.segments[0]
        rel.dependent_chain_plan.segments=(replace(seg,transition_ids=(t.transition_id,)),)
        before,after=rel.dependent_chain_plan.states
        rel.dependent_chain_plan.states=(before,replace(after,fact_ids=tuple(f for f in after.fact_ids if f!="fact_out1")))
    elif mutation=="view-params": ir.pm_nodes[-1].params=[999]
    rel.certificates=(c,*rel.certificates[1:])
    if mutation not in ("type","digest"): t=replace(t,certificate_digest=_typed_certificate_digest(c))
    rel.transition_specs=(t,*rel.transition_specs[1:])
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


@pytest.mark.parametrize("projection", [".1", ".2"])
@pytest.mark.parametrize("side", ["sm", "pm"])
@pytest.mark.parametrize("argument", [0,1,2,3])
@pytest.mark.parametrize("dimension", [0,1,2,3])
def test_every_shape_equation_is_checked(projection,side,argument,dimension):
    plan,f=matcher_fixture(projection=projection)
    step=plan.steps[0 if side=="sm" else 2]
    shapes=list(step.input_shapes)+[step.output_shape]
    changed=list(shapes[argument]);changed[dimension]+=1;shapes[argument]=tuple(changed)
    step.input_shapes=tuple(shapes[:3]);step.output_shape=shapes[3]
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_matmul_frontiers(plan,(f,),("sharded" if projection==".1" else "reduction",))


@pytest.mark.parametrize("case", ["float-full", "bool-full", "source-axis"])
def test_exact_shape_types_and_fact_axis(case):
    if case=="source-axis":
        from trainverify.bridge_emitter.composer import render_closed_segment, _typed_certificate_digest
        ir,rel=renderer_fixture(projections=(".1",))
        c=rel.certificates[0];t=rel.transition_specs[0]
        bad=replace(c.input_facts[0],gather_dim=1)
        c=replace(c,input_facts=(bad,*c.input_facts[1:]))
        rel.certificates=(c,)
        rel.transition_specs=(replace(t,pre_facts=tuple(sorted(c.input_facts)),certificate_digest=_typed_certificate_digest(c)),)
        fs=rel.dependent_chain_plan.relation_facts
        rel.dependent_chain_plan.relation_facts=(replace(fs[0],source=bad),*fs[1:])
        with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")
    else:
        plan,f=matcher_fixture(b=1)
        sm=plan.steps[0];gs=list(sm.input_shapes[0]);gs[0]=1.0 if case=="float-full" else True
        sm.input_shapes=(tuple(gs),*sm.input_shapes[1:])
        with pytest.raises(rc.RelationCompositionError): rc.advance_k_rank_bw_matmul_frontiers(plan,(f,),("sharded",))


def test_old_nonquery_rank_domain_stays_closed():
    for k in (2,3,5):
        plan,f=matcher_fixture(k)
        for s in plan.steps:
            local=s.side=="pm"; r=s.rank
            s.input_bindings=("shared:g",f"{s.side}:x:{r}",f"{s.side}:y:{r}")
            s.input_shapes=((1,4,8,8),(1,4,8,2 if local else 2*k),(1,4,2 if local else 2*k,8))
            s.output_shape=(1,4,8,2 if local else 2*k)
        cs,fs,ls=rc.advance_k_rank_bw_matmul_frontiers(plan,(f,),("sharded",))
        assert cs==() and fs==(f,) and ls==("sharded",)


def test_query_registry_imports_and_old_dispatch_removed():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer
    for rule in RULES:
        spec=rc.get_closed_rule_spec(rule)
        assert spec.certificate_type is rc.KRankBWMatmulCertificate
        assert "denote.KRankBWMatmulQuery" in spec.lean_imports
        assert spec.singleton_renderer=="bw_matmul_query_renderer:render_closed_bw_matmul_query_segment"
    assert select_bw_compound_renderer((RULES[0],RULES[0])) is None
    assert select_bw_compound_renderer(("bw-matmul-fst-query-sharded-rank4","bw-matmul-snd-contraction-reduction-rank4","bw-view-joined")) is None


def witness_source(k=3,b=2,h=3,q=5,n=7,m=11,projections=(".1",".2"),view=False):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(k,b,h,q,n,m,projections,view)
    return fixture_source(ir,rel,render_closed_segment,pm_num_ranks=k).replace("SyntheticBWLayernorm","SyntheticBWMatmulQuery").replace("import denote.KRankBWLayernorm","import denote.KRankBWMatmulQuery\nimport denote.KRankMatmulQueryAxis")



def combined_witness_source():
    cases=({"k":1,"projections":(".1",)}, {"k":2,"projections":(".2",)},
           {"k":3}, {"k":4,"b":1,"h":4,"q":4,"n":16,"m":16}, {"k":5,"view":True})
    sources=[witness_source(**kw).replace("SyntheticBWMatmulQuery",f"MatmulQueryCase{i}") for i,kw in enumerate(cases)]
    imports=list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


def test_matmul_query_checked_in_witness_matches_generator():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedBWMatmulQueryWitness.lean"
    assert path.read_text()==combined_witness_source()
