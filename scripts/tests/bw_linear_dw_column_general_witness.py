"""Exact per-case conditional column dW witnesses; never invokes Lean."""
from dataclasses import replace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node

RULE = "bw-linear-dw-input-column-sharded-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dw_column_allGather_rank3"
CASES = ((1,3,2,1,4),(2,2,5,7,3),(3,2,5,7,11),(5,2,1,3,2),(2,1,16,64,32),(4,1,16,64,16))


def renderer_fixture(k=3,b=2,s=5,o=7,i=11,*,dual=False,sparse=False,with_view=False,namespace="SyntheticBWLinearDwColumnGeneral"):
    from scripts.tests.test_k_rank_bw_linear_dx_column import renderer_fixture as dx_fixture
    ir,rel=dx_fixture(k,o,i,b=b,s=s)
    chain=rel.dependent_chain_plan
    g,x,w,dx=chain.relation_facts
    g=replace(g,source=replace(g.source,step_triple=(f"init:{g.sm_tid}",),joined_pm_step=f"init:{g.joined_pm_tid}"))
    x=replace(x,source=replace(x.source,step_triple=(f"init:{x.sm_tid}",*(f"init:{u}" for u in x.pm_tids))))
    w=replace(w,source=replace(w.source,step_triple=(f"init:{w.sm_tid}",*(f"init:{u}" for u in w.pm_tids))))
    indices=tuple(range(k))
    if sparse:
        ir.pm_nodes.insert(1,Node(0,"FW_neg",[9000],[9001],[]))
        ir.sm_nodes.append(Node(0,"FW_neg",[9010],[9011],[]))
        indices=tuple(0 if r==0 else r+1 for r in range(k))
    dx=replace(dx,source=replace(dx.source,step_triple=("sm:0:0",*(f"pm:{p}:0" for p in indices))))
    df=rc.RelationFactSpec("sharded",("sm:0:1",*(f"pm:{p}:1" for p in indices)),gather_dim=1)
    dw=replace(w,fact_id="fact_dw",source=df,sm_tid=401,pm_tids=tuple(5000+r for r in range(k)))
    c=rc.KRankBWLinearDwColumnShardedCertificate(RULE,k,g.source,x.source,w.source,df,"sm:0:1",tuple(f"pm:{p}:1" for p in indices),THEOREM)
    base=rel.transition_specs[0]
    t=replace(base,transition_id="transition_dw",rule_id=RULE,pre_facts=tuple(sorted((g.source,x.source,w.source))),post_facts=(df,),pm_node_indices=indices,lean_theorem=THEOREM,certificate_digest=_typed_certificate_digest(c))
    certs=[];ts=[];records=[g,x,w]
    if dual:
        dc=replace(rel.certificates[0],input_facts=(g.source,x.source,w.source),output_fact=dx.source,pm_step_ids=tuple(f"pm:{p}:0" for p in indices))
        certs.append(dc);ts.append(replace(base,pre_facts=tuple(sorted(dc.input_facts)),post_facts=(dx.source,),pm_node_indices=indices,certificate_digest=_typed_certificate_digest(dc)));records.append(dx)
    certs.append(c);ts.append(t);records.append(dw)
    if with_view:
        si,pi=len(ir.sm_nodes),len(ir.pm_nodes)
        vf=rc.RelationFactSpec("joined",(f"sm:{si}:0",),joined_pm_step=f"pm:{pi}:0")
        vc=rc.JoinedBWViewCertificate("bw-view-joined",g.full_shape,g.full_shape,g.source,vf,f"sm:{si}:0",f"pm:{pi}:0","TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view")
        certs.append(vc);ts.append(rc.CertificateTransitionSpec("transition_view",vc.rule_id,(g.source,),(vf,),(si,),(pi,),vc.lean_theorem,certificate_digest=_typed_certificate_digest(vc)))
        records.append(replace(g,fact_id="fact_view",source=vf,sm_tid=110,joined_pm_tid=1100))
        ir.sm_nodes.append(Node(0,"BW_view",[g.sm_tid,g.sm_tid],[110],list(g.full_shape)))
        ir.pm_nodes.append(Node(0,"BW_view",[g.joined_pm_tid,g.joined_pm_tid],[1100],list(g.full_shape)))
    chain.relation_facts=tuple(records)
    chain.states=(replace(chain.states[0],fact_ids=tuple(r.fact_id for r in (g,x,w))),replace(chain.states[1],fact_ids=tuple(r.fact_id for r in records)))
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in ts),sm_range=(0,len(ir.sm_nodes)),pm_range=(0,len(ir.pm_nodes))),)
    chain.complete=True
    rel.certificates=tuple(certs);rel.transition_specs=tuple(ts)
    ir.pm_num_ranks=k;ir.sm_graph_ref=f"{namespace}.smGraph";ir.pm_graph_ref=f"{namespace}.pmGraph"
    return ir,rel


def render(ir,rel,segment_id):
    from trainverify.bridge_emitter.bw_linear_column_dual_renderer import render_closed_k_rank_bw_linear_column_dual_segment
    from trainverify.bridge_emitter.bw_linear_dx_column_renderer import render_closed_k_rank_bw_linear_dw_column_segment
    dual=any(t.rule_id=="bw-linear-dx-column-sharded-k-rank" for t in rel.transition_specs)
    return (render_closed_k_rank_bw_linear_column_dual_segment if dual else render_closed_k_rank_bw_linear_dw_column_segment)(ir,rel,segment_id)


def witness_source(k=3,b=2,s=5,o=7,i=11,*,dual=False,sparse=False,with_view=False,namespace="SyntheticBWLinearDwColumnGeneral",render_fn=None):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    ir,rel=renderer_fixture(k,b,s,o,i,dual=dual,sparse=sparse,with_view=with_view,namespace=namespace)
    return fixture_source(ir,rel,render_fn or render,pm_num_ranks=k).replace("SyntheticBWLayernorm",namespace).replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDwColumnGeneral\nimport denote.KRankBWLinearDxColumnGeneral").replace("noncomputable section","set_option maxHeartbeats 500000\nnoncomputable section")


def mixed_renderer_fixture(b=2,s=8):
    from scripts.tests.test_bw_column_collective_general import fixture
    ir,rel=fixture(b,s)
    chain=rel.dependent_chain_plan
    g,x,w=chain.relation_facts[:3]
    canonical=[]
    for r in (g,x,w):
        source=replace(r.source,step_triple=(f"init:{r.sm_tid}",*(f"init:{u}" for u in r.pm_tids)),**({"joined_pm_step":f"init:{r.joined_pm_tid}"} if r.kind=="joined" else {}))
        canonical.append(replace(r,source=source))
    g,x,w=canonical
    dc=replace(rel.certificates[0],input_facts=(g.source,x.source,w.source))
    dt=replace(rel.transition_specs[0],pre_facts=tuple(sorted(dc.input_facts)),certificate_digest=_typed_certificate_digest(dc))
    df=rc.RelationFactSpec("sharded",("sm:1:1",*(f"pm:{r}:1" for r in range(4))),gather_dim=1)
    dw=replace(w,fact_id="fact_dw",source=df,sm_tid=401,pm_tids=tuple(5000+r for r in range(4)))
    c=rc.KRankBWLinearDwColumnShardedCertificate(RULE,4,g.source,x.source,w.source,df,"sm:1:1",tuple(f"pm:{r}:1" for r in range(4)),THEOREM)
    t=replace(dt,transition_id="transition_dw",rule_id=RULE,post_facts=(df,),lean_theorem=THEOREM,certificate_digest=_typed_certificate_digest(c))
    chain.relation_facts=(*canonical,*chain.relation_facts[3:],dw)
    chain.states=(chain.states[0],replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,"fact_dw")))
    rel.certificates=(dc,c,*rel.certificates[1:]);rel.transition_specs=(dt,t,*rel.transition_specs[1:])
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in rel.transition_specs)),)
    return ir,rel


def mixed_witness_source(b=2,s=8):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_gather_view_alltoall_renderer import render_closed_bw_linear_gather_view_alltoall_segment
    ir,rel=mixed_renderer_fixture(b,s)
    return fixture_source(ir,rel,render_closed_bw_linear_gather_view_alltoall_segment,pm_num_ranks=4).replace("SyntheticBWLayernorm","SyntheticBWLinearDxColumn").replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDwColumnGeneral\nimport denote.KRankBWLinearDxColumnGeneral\nimport denote.KRankAllToAll")


def combined_witness_source():
    parts=[witness_source(*args,dual=dual,sparse=True,with_view=True,namespace=f"ColumnDwCase{j}_{int(dual)}") for j,args in enumerate(CASES) for dual in (False,True)]
    imports=list(dict.fromkeys(line for p in parts for line in p.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(l for l in p.splitlines() if not l.startswith("import ")) for p in parts)+"\n"
