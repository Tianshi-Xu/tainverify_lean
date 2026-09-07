"""Portable interleaved dim-1 FW/BW sum inputs and frozen-production replay."""
from dataclasses import replace
from types import SimpleNamespace as NS
from pathlib import Path
import json
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter.composer import _typed_certificate_digest

SUM = "sum-producer-sharded-k-rank-dim1"
BW = "bw-sum-scalar-broadcast-dim1-k-rank"
ST = "TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum"
BT = "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3"

def fixture(k=2, b=2, s=3, h=5):
    full, shard = (b, s*k, h), (b, s, h)
    xt = tuple(1000-r*7 for r in range(k))
    yt = tuple(2000-r*7 for r in range(k))
    zt = tuple(3000-r*7 for r in range(k))
    g = rc.RelationFactSpec("reduction", ("init:9", "init:9"))
    x = rc.RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))), gather_dim=1)
    y = rc.RelationFactSpec("reduction", ("sm:1:0", *(f"pm:{k+2*r}:0" for r in range(k))))
    z = rc.RelationFactSpec("sharded", ("sm:2:0", *(f"pm:{k+2*r+1}:0" for r in range(k))), gather_dim=1)
    records = tuple(rc.ClosedRelationFactRecord(n,f,f.layout,t,ts,None,None,fs,ss,gather_dim=f.gather_dim) for n,f,t,ts,fs,ss in (
        ("fact_g",g,9,(9,),(1,),(1,)), ("fact_x",x,10,xt,full,shard),
        ("fact_sum",y,20,yt,(1,),(1,)), ("fact_bw",z,30,zt,full,shard)))
    certs = (rc.KRankSumProducerCertificate(SUM,k,1,full,shard,x,y,y.step_triple[0],y.step_triple[1:],ST),
             rc.KRankBWSumCertificate(BW,k,1,g,x,z,z.step_triple[0],z.step_triple[1:],BT))
    transitions = tuple(replace(rc.CertificateTransitionSpec(n,c.rule_id,pre,(post,),sm,pm,c.lean_theorem),certificate_digest=_typed_certificate_digest(c)) for n,c,pre,post,sm,pm in (
        ("tr_sum",certs[0],(x,),y,(1,),tuple(k+2*r for r in range(k))),
        ("tr_bw",certs[1],(g,x),z,(2,),tuple(k+2*r+1 for r in range(k)))))
    segment = rc.ClosedDependentSegmentRecord("segment_000000","component_0","state_before","state_after",("tr_sum","tr_bw"),(1,3),(k,3*k))
    states=(rc.ClosedRelationStateRecord("state_before",("fact_g","fact_x")),rc.ClosedRelationStateRecord("state_after",tuple(r.fact_id for r in records)))
    chain=NS(complete=True,relation_facts=records,states=states,segments=(segment,),authority_facts=(),anchor_fact=None)
    sm=[Node(0,"FW_float",[8],[10],[]),Node(0,"FW_sum",[10],[20],[]),Node(0,"BW_sum",[9,10],[30],[])]
    pm=[Node(r,"FW_float",[8],[xt[r]],[]) for r in range(k)]
    for r in range(k): pm.extend([Node(r,"FW_sum",[xt[r]],[yt[r]],[]),Node(r,"BW_sum",[9,xt[r]],[zt[r]],[])])
    return NS(sm_nodes=sm,pm_nodes=pm,sm_graph_ref="SumWitness.smGraph",pm_graph_ref="SumWitness.pmGraph"), NS(dependent_chain_plan=chain,transition_specs=transitions,certificates=certs)

def witness_source(k=2, b=2, s=3, h=5):
    """Return exact standalone Lean bytes; caller owns writing/kernel execution."""
    from trainverify.bridge_emitter.sum_fw_bw_renderer import render_closed_sum_fw_bw_segment
    from trainverify.bridge_emitter.composer import _node_text
    ir, rel = fixture(k,b,s,h)
    chain=rel.dependent_chain_plan
    chain.anchor_fact=NS(fact_id="anchor",kind="tensor_shape",side="sm",tid=8,shape=(1,))
    chain.states=tuple(replace(state,fact_ids=(*state.fact_ids,"anchor")) for state in chain.states)
    lines=["import denote.RelationCompiler", "import denote.KRankBWSumSequence",
           "open TrainVerify.Denote", "open TrainVerify.Denote.RelationCompiler",
           "namespace SumWitness", "noncomputable section", "set_option maxHeartbeats 500000",
           f"def smGraph : GraphDecl := {{ numRanks := 1, nodes := [{', '.join(_node_text(n) for n in ir.sm_nodes)}], replicaGroups := [] }}",
           f"def pmGraph : GraphDecl := {{ numRanks := {k}, nodes := [{', '.join(_node_text(n) for n in ir.pm_nodes)}], replicaGroups := [] }}"]
    for rec in chain.relation_facts:
        tids=str(list(rec.pm_tids)); full=str(list(rec.full_shape)); shard=str(list(rec.shard_shape))
        args=f"{rec.sm_tid} {tids}"
        if rec.kind=="sharded": args+=f" 1 {full} {shard}"
        else: args+=f" {full}"
        lines.append(f"private def {rec.fact_id} : RelationFact := .{rec.kind} {args}")
    lines.append("private def anchor : RelationFact := .tensorShape .sm 8 [1]")
    for state in chain.states:
        lines.extend([f"private def {state.state_id} : RelationState where",
                      f"  facts := [{', '.join(state.fact_ids)}]", "  nonempty := by decide"])
    lines.append(render_closed_sum_fw_bw_segment(ir,rel,"segment_000000"))
    lines.extend(["#print axioms segment_000000", "end", "end SumWitness", ""])
    return "\n".join(lines)

def production_fixture(k, audit_root):
    root=Path(audit_root)/f"p{k}"
    rows=json.loads((root/"attempts.json").read_text())
    row=next(r for r in rows if r["segment_id"]=="segment_000095")
    classes=json.loads((root/"failure_classes.json").read_text())
    assert row["class_id"]=="C01" and next(c for c in classes if c["class_id"]=="C01")["family"]==[SUM,BW]
    def tup(v):
        if isinstance(v,list): return tuple(tup(x) for x in v)
        return v
    def fact(v): return rc.RelationFactSpec(**{a:tup(b) for a,b in v.items()})
    raw=json.loads((root/"global_relation.json").read_text())["dependent_chain_plan"]
    records=tuple(rc.ClosedRelationFactRecord(**{a:fact(v) if a=="source" else tup(v) for a,v in r.items()}) for r in raw["relation_facts"])
    states=tuple(rc.ClosedRelationStateRecord(**{a:tup(v) for a,v in r.items()}) for r in raw["states"])
    segment=rc.ClosedDependentSegmentRecord(**{a:tup(v) for a,v in row["segment"].items()})
    transitions=tuple(rc.CertificateTransitionSpec(**{a:tuple(fact(f) for f in v) if a in ("pre_facts","post_facts") else tup(v) for a,v in r.items()}) for r in row["transitions"])
    certs=[]
    types={"KRankSumProducerCertificate":rc.KRankSumProducerCertificate,"KRankBWSumCertificate":rc.KRankBWSumCertificate}
    for r in json.loads((root/"certificates.json").read_text()):
        if r["type"] in types:
            certs.append(types[r["type"]](**{a:fact(v) if a.endswith("_fact") else tup(v) for a,v in r["data"].items()}))
    from trainverify.bridge_emitter import parser as p
    from trainverify.bridge_emitter.model_authority import load_model_authority,materialize_target_ir
    saved=p.DENOTE_DIR,p.GEN_DIR,p.GEN_FILE,p.MOD_PREFIX
    try:
        p.DENOTE_DIR=p.GEN_DIR="trainverify/FreshGPT";p.GEN_FILE="GeneratedData.lean";p.MOD_PREFIX="FreshGPT"
        model=load_model_authority(tuple(range(1,27)),str(Path(audit_root).parent/"definitions-fresh-only-parent"/f"p{k}"),model_id="sum-replay",allow_partial=False)
        ir=materialize_target_ir(model,3)
    finally: p.DENOTE_DIR,p.GEN_DIR,p.GEN_FILE,p.MOD_PREFIX=saved
    chain=NS(relation_facts=records,states=states,segments=(segment,),authority_facts=tuple(NS(**r) for r in raw["authority_facts"]),anchor_fact=NS(**raw["anchor_fact"]))
    return ir,NS(dependent_chain_plan=chain,transition_specs=transitions,certificates=tuple(certs))
