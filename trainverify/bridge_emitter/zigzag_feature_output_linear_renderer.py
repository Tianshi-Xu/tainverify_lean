"""Generic atomic renderer for joined-zigzag activation × sharded weight output linears."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict

RULE = "zigzag-feature-output-linear-two-rank"
THEOREM = "TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.output_sharded_linear_two"

def _digest(c):
    return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()

def render_closed_zigzag_feature_output_linear_segment(ir, relation, segment_id):
    from .composer import _node_text, _shape_text
    from .relation_compiler import ZigzagFeatureOutputLinearCertificate
    chain=relation.dependent_chain_plan
    matches=[] if chain is None else [s for s in chain.segments if s.segment_id==segment_id]
    if chain is None or not chain.complete or len(matches)!=1: raise ValueError("zigzag-feature output linear requires one complete segment")
    seg=matches[0]
    if len(seg.transition_ids)!=1: raise ValueError("zigzag-feature output linear requires one transition")
    t={x.transition_id:x for x in relation.transition_specs}[seg.transition_ids[0]]
    if t.rule_id!=RULE or t.lean_theorem!=THEOREM or len(t.pre_facts)!=2 or len(t.post_facts)!=1: raise ValueError("zigzag-feature output linear theorem/fact grammar disagrees")
    certs=[c for c in relation.certificates if type(c) is ZigzagFeatureOutputLinearCertificate and c.rule_id==RULE and c.lean_theorem==THEOREM and {c.activation_fact,c.weight_fact}==set(t.pre_facts) and c.output_fact==t.post_facts[0] and _digest(c)==t.certificate_digest]
    if len(certs)!=1: raise ValueError("zigzag-feature output linear lacks one exact certificate")
    c=certs[0]; records={x.source:x for x in chain.relation_facts}; states={x.state_id:x for x in chain.states}
    act,weight,out=records[c.activation_fact],records[c.weight_fact],records[c.output_fact]
    before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if not {act.fact_id,weight.fact_id}<=set(before.fact_ids) or out.fact_id not in after.fact_ids or not set(after.fact_ids)<=set(before.fact_ids)|{out.fact_id}: raise ValueError("zigzag-feature output linear liveness disagrees")
    smids=tuple(range(*seg.sm_range)); pmids=tuple(range(*seg.pm_range))
    if t.sm_node_indices!=smids or t.pm_node_indices!=pmids or len(smids)!=1 or len(pmids)!=2: raise ValueError("zigzag-feature output linear requires exact 1x2 frame")
    sm=ir.sm_nodes[smids[0]]; p0,p1=(ir.pm_nodes[i] for i in pmids)
    if (sm.rank,p0.rank,p1.rank)!=(0,0,1) or any(n.op!="FW_mix_precision_linear" or len(n.ins)!=2 or len(n.outs)!=1 or n.params for n in (sm,p0,p1)): raise ValueError("zigzag-feature output linear writer signature disagrees")
    if act.kind!="joined_zigzag" or weight.kind!="sharded" or out.kind!="zigzag_feature" or weight.gather_dim!=0 or out.gather_dim!=1: raise ValueError("zigzag-feature output linear relation layouts disagree")
    if act.metadata_tid is None or out.metadata_tid!=act.metadata_tid or out.metadata_region_id!=act.metadata_region_id: raise ValueError("zigzag-feature output linear metadata disagrees")
    if len(weight.pm_tids)!=2 or len(out.pm_tids)!=2 or act.joined_pm_tid is None: raise ValueError("zigzag-feature output linear rank payload disagrees")
    if (sm.ins,p0.ins,p1.ins)!=( [act.sm_tid,weight.sm_tid], [act.joined_pm_tid,weight.pm_tids[0]], [act.joined_pm_tid,weight.pm_tids[1]] ): raise ValueError("zigzag-feature output linear input roles disagree")
    if (sm.outs[0],p0.outs[0],p1.outs[0])!=(out.sm_tid,out.pm_tids[0],out.pm_tids[1]): raise ValueError("zigzag-feature output linear outputs disagree")
    rows,input_dim,feature=c.rows,c.input_features,c.output_feature
    if min(rows,input_dim,feature)<=0 or act.full_shape!=(2*rows,input_dim) or act.shard_shape!=(rows,input_dim) or act.row_shard_shape!=(rows,input_dim) or weight.full_shape!=(2*feature,input_dim) or weight.shard_shape!=(feature,input_dim) or out.full_shape!=(2*rows,2*feature) or out.row_shard_shape!=(rows,2*feature) or out.shard_shape!=(2*rows,feature): raise ValueError("zigzag-feature output linear shape contract disagrees")
    smt,p0t,p1t=map(_node_text,(sm,p0,p1)); full=_shape_text(list(out.full_shape)); row=_shape_text(list(out.row_shard_shape)); feat=_shape_text(list(out.shard_shape)); afull=_shape_text(list(act.full_shape)); arow=_shape_text(list(act.row_shard_shape)); wfull=_shape_text(list(weight.full_shape)); wshard=_shape_text(list(weight.shard_shape))
    def writer(name,graph,store,nodes,pos,node,final,nodes_name):
        bef=nodes[:pos]; aft=nodes[pos+1:]
        return [f"    have {name} : {final} {node.outs[0]} = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",f"      simpa [{final}, {nodes_name}] using",f"        (foldl_faithful_binary_middle_writer {graph} {store} [{', '.join(_node_text(x) for x in bef)}] [{', '.join(_node_text(x) for x in aft)}] {_node_text(node)}",f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} fw_linear (by","            intro s","            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","            unfold applyNodeDistributed","            rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",f"            · exact applyNode_fw_mix_precision_linear_out_1p {graph} s {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}","            · native_decide","            · native_decide","          ) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"]
    lines=[f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := [{smt}]",f"  pmNodes := [{p0t}, {p1t}]","  sound := by","    intro smStore pmStore hstate",f"    let smNodes : List NodeDecl := [{smt}]",f"    let pmNodes : List NodeDecl := [{p0t}, {p1t}]",f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by","      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide",f"    have ha : {act.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"    have hw : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)"]
    lines+=writer("hsm",ir.sm_graph_ref,"smStore",(sm,),0,sm,"smFinal","smNodes")+writer("hp0",ir.pm_graph_ref,"pmStore",(p0,p1),0,p0,"pmFinal","pmNodes")+writer("hp1",ir.pm_graph_ref,"pmStore",(p0,p1),1,p1,"pmFinal","pmNodes")
    lines += [f"    have hmeta : pmFinal {out.metadata_tid} = pmStore {act.metadata_tid} := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)",f"    have hout : {out.fact_id}.Holds smFinal pmFinal := by",f"      change JoinedZigzagRel (smStore {act.sm_tid}) (pmStore {act.joined_pm_tid}) (pmStore {act.metadata_tid}) {afull} {arow} at ha",f"      change ShardedRel (smStore {weight.sm_tid}) [pmStore {weight.pm_tids[0]}, pmStore {weight.pm_tids[1]}] 0 {wfull} {wshard} at hw",f"      have core := ZigzagFeatureRel.output_sharded_linear_two {rows} {input_dim} {feature} ha hw (by native_decide) (by native_decide) (by native_decide)",f"      change ZigzagFeatureRel (smFinal {out.sm_tid}) [pmFinal {out.pm_tids[0]}, pmFinal {out.pm_tids[1]}] (pmFinal {out.metadata_tid}) {full} {row} {feat}","      rw [hsm, hp0, hp1, hmeta]","      exact core","    exact RelationState.Holds.mono_insert hframe hout (by native_decide)",""]
    return "\n".join(lines)
