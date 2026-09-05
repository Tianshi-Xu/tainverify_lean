"""Atomic positive tuple of paired ordinary/sharded identity reshape or view transitions."""
from __future__ import annotations
import hashlib,json
from dataclasses import asdict

def _digest(c):return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()

def render_closed_mixed_identity_tuple_segment(ir,relation,segment_id):
    try:
        from .composer import _node_text,_shape_text
        from .relation_compiler import FrontierIdentityViewCertificate,KRankContiguousRelationCertificate
    except ImportError:
        from composer import _node_text,_shape_text
        from relation_compiler import FrontierIdentityViewCertificate,KRankContiguousRelationCertificate
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None:raise ValueError("mixed identity tuple segment missing")
    by={t.transition_id:t for t in relation.transition_specs};ts=tuple(by[x] for x in seg.transition_ids)
    ordinary=tuple(t for t in ts if t.rule_id in {"identity-reshape-ordinary-two-rank","identity-view-ordinary-two-rank"})
    sharded=tuple(t for t in ts if t.rule_id in {"reshape-sharded-k-rank","view-sharded-k-rank"})
    if not ordinary or len(ordinary)!=len(sharded) or len(ts)!=len(ordinary)+len(sharded):raise ValueError("mixed identity tuple requires equal positive typed views")
    op="FW_reshape" if ordinary[0].rule_id.startswith("identity-reshape") else "FW_view"
    if any(t.rule_id!=ordinary[0].rule_id for t in ordinary) or any(t.rule_id!=("reshape-sharded-k-rank" if op=="FW_reshape" else "view-sharded-k-rank") for t in sharded):raise ValueError("mixed identity tuple is not homogeneous")
    sh_by_sm={t.sm_node_indices:t for t in sharded}
    if len(sh_by_sm)!=len(sharded) or any(t.sm_node_indices not in sh_by_sm for t in ordinary):raise ValueError("mixed identity tuple lacks paired shared writers")
    pairs=tuple((ot,sh_by_sm[ot.sm_node_indices]) for ot in ordinary)
    records={f.source:f for f in chain.relation_facts};states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    rows=[]
    for ot,st in pairs:
        ocs=[c for c in relation.certificates if type(c) is FrontierIdentityViewCertificate and c.rule_id==ot.rule_id and c.lean_theorem==ot.lean_theorem and _digest(c)==ot.certificate_digest and c.input_step_triple==ot.pre_facts[0].step_triple and c.output_step_triple==ot.post_facts[0].step_triple]
        scs=[c for c in relation.certificates if type(c) is KRankContiguousRelationCertificate and c.rule_id==st.rule_id and c.lean_theorem==st.lean_theorem and _digest(c)==st.certificate_digest and c.input_fact==st.pre_facts[0] and c.output_fact==st.post_facts[0]]
        if len(ocs)!=1 or len(scs)!=1:raise ValueError("mixed identity tuple exact certificate missing")
        opre,opost,spre,spost=records[ot.pre_facts[0]],records[ot.post_facts[0]],records[st.pre_facts[0]],records[st.post_facts[0]]
        if (ot.lean_theorem!="TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id" or st.lean_theorem!="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_id" or spre.kind!="sharded" or opre.kind!="ordinary" or (opre.sm_tid,opre.pm_tids)!=(spre.sm_tid,spre.pm_tids) or (opost.sm_tid,opost.pm_tids)!=(spost.sm_tid,spost.pm_tids) or ot.sm_node_indices!=st.sm_node_indices or ot.pm_node_indices!=st.pm_node_indices):raise ValueError("mixed identity tuple relation pairing disagrees")
        rows.append((ot,st,opre,opost,spre,spost))
    sm_frame=tuple(ir.sm_nodes[i] for i in range(*seg.sm_range));pm_frame=tuple(ir.pm_nodes[i] for i in range(*seg.pm_range));k=ir.pm_num_ranks
    owned_sm={i for ot,_st,*_ in rows for i in ot.sm_node_indices};owned_pm={i for ot,_st,*_ in rows for i in ot.pm_node_indices}
    if owned_sm!=set(range(*seg.sm_range)) or owned_pm!=set(range(*seg.pm_range)) or k<=0:raise ValueError("mixed identity tuple does not exactly cover frame")
    fresh=[];required=set()
    for ot,st,opre,opost,spre,spost in rows:
        if len(ot.sm_node_indices)!=1 or len(ot.pm_node_indices)!=k:raise ValueError("mixed identity tuple writer cardinality disagrees")
        sm=ir.sm_nodes[ot.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in ot.pm_node_indices)
        if (sm.rank!=0 or tuple(n.rank for n in pms)!=tuple(range(k)) or any(n.op!=op or len(n.ins)!=1 or len(n.outs)!=1 or not n.params for n in (sm,*pms)) or (sm.ins[0],*(n.ins[0] for n in pms))!=(opre.sm_tid,*opre.pm_tids) or (sm.outs[0],*(n.outs[0] for n in pms))!=(opost.sm_tid,*opost.pm_tids) or tuple(sm.params)!=opost.full_shape or any(tuple(n.params)!=opost.shard_shape for n in pms) or (opre.full_shape,opre.shard_shape)!=(opost.full_shape,opost.shard_shape) or (spre.full_shape,spre.shard_shape)!=(opre.full_shape,opre.shard_shape) or (spost.full_shape,spost.shard_shape)!=(opost.full_shape,opost.shard_shape)):raise ValueError("mixed identity tuple writer/shape authority disagrees")
        required|={opre.fact_id,spre.fact_id};fresh += [opost.fact_id,spost.fact_id]
    if not required<=set(before.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|set(fresh):raise ValueError("mixed identity tuple liveness disagrees")
    sid=segment_id;smn=f"{sid}_smNodes";pmn=f"{sid}_pmNodes";smf=f"{sid}_smFinal";pmf=f"{sid}_pmFinal"
    lines=[f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s"]
    def writer(name,graph,store,final,nodes_name,frame,pos,node,target):
        prefix,suffix=frame[:pos],frame[pos+1:]
        apply=(f"exact applyNode_fw_reshape_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {_shape_text(node.params)}" if op=="FW_reshape" else f"exact applyNode_fw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.outs[0]}")
        lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[0]} = fw_view {_shape_text(list(target))} ({store} {node.ins[0]}) := by",f"  unfold {final}",f"  simpa [{nodes_name}] using",f"    (foldl_faithful_unary_middle_writer {graph} {store} [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}] {_node_text(node)} {node.ins[0]} {node.outs[0]} (fun x => fw_view {_shape_text(list(target))} x) (by","      intro t","      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","      simp [applyNodeDistributed,applyNodeRingAttn]",f"      {apply}","    ) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"])
    helper_rows=[]
    for index,(ot,st,opre,opost,spre,spost) in enumerate(rows):
        sm=ir.sm_nodes[ot.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in ot.pm_node_indices);names=[]
        n=f"{sid}_smWriter{index}";writer(n,ir.sm_graph_ref,"smStore",smf,smn,sm_frame,ot.sm_node_indices[0]-seg.sm_range[0],sm,opost.full_shape);names.append(n)
        for rank,node in enumerate(pms):
            n=f"{sid}_pmWriter{index}_{rank}";writer(n,ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,ot.pm_node_indices[rank]-seg.pm_range[0],node,opost.shard_shape);names.append(n)
        helper_rows.append(tuple(names))
    lines += ["set_option maxHeartbeats 500000 in",f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    unfold {smf} {pmf}",f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"]
    proofs=[]
    for index,((ot,st,opre,opost,spre,spost),names) in enumerate(zip(rows,helper_rows)):
        full,shard=_shape_text(list(opre.full_shape)),_shape_text(list(opre.shard_shape));prelist="["+", ".join(f"pmStore {x}" for x in spre.pm_tids)+"]";postlist="["+", ".join(f"({pmf} pmStore) {x}" for x in spost.pm_tids)+"]"
        lines += [f"  have ho{index} : {opre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"  have hs{index} : {spre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"  have houtO{index} : {opost.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    change GeneratedPatterns.Ordinary2Rel (smStore {opre.sm_tid}) (pmStore {opre.pm_tids[0]}) (pmStore {opre.pm_tids[1]}) {full} {shard} at ho{index}",f"    have core := Ordinary2Rel.view_id ho{index}",f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {opost.sm_tid}) (({pmf} pmStore) {opost.pm_tids[0]}) (({pmf} pmStore) {opost.pm_tids[1]}) {full} {shard}",f"    rw [{', '.join(name + (' smStore' if j==0 else ' pmStore') for j,name in enumerate(names))}]","    exact core",f"  have houtS{index} : {spost.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    change ShardedRel (smStore {spre.sm_tid}) {prelist} {spre.gather_dim} {full} {shard} at hs{index}",f"    have core := ShardedRel.fw_view_id hs{index}",f"    change ShardedRel (({smf} smStore) {spost.sm_tid}) {postlist} {spost.gather_dim} {full} {shard}",f"    rw [{', '.join(name + (' smStore' if j==0 else ' pmStore') for j,name in enumerate(names))}]","    simpa only [List.map] using core"]
        proofs += [f"houtO{index}",f"houtS{index}"]
    lines += ["  intro fact hfact",f"  have covered : fact ∈ [{', '.join(fresh)}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{', '.join(fresh)}] ++ {before.state_id}.facts by native_decide) hfact","  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered","  rcases covered with fresh | old","  · rcases fresh with "+" | ".join("rfl" for _ in fresh)]
    lines += [f"    · exact {p}" for p in proofs];lines += ["  · exact hframe fact old",f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by","    intro smStore pmStore hstate",f"    simpa only [{smf},{pmf}] using {sid}_sound smStore pmStore hstate",""]
    return "\n".join(lines)
