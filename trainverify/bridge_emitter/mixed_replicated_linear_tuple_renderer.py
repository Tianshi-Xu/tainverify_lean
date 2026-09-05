"""Atomic positive tuple of paired ordinary/sharded replicated linear transitions."""
from __future__ import annotations
import hashlib,json
from dataclasses import asdict

def _digest(c):return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()

def render_closed_mixed_replicated_linear_tuple_segment(ir,relation,segment_id):
    try:
        from .composer import _node_text,_shape_text
        from .relation_compiler import FrontierLinearCertificate,KRankLocalRelationCertificate
    except ImportError:
        from composer import _node_text,_shape_text
        from relation_compiler import FrontierLinearCertificate,KRankLocalRelationCertificate
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None:raise ValueError("mixed linear tuple segment missing")
    by={t.transition_id:t for t in relation.transition_specs};ts=tuple(by[x] for x in seg.transition_ids)
    ordinary=tuple(t for t in ts if t.rule_id=="mix-precision-linear-ordinary-two-rank");sharded=tuple(t for t in ts if t.rule_id=="mix-linear-sharded-two-rank-dim0")
    if not ordinary or len(ordinary)!=len(sharded) or len(ts)!=2*len(ordinary):raise ValueError("mixed linear tuple requires equal positive views")
    sh_by_sm={t.sm_node_indices:t for t in sharded}
    if len(sh_by_sm)!=len(sharded) or any(t.sm_node_indices not in sh_by_sm for t in ordinary):raise ValueError("mixed linear tuple shared writer pairing missing")
    records={f.source:f for f in chain.relation_facts};states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    rows=[]
    for ot in ordinary:
        st=sh_by_sm[ot.sm_node_indices];weights=[f for f in ot.pre_facts if f.layout=="joined"];acts=[f for f in ot.pre_facts if f.layout=="ordinary"]
        if len(weights)!=1 or len(acts)!=1:raise ValueError("mixed linear tuple typed roles ambiguous")
        ws,aspec=weights[0],acts[0]
        ocs=[c for c in relation.certificates if type(c) is FrontierLinearCertificate and c.rule_id==ot.rule_id and c.lean_theorem==ot.lean_theorem and c.weight_fact==ws and c.input_step_triple==aspec.step_triple and c.output_step_triple==ot.post_facts[0].step_triple and _digest(c)==ot.certificate_digest]
        scs=[c for c in relation.certificates if type(c) is KRankLocalRelationCertificate and c.rule_id==st.rule_id and c.lean_theorem==st.lean_theorem and c.input_fact==st.pre_facts[0] and c.output_fact==st.post_facts[0] and _digest(c)==st.certificate_digest]
        if len(ocs)!=1 or len(scs)!=1:raise ValueError("mixed linear tuple exact certificate missing")
        weight,opre,opost,spre,spost=records[ws],records[aspec],records[ot.post_facts[0]],records[st.pre_facts[0]],records[st.post_facts[0]]
        if (ot.lean_theorem!="TrainVerify.Denote.fw_mix_precision_linear_allGather0_commute_2" or st.lean_theorem!="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_linear_dim0_two_2d" or weight.kind!="joined" or opre.kind!="ordinary" or spre.kind!="sharded" or (opre.sm_tid,opre.pm_tids)!=(spre.sm_tid,spre.pm_tids) or (opost.sm_tid,opost.pm_tids)!=(spost.sm_tid,spost.pm_tids) or ot.pm_node_indices!=st.pm_node_indices):raise ValueError("mixed linear tuple relation pairing disagrees")
        rows.append((ot,st,weight,opre,opost,spre,spost))
    sm_frame=tuple(ir.sm_nodes[i] for i in range(*seg.sm_range));pm_frame=tuple(ir.pm_nodes[i] for i in range(*seg.pm_range));k=ir.pm_num_ranks
    owned_sm={i for ot,_st,*_ in rows for i in ot.sm_node_indices};owned_pm={i for ot,_st,*_ in rows for i in ot.pm_node_indices}
    if owned_sm!=set(range(*seg.sm_range)) or owned_pm!=set(range(*seg.pm_range)) or k!=2:raise ValueError("mixed linear tuple exact frame coverage disagrees")
    required=set();fresh=[]
    for ot,st,w,opre,opost,spre,spost in rows:
        sm=ir.sm_nodes[ot.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in ot.pm_node_indices);wsm,wpm=w.sm_tid,w.joined_pm_tid
        if wpm is None or len(ot.sm_node_indices)!=1 or len(ot.pm_node_indices)!=k or sm.rank!=0 or tuple(n.rank for n in pms)!=tuple(range(k)) or any(n.op!="FW_mix_precision_linear" or len(n.ins)!=2 or len(n.outs)!=1 or n.params not in (None,[]) for n in (sm,*pms)) or (sm.ins[0],*(n.ins[0] for n in pms))!=(opre.sm_tid,*opre.pm_tids) or (sm.ins[1],*(n.ins[1] for n in pms))!=(wsm,wpm,wpm) or (sm.outs[0],*(n.outs[0] for n in pms))!=(opost.sm_tid,*opost.pm_tids):raise ValueError("mixed linear tuple writer topology disagrees")
        if len(opre.shard_shape)!=2 or len(opost.shard_shape)!=2:raise ValueError("mixed linear tuple rank unsupported")
        r,inp=opre.shard_shape;out=opost.shard_shape[1]
        if min(r,inp,out)<=0 or opre.full_shape!=(r*2,inp) or opost.full_shape!=(r*2,out) or opost.shard_shape!=(r,out) or w.full_shape!=(out,inp) or (spre.full_shape,spre.shard_shape)!=(opre.full_shape,opre.shard_shape) or (spost.full_shape,spost.shard_shape)!=(opost.full_shape,opost.shard_shape):raise ValueError("mixed linear tuple shape contract disagrees")
        required|={w.fact_id,opre.fact_id,spre.fact_id};fresh += [opost.fact_id,spost.fact_id]
    if not required<=set(before.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|set(fresh):raise ValueError("mixed linear tuple liveness disagrees")
    sid=segment_id;smn=f"{sid}_smNodes";pmn=f"{sid}_pmNodes";smf=f"{sid}_smFinal";pmf=f"{sid}_pmFinal"
    lines=[f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s"]
    def writer(name,graph,store,final,nodes_name,frame,pos,node):
        prefix,suffix=frame[:pos],frame[pos+1:]
        lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[0]} = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",f"  unfold {final}",f"  simpa [{nodes_name}] using",f"    (foldl_faithful_binary_middle_writer {graph} {store} [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}] {_node_text(node)} {node.ins[0]} {node.ins[1]} {node.outs[0]} fw_linear (by","      intro t","      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","      simp [applyNodeDistributed,applyNodeRingAttn]",f"      exact applyNode_fw_mix_precision_linear_out_1p {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}","    ) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"])
    helper_rows=[]
    for index,(ot,st,w,opre,opost,spre,spost) in enumerate(rows):
        sm=ir.sm_nodes[ot.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in ot.pm_node_indices);names=[]
        n=f"{sid}_smWriter{index}";writer(n,ir.sm_graph_ref,"smStore",smf,smn,sm_frame,ot.sm_node_indices[0]-seg.sm_range[0],sm);names.append(n)
        for rank,node in enumerate(pms):n=f"{sid}_pmWriter{index}_{rank}";writer(n,ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,ot.pm_node_indices[rank]-seg.pm_range[0],node);names.append(n)
        helper_rows.append(tuple(names))
    lines += ["set_option maxHeartbeats 500000 in",f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    unfold {smf} {pmf}",f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"]
    proofs=[]
    for index,((ot,st,w,opre,opost,spre,spost),names) in enumerate(zip(rows,helper_rows)):
        r,inp=opre.shard_shape;out=opost.shard_shape[1];fi=_shape_text(list(opre.full_shape));si=_shape_text(list(opre.shard_shape));fo=_shape_text(list(opost.full_shape));so=_shape_text(list(opost.shard_shape));ws=_shape_text(list(w.full_shape));wpm=w.joined_pm_tid
        rew=", ".join(name+(" smStore" if j==0 else " pmStore") for j,name in enumerate(names))
        lines += [f"  have hw{index} : {w.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"  have ho{index} : {opre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"  have houtO{index} : {opost.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    change smStore {w.sm_tid}=pmStore {wpm} ∧ (smStore {w.sm_tid}).shape={ws} ∧ (pmStore {wpm}).shape={ws} at hw{index}",f"    change GeneratedPatterns.Ordinary2Rel (smStore {opre.sm_tid}) (pmStore {opre.pm_tids[0]}) (pmStore {opre.pm_tids[1]}) {fi} {si} at ho{index}",f"    have core := Ordinary2Rel.mix_precision_linear {r} {inp} {out} ho{index} hw{index}.2.2 hw{index}.1 (by native_decide) (by native_decide) (by native_decide)",f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {opost.sm_tid}) (({pmf} pmStore) {opost.pm_tids[0]}) (({pmf} pmStore) {opost.pm_tids[1]}) {fo} {so}",f"    rw [{rew}]","    exact core",f"  have houtS{index} : {spost.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    change ShardedRel (({smf} smStore) {spost.sm_tid}) [({pmf} pmStore) {spost.pm_tids[0]},({pmf} pmStore) {spost.pm_tids[1]}] 0 {fo} {so}",f"    exact ShardedRel.ofOrdinary2_dim0_rank2 (rows := {r}) (width := {out}) houtO{index}"]
        proofs += [f"houtO{index}",f"houtS{index}"]
    lines += ["  intro fact hfact",f"  have covered : fact ∈ [{', '.join(fresh)}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{', '.join(fresh)}] ++ {before.state_id}.facts by native_decide) hfact","  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered","  rcases covered with fresh | old","  · rcases fresh with "+" | ".join("rfl" for _ in fresh)]
    lines += [f"    · exact {p}" for p in proofs];lines += ["  · exact hframe fact old",f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by","    intro smStore pmStore hstate",f"    simpa only [{smf},{pmf}] using {sid}_sound smStore pmStore hstate",""]
    return "\n".join(lines)
