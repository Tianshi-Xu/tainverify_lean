"""Closed PM-only renderer for ordered reduce-scatter reconstruction."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict


def _certificate_digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        separators=(",", ":"), sort_keys=True,
    ).encode()).hexdigest()


def render_closed_k_rank_reduce_scatter_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value
        from .relation_compiler import (
            CP2ShardedToOrdinaryCertificate,
            KRankReduceScatterReconstructionCertificate,
        )
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value
        from relation_compiler import (
            CP2ShardedToOrdinaryCertificate,
            KRankReduceScatterReconstructionCertificate,
        )
    rule="reduce-scatter-reconstruction-k-rank";chain=relation.dependent_chain_plan
    segs=[] if chain is None else [s for s in chain.segments if s.segment_id==segment_id]
    if chain is None or not chain.complete or len(segs)!=1:raise ValueError(f"{rule} requires one complete segment")
    seg=segs[0]
    if len(seg.transition_ids) not in (1,2):raise ValueError(f"{rule} requires reduction plus optional exact CP2 adapter")
    ts=[]
    for transition_id in seg.transition_ids:
        matches=[t for t in relation.transition_specs if t.transition_id==transition_id]
        if len(matches)!=1:raise ValueError(f"{rule} transition identity is missing or duplicated")
        ts.append(matches[0])
    t=ts[0]
    if t.rule_id != rule:raise ValueError(f"{rule} must own the physical transition first")
    cs=[c for c in relation.certificates if type(c) is KRankReduceScatterReconstructionCertificate and c.rule_id==t.rule_id and c.lean_theorem==t.lean_theorem and (c.input_fact,)==t.pre_facts and (c.output_fact,)==t.post_facts and _certificate_digest(c)==t.certificate_digest]
    if len(cs)!=1:raise ValueError(f"{rule} lacks one exact certificate")
    c=cs[0];adapter=None
    if len(ts)==2:
        at=ts[1]
        adapters=[a for a in relation.certificates if type(a) is CP2ShardedToOrdinaryCertificate and a.rule_id==at.rule_id and a.lean_theorem==at.lean_theorem and (a.input_fact,)==at.pre_facts and (a.output_fact,)==at.post_facts and a.input_fact==c.output_fact and _certificate_digest(a)==at.certificate_digest]
        if len(adapters)!=1:raise ValueError(f"{rule} lacks one exact co-owned CP2 adapter")
        adapter=adapters[0]
    records={x.source:x for x in chain.relation_facts};states={x.state_id:x for x in chain.states}
    try:
        pre=records[c.input_fact];post=records[c.output_fact]
        ordinary=None if adapter is None else records[adapter.output_fact]
        before=states[seg.pre_state_id];after=states[seg.post_state_id]
    except KeyError as exc:raise ValueError(f"{rule} fact/state framing is unresolved") from exc
    k=c.rank_count;dim=c.scatter_dim
    if (k<=0 or pre.kind!="reduction" or post.kind!="sharded" or post.gather_dim!=dim or len(pre.pm_tids)!=k or len(post.pm_tids)!=k or tuple(pre.full_shape)!=c.full_shape or tuple(post.full_shape)!=c.full_shape or tuple(post.shard_shape)!=c.shard_shape or ir.pm_num_ranks!=k):raise ValueError(f"{rule} relation metadata disagrees")
    if adapter is not None and (
        k != 2 or dim != 0 or ordinary.kind != "ordinary"
        or ordinary.sm_tid != post.sm_tid or ordinary.pm_tids != post.pm_tids
        or ordinary.full_shape != post.full_shape
        or ordinary.shard_shape != post.shard_shape
        or not ts[1].fact_only
        or tuple(ts[1].sm_node_indices)
        or tuple(ts[1].pm_node_indices)
    ):raise ValueError(f"{rule} CP2 adapter metadata/ownership disagrees")
    smidx=tuple(range(*seg.sm_range));pmframeidx=tuple(range(*seg.pm_range));writeridx=tuple(t.pm_node_indices)
    if (smidx or tuple(t.sm_node_indices) or len(writeridx)!=k
            or not set(writeridx)<=set(pmframeidx)
            or c.pm_step_ids!=tuple(f"pm:{i}:0" for i in writeridx)):
        raise ValueError(f"{rule} physical ownership is not exact")
    nodes=tuple(ir.pm_nodes[i] for i in pmframeidx)
    writers=tuple(ir.pm_nodes[i] for i in writeridx)
    for rank,node in enumerate(writers):
        if (node.op!="ReduceScatterPrim" or node.rank!=rank or tuple(node.params or ())!=(dim,) or tuple(node.ins)!=tuple(pre.pm_tids) or tuple(node.outs)!=(post.pm_tids[rank],)):raise ValueError(f"{rule} writer signature mismatch")
    live={*pre.pm_tids,*post.pm_tids}
    for index,node in zip(pmframeidx,nodes):
        if index not in writeridx and set(node.outs)&live:
            raise ValueError(f"{rule} frame overwrites live relation authority")
    produced={post.fact_id} | ({ordinary.fact_id} if ordinary is not None else set())
    terminal_fact=ordinary.fact_id if ordinary is not None else post.fact_id
    if (pre.fact_id not in before.fact_ids or terminal_fact not in after.fact_ids
            or not set(after.fact_ids)<=set(before.fact_ids)|produced):raise ValueError(f"{rule} liveness mismatch")
    pmn=f"{segment_id}_pmNodes";pmf=f"{segment_id}_pmFinal"
    node_chunks=[nodes[start:start+128] for start in range(0,len(nodes),128)]
    part_names=[f"{pmn}Part{index}" for index in range(len(node_chunks))]
    lines=["end"]
    for name,chunk in zip(part_names,node_chunks):
        lines.append(f"private def {name} : List NodeDecl := [{', '.join(_node_text(n) for n in chunk)}]")
    lines.extend([f"private def {pmn} : List NodeDecl := {' ++ '.join(part_names)}","noncomputable section",f"@[irreducible] private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""])
    helpers=[]
    for rank,(absolute_index,node) in enumerate(zip(writeridx,writers)):
        position=absolute_index-seg.pm_range[0]
        name=f"{segment_id}_writer{rank}";helpers.append(name);fs=f"({pmf} pmStore)";expr=f"reduceScatterPrimDimN {dim} {ir.pm_graph_ref}.numRanks {rank} [{', '.join('{store} '+str(x) for x in pre.pm_tids)}]"
        lines.extend([f"private theorem {name} (pmStore : Store) : {fs} {node.outs[0]} = {expr.format(store=fs)} := by",f"  have hfinal : {fs} = {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by unfold {pmf}; rfl"])
        proof=_render_mixed_final_value(name="hout",graph=ir.pm_graph_ref,initial_store="pmStore",final_store=fs,final_equality="hfinal",nodes_name=pmn,nodes=list(nodes),position=position,output_tid=node.outs[0],input_tids=tuple(node.ins),written_tids={x for n in nodes for x in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_reduceScatterPrim_out {ir.pm_graph_ref} t {rank} {dim} [{', '.join(str(x) for x in pre.pm_tids)}] {node.outs[0]}"])
        lines.extend(x[2:] if x.startswith("  ") else x for x in proof);lines.extend(["  exact hout",""])
    contrib="["+", ".join(f"pmFinal {x}" for x in pre.pm_tids)+"]";outs="["+", ".join(f"pmFinal {x}" for x in post.pm_tids)+"]";full=_shape_text(list(c.full_shape));shard=_shape_text(list(c.shard_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds smStore ({pmf} pmStore) := by",f"  let pmFinal := {pmf} pmStore",f"  have hframeRaw : {before.state_id}.Holds smStore ({pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) := by",f"    apply RelationState.Holds.fold_frame (smGraph := {ir.sm_graph_ref}) (pmGraph := {ir.pm_graph_ref}) [] {pmn} smStore pmStore hstate <;> native_decide",f"  have hfinal : pmFinal = {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by unfold pmFinal {pmf}; rfl",f"  have hframe : {before.state_id}.Holds smStore pmFinal := by rw [hfinal]; exact hframeRaw",f"  have hred : {pre.fact_id}.Holds smStore pmFinal := hframe _ (by native_decide)",f"  change ReductionRel (smStore {pre.sm_tid}) {contrib} {full} at hred"])
    for rank,h in enumerate(helpers):lines.extend([f"  have hw{rank}:={h} pmStore",f"  change pmFinal {post.pm_tids[rank]} = reduceScatterPrimDimN {dim} {k} {rank} {contrib} at hw{rank}",f"  have hredValue{rank} : smStore {pre.sm_tid} = allReducePrim {k} {rank} {contrib} := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value",f"  have hc{rank} : pmFinal {post.pm_tids[rank]} = chunkPrimDimN {dim} {k} {rank} (smStore {pre.sm_tid}) := by rw [hw{rank}]; unfold reduceScatterPrimDimN; rw [← hredValue{rank}]"])
    explicit_chunks="["+", ".join(f"chunkPrimDimN {dim} {k} {rank} (smStore {pre.sm_tid})" for rank in range(k))+"]"
    lines.extend([f"  have hordered : {outs} = List.ofFn (fun r : Fin {k} => chunkPrimDimN {dim} {k} r.1 (smStore {pre.sm_tid})) := by",f"    change {outs} = {explicit_chunks}",f"    rw [{', '.join('hc'+str(r) for r in range(k))}]",f"  have hvalue : smStore {pre.sm_tid} = allGatherPrimDimN {dim} {outs}.length 0 {outs} := by",f"    rw [hordered]",f"    simp only [List.length_ofFn]","    symm",f"    exact allGatherPrimDimN_chunks_ofFn {dim} {k} (smStore {pre.sm_tid}) (by omega) (by rw [hred.full_shape]; native_decide) (by rw [hred.full_shape]; native_decide)"])
    for rank in range(k):lines.extend([f"  have hs{rank} : (pmFinal {post.pm_tids[rank]}).shape = {shard} := by",f"    rw [hc{rank}, chunkPrimDimN_shape {dim} {k} {rank} (smStore {pre.sm_tid}) {full} hred.full_shape (by omega)]","    native_decide"])
    lines.extend([f"  have hout : {post.fact_id}.Holds smStore pmFinal := by",f"    change ShardedRel (smStore {post.sm_tid}) {outs} {dim} {full} {shard}","    refine { full_value := hvalue, full_shape := hred.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }","    intro x hx","    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx","    rcases hx with "+" | ".join("rfl" for _ in range(k))])
    for rank in range(k):lines.append(f"    · exact hs{rank}")
    published=[(post.fact_id,"hout")]
    if ordinary is not None:
        lines.extend([
            f"  have hord : {ordinary.fact_id}.Holds smStore pmFinal := by",
            f"    change ShardedRel (smStore {post.sm_tid}) {outs} 0 {full} {shard} at hout",
            f"    change GeneratedPatterns.Ordinary2Rel (smStore {ordinary.sm_tid}) (pmFinal {ordinary.pm_tids[0]}) (pmFinal {ordinary.pm_tids[1]}) {full} {shard}",
            f"    exact ShardedRel.toOrdinary2_dim0_rank2 (rows := {post.shard_shape[0]}) (width := {post.shard_shape[1]}) hout",
        ])
        published.append((ordinary.fact_id,"hord"))
    fresh="["+", ".join(fact for fact,_ in published)+"]"
    lines.extend(["  intro fact hfact",f"  have hc : fact ∈ {fresh} ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ {fresh} ++ {before.state_id}.facts by native_decide) hfact","  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc","  rcases hc with fresh | old","  · rcases fresh with "+" | ".join("rfl" for _ in published)])
    for _,proof in published:lines.append(f"    · exact {proof}")
    lines.extend(["  · exact hframe fact old","",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where","  smNodes := []",f"  pmNodes := {pmn}","  sound := by",f"    intro smStore pmStore hstate",f"    rw [← show {pmf} pmStore = {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore by unfold {pmf}; rfl]",f"    exact {segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
