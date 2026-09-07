"""One-fold hidden embedding / AllToAll / sequence embedding atomic replay.

Hidden and sequence gradients are independent; only the sequence gradient is
produced by the collective. IDs chunks are existing closed pre-state authority.
"""
from __future__ import annotations
import re


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_bw_embedding_alltoall_mixed_segment(ir, relation, segment_id):
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import get_closed_rule_spec
    chain=relation.dependent_chain_plan
    segments=[] if chain is None else [s for s in chain.segments if s.segment_id==segment_id]
    if chain is None or len(segments)!=1: raise ValueError("missing or ambiguous atomic segment")
    segment=segments[0]
    tm={t.transition_id:t for t in relation.transition_specs}
    if len(tm)!=len(relation.transition_specs) or len(segment.transition_ids)!=3 or len(set(segment.transition_ids))!=3:
        raise ValueError("ambiguous transition identity")
    try: transitions=[tm[t] for t in segment.transition_ids]
    except KeyError as exc: raise ValueError("missing transition") from exc
    rules=('bw-embedding-hidden-sharded-k-rank','alltoall-k-rank-layout-transport','bw-embedding-sequence-reduction-k-rank')
    if {t.rule_id for t in transitions}!=set(rules): raise ValueError("mixed embedding family mismatch")
    ht,at,qt=(next(t for t in transitions if t.rule_id==rule) for rule in rules)
    def select(t,roles):
        spec=get_closed_rule_spec(t.rule_id)
        return _select_exact_typed_certificate(relation,t,t.rule_id,spec.lean_theorems[0],spec.certificate_type,roles)
    hc=select(ht,lambda c:(tuple(sorted((c.gradient_fact,c.ids_fact,c.weight_fact))),(c.output_fact,)))
    ac=select(at,lambda c:((c.input_fact,),(c.output_fact,)))
    qc=select(qt,lambda c:(tuple(sorted((c.gradient_fact,c.ids_chunks_fact,c.weight_fact))),(c.output_fact,)))
    records={x.source:x for x in chain.relation_facts}; by_id={x.fact_id:x for x in chain.relation_facts}
    states={x.state_id:x for x in chain.states}
    if len(records)!=len(chain.relation_facts) or len(by_id)!=len(records) or len(states)!=len(chain.states):raise ValueError("ambiguous fact/state identity")
    try:
        hg,hi,hw,ho=(records[f] for f in (hc.gradient_fact,hc.ids_fact,hc.weight_fact,hc.output_fact))
        ai,ao=(records[f] for f in (ac.input_fact,ac.output_fact))
        qg,qi,qw,qo=(records[f] for f in (qc.gradient_fact,qc.ids_chunks_fact,qc.weight_fact,qc.output_fact))
        before,after=states[segment.pre_state_id],states[segment.post_state_id]
    except KeyError as exc:raise ValueError("missing materialized authority") from exc
    k=hc.rank_count
    if type(k) is not int or k<=0 or k!=ir.pm_num_ranks or ir.sm_num_ranks!=1 or ac.rank_count!=k or qc.rank_count!=k:raise ValueError("rank authority mismatch")
    if ao!=qg or hg.source==ai.source:raise ValueError("expected independent hidden gradient and internal sequence gradient")
    ss,se=segment.sm_range;ps,pe=segment.pm_range
    if not 0<=ss<=se<=len(ir.sm_nodes) or not 0<=ps<=pe<=len(ir.pm_nodes):raise ValueError("invalid frame")
    def source_tid(ref,side):
        m=re.fullmatch(r'init:(0|[1-9][0-9]*)',ref)
        if m:return int(m[1])
        m=re.fullmatch(r'(sm|pm):(0|[1-9][0-9]*):(0|[1-9][0-9]*)',ref)
        if m is None or m[1]!=side:raise ValueError("invalid source reference")
        nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
        pos,slot=int(m[2]),int(m[3])
        if pos>=len(nodes) or slot>=len(nodes[pos].outs):raise ValueError("source outside graph")
        return nodes[pos].outs[slot]
    def latest(ref,side,pos):
        tid=source_tid(ref,side);nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
        writers=[(i,j) for i,n in enumerate(nodes[:pos]) for j,t in enumerate(n.outs) if t==tid]
        expected=f'{side}:{writers[-1][0]}:{writers[-1][1]}' if writers else f'init:{tid}'
        if ref!=expected:raise ValueError("source is not latest before read")
    def record(x,kind,dim,full,shard,n):
        f=x.source
        if (x.kind!=kind or f.layout!=kind or x.gather_dim!=dim or f.gather_dim!=dim or x.full_shape!=full or x.shard_shape!=shard or len(x.pm_tids)!=n or len(f.step_triple)!=n+1 or x.metadata_tid is not None or x.metadata_region_id is not None or x.row_shard_shape is not None or x.source_tid_triples or x.joined_pm_tid is not None or f.source_step_triples or f.joined_pm_step is not None):raise ValueError("source/record role axis shape mismatch")
        if source_tid(f.step_triple[0],'sm')!=x.sm_tid or tuple(source_tid(z,'pm') for z in f.step_triple[1:])!=x.pm_tids:raise ValueError("source/record TID mismatch")
    b,s,v,d=hc.batch_size,hc.sequence_size,hc.vocab_size,hc.shard_hidden
    qb,qs,qh,qv=qc.batch_size,qc.shard_sequence,qc.hidden_size,qc.vocab_size
    if any(type(z) is not int or z<=0 for z in (b,s,v,d,qb,qs,qh,qv)) or qc.shard_dim!=1:raise ValueError("dimension authority mismatch")
    record(hg,'sharded',2,(b,s,d*k),(b,s,d),k)
    record(hi,'sharded',0,(b,s),(b,s),1)
    for x in (hw,ho):record(x,'sharded',1,(v,d*k),(v,d),k)
    record(qg,'sharded',1,(qb,qs*k,qh),(qb,qs,qh),k)
    record(qi,'chunked',1,(qb,qs*k),(qb,qs),k)
    record(qw,'sharded',0,(qv,qh),(qv,qh),1)
    record(qo,'reduction',None,(qv,qh),(qv,qh),k)
    di,do=ac.input_gather_dim,ac.output_gather_dim
    if di!=2 or do!=1:raise ValueError("collective axis mismatch")
    full=list(ai.shard_shape)
    if len(full)!=3:raise ValueError("collective shape mismatch")
    full[di]*=k;record(ai,'sharded',di,tuple(full),ai.shard_shape,k)
    if ai.full_shape!=ao.full_shape or ai.sm_tid!=ao.sm_tid or ac.output_fact.step_triple!=(ac.input_fact.step_triple[0],*ac.pm_step_ids):raise ValueError("collective source mismatch")
    for tr,c,inputs,out in ((ht,hc,(hg,hi,hw),ho),(qt,qc,(qg,qi,qw),qo)):
        if len(tr.sm_node_indices)!=1 or len(tr.pm_node_indices)!=k or len(set(tr.pm_node_indices))!=k:raise ValueError("writer cardinality")
        if c.sm_step_id!=f'sm:{tr.sm_node_indices[0]}:0' or c.pm_step_ids!=tuple(f'pm:{i}:0' for i in tr.pm_node_indices) or out.source.step_triple!=(c.sm_step_id,*c.pm_step_ids):raise ValueError("writer footprint")
        for side,positions in (('sm',tr.sm_node_indices),('pm',tr.pm_node_indices)):
            nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
            for rank,pos in enumerate(positions):
                if pos not in range(ss,se) if side=='sm' else pos not in range(ps,pe):raise ValueError("writer outside frame")
                n=nodes[pos];ins=tuple(x.sm_tid if side=='sm' else x.pm_tids[0 if len(x.pm_tids)==1 else rank] for x in inputs)
                if n.op!='BW_embedding' or n.rank!=rank or n.params or tuple(n.ins)!=ins or n.outs!=[out.sm_tid if side=='sm' else out.pm_tids[rank]]:raise ValueError("embedding writer roles/rank mismatch")
                for x in inputs:latest(x.source.step_triple[0 if side=='sm' else 1 if len(x.pm_tids)==1 else rank+1],side,pos)
    if at.sm_node_indices or len(at.pm_node_indices)!=k or len(set(at.pm_node_indices))!=k or ac.pm_step_ids!=tuple(f'pm:{i}:0' for i in at.pm_node_indices):raise ValueError("collective footprint")
    anodes=[]
    for rank,pos in enumerate(at.pm_node_indices):
        if pos not in range(ps,pe):raise ValueError("collective outside frame")
        n=ir.pm_nodes[pos];anodes.append(n)
        if n.rank!=rank or n.op!='AllToAllPrim' or n.ins!=list(ai.pm_tids) or n.outs!=[ao.pm_tids[rank]] or n.params!=[di,do]:raise ValueError("collective writer rank/roles mismatch")
        for ref in ai.source.step_triple[1:]:latest(ref,'pm',pos)
    latest(ai.source.step_triple[0],'sm',ss)
    # Chunk facts must name the certificate's real earlier producers, not invented initial chunks.
    if qi.source.step_triple[1:]!=qc.pm_chunk_steps:raise ValueError("IDs chunk authority mismatch")
    fresh={ho.fact_id,ao.fact_id,qo.fact_id};required={x.fact_id for x in (hg,hi,hw,ai,qi,qw)}
    if not required<=set(before.fact_ids) or fresh & set(before.fact_ids) or not {ho.fact_id,qo.fact_id}<=set(after.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh:raise ValueError("active/public state mismatch")
    authority={x.fact_id:x for x in chain.authority_facts}
    if chain.anchor_fact is not None:authority[chain.anchor_fact.fact_id]=chain.anchor_fact
    def live(ids):
        sm,pm=set(),set()
        for fid in ids:
            if fid in by_id:
                x=by_id[fid];sm.add(x.sm_tid);pm.update(x.pm_tids)
                if x.joined_pm_tid is not None:pm.add(x.joined_pm_tid)
                if x.metadata_tid is not None:sm.add(x.metadata_tid);pm.add(x.metadata_tid)
                for t,a,b in x.source_tid_triples:sm.add(t);pm.update((a,b))
            elif fid in authority:
                x=authority[fid]
                if x.kind=='tensor_shape':(sm if x.side=='sm' else pm).add(x.tid)
                elif x.kind=='tensor_eq':
                    (sm if x.left_side=='sm' else pm).add(x.left_tid);(sm if x.right_side=='sm' else pm).add(x.right_tid)
                else:raise ValueError("unsupported authority kind")
            else:raise ValueError("unknown active fact")
        return sm,pm
    old=live(before.fact_ids);active=live(set(before.fact_ids)|set(after.fact_ids)|fresh)
    for side,nodes,bounds,owned,allowed,olds,lives in (
        ('sm',ir.sm_nodes,(ss,se),(*ht.sm_node_indices,*qt.sm_node_indices),{ho.sm_tid,qo.sm_tid},old[0],active[0]),
        ('pm',ir.pm_nodes,(ps,pe),(*ht.pm_node_indices,*at.pm_node_indices,*qt.pm_node_indices),set(ho.pm_tids+ao.pm_tids+qo.pm_tids),old[1],active[1])):
        if len(set(owned))!=len(owned):raise ValueError("overlapping writers")
        for pos in range(*bounds):
            if set(nodes[pos].outs)&(olds | (lives-(allowed if pos in owned else set()))):raise ValueError("frame overwrites live authority")
        if any(sum(t in n.outs for n in nodes[slice(*bounds)])!=1 for t in allowed):raise ValueError("output writer ambiguity")
    sm_frame=list(ir.sm_nodes[ss:se]);pm_frame=list(ir.pm_nodes[ps:pe])
    sm_nodes_name,pm_nodes_name,sm_final_name,pm_final_name=(f'{segment_id}_{z}' for z in ('sm_nodes','pm_nodes','sm_final','pm_final'))
    lines=[f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",f"@[irreducible] private def {sm_final_name} (s : Store) : Store := {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"@[irreducible] private def {pm_final_name} (s : Store) : Store := {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s"]
    def writer(name, graph, initial, final_name, nodes_name, frame, position, node):
        final, theorem_name = f"({final_name} {initial})", f"{segment_id}_{name}"
        expression = f"bw_embedding ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        proof = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame, position=position,
            output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs}, expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_embedding_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]}",
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in proof)
        lines.extend(["  exact hout", ""])
        return theorem_name

    helpers={}
    for label,tr in (('H',ht),('Q',qt)):
        helpers[label]=(writer(label+'Sm',ir.sm_graph_ref,'smStore',sm_final_name,sm_nodes_name,sm_frame,tr.sm_node_indices[0]-ss,ir.sm_nodes[tr.sm_node_indices[0]]),tuple(writer(label+f'Pm{rank}',ir.pm_graph_ref,'pmStore',pm_final_name,pm_nodes_name,pm_frame,pos-ps,ir.pm_nodes[pos]) for rank,pos in enumerate(tr.pm_node_indices)))
    pf,pn,pmframe=pm_final_name,pm_nodes_name,pm_frame
    awriters=[]
    for rank,(p,n) in enumerate(zip(at.pm_node_indices,anodes)):
        final=f"({pf} store)";th=f"{segment_id}_hAllToAll{rank}"
        expr=f"allToAllPrimWithDims {ir.pm_graph_ref}.numRanks {rank} ["+", ".join(f"{{store}} {u}" for u in ai.pm_tids)+f"] {di} {do}"
        lines.extend([f"private theorem {th} (store : Store) : {final} {n.outs[0]} = {expr.format(store=final)} := by",f"  have hfinal : {final} = {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store := by unfold {pf}; rfl"])
        helper=_render_mixed_final_value(name="hout",graph=ir.pm_graph_ref,initial_store="store",final_store=final,final_equality="hfinal",nodes_name=pn,nodes=pmframe,position=p-ps,output_tid=n.outs[0],input_tids=ai.pm_tids,written_tids={u for n in pmframe for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"simpa only [List.map] using applyNode_allToAllPrimWithDims_out {ir.pm_graph_ref} t {rank} [{', '.join(map(str,ai.pm_tids))}] {n.outs[0]} {di} {do}"])
        lines.extend(z[2:] if z.startswith("  ") else z for z in helper);lines.extend(["  exact hout",""]);awriters.append(th)
    vals=lambda r:"["+", ".join(f"pmFinal {u}" for u in r.pm_tids)+"]"
    shape=lambda s:_shape_text(list(s))
    a_theorem=ac.lean_theorem
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",f"  let smFinal := {sm_final_name} smStore",f"  let pmFinal := {pm_final_name} pmStore",f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"    unfold smFinal pmFinal {sm_final_name} {pm_final_name}",f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate <;> native_decide"])
    start=len(lines)
    al,aol=vals(ai),vals(ao)
    lines.extend([f" have hai : {ai.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f" change ShardedRel (smFinal {ai.sm_tid}) {al} {di} {shape(ai.full_shape)} {shape(ai.shard_shape)} at hai"])
    for r,th in enumerate(awriters):
        lines.append(f" have hA{r} : pmFinal {ao.pm_tids[r]} = allToAllPrimWithDims {k} {r} {al} {di} {do} := {th} pmStore")
    lines.extend([f" have hHead : (({al}.head?.map (fun t => t.shape)).getD []) = {shape(ai.shard_shape)} := hai.shard_shapes _ (by simp)",f" have hAV : smFinal {ai.sm_tid} = allGatherPrimDimN {di} {k} 0 {al} := by simpa only [List.length_cons,List.length_nil] using hai.full_value",f" have hGS : (allGatherPrimDimN {di} {k} 0 {al}).shape = {shape(ai.full_shape)} := by rw [←hAV]; exact hai.full_shape",f" have hOd : {do} < (allGatherPrimDimN {di} {k} 0 {al}).shape.length := by rw [hGS]; decide",f" have hDv : (allGatherPrimDimN {di} {k} 0 {al}).shape.getD {do} 0 % {k} = 0 := by rw [hGS]; decide"])
    for r in range(k):lines.append(f" have hAS{r} : (pmFinal {ao.pm_tids[r]}).shape = {shape(ao.shard_shape)} := by rw [hA{r},allToAllPrimWithDims_shape {k} {r} {al} {di} {do} {shape(ai.shard_shape)} hHead (by decide)]; decide")
    lines.extend([f" have hOrd : {aol} = List.ofFn (fun r : Fin {k} => allToAllPrimWithDims {k} r.1 {al} {di} {do}) := by rw ["+", ".join(f"hA{r}" for r in range(k))+"]; rfl",f" have hAC : allGatherPrimDimN {do} {aol}.length 0 {aol} = allGatherPrimDimN {di} {k} 0 {al} := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using ({a_theorem} {di} {do} {al} (by simp) hOd hDv)",f" have houtA : {ao.fact_id}.Holds smFinal pmFinal := by",f"   change ShardedRel (smFinal {ao.sm_tid}) {aol} {do} {shape(ao.full_shape)} {shape(ao.shard_shape)}","   refine { full_value := ?_, full_shape := hai.full_shape, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }","   · rw [hAC]; exact hAV","   · simp only [List.forall_mem_cons]; exact ⟨"+", ".join(f"hAS{r}" for r in range(k))+", List.forall_mem_nil _⟩","   · simp only [List.length_cons,List.length_nil]; decide"])
    lines[start:]=[" "+z for z in lines[start:]]
    for label,cert,gradient,ids,weight,output in (('H',hc,hg,hi,hw,ho),('Q',qc,qg,qi,qw,qo)):
        local=[]
        _embedding_math(local,label,cert,gradient,ids,weight,output,helpers[label],_shape_text)
        lines.append(f"  have hout{label} : {output.fact_id}.Holds smFinal pmFinal := by")
        lines.extend('  '+z for z in local)
        lines.append('    exact hout')
    freshtext=', '.join((ho.fact_id,ao.fact_id,qo.fact_id))
    lines.extend(['  intro fact hfact',f'  have hc : fact ∈ [{freshtext}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{freshtext}] ++ {before.state_id}.facts by native_decide) hfact','  simp only [List.mem_append] at hc','  rcases hc with fresh | old','  · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh','    rcases fresh with rfl | rfl | rfl','    · exact houtH','    · exact houtA','    · exact houtQ','  · exact hframe fact old',f'private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where',f'  smNodes := {sm_nodes_name}',f'  pmNodes := {pm_nodes_name}',f'  sound := by intro a b h; have z := {segment_id}_sound a b h; unfold {sm_final_name} {pm_final_name} at z; exact z',''])
    return '\n'.join(lines)


def _embedding_math(lines,label,cert,gradient,ids,weight,output,helpers,_shape_text):
    k=cert.rank_count
    sm_helper,pm_helpers=helpers
    gradients='['+', '.join(f'pmFinal {t}' for t in gradient.pm_tids)+']'
    weights='['+', '.join(f'pmFinal {t}' for t in weight.pm_tids)+']'
    outputs='['+', '.join(f'pmFinal {t}' for t in output.pm_tids)+']'
    full,shard=_shape_text(list(output.full_shape)),_shape_text(list(output.shard_shape))
    if label=='H':
        b,s,v,d=cert.batch_size,cert.sequence_size,cert.vocab_size,cert.shard_hidden
        theorem=cert.lean_theorem
        lines.extend([
            f"  have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {gradient.sm_tid}) {gradients} 2 {_shape_text(list(gradient.full_shape))} {_shape_text(list(gradient.shard_shape))} at hg",
            f"  have hgV : smFinal {gradient.sm_tid} = allGatherPrimDimN 2 {k} 0 {gradients} := by",
            "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
            f"  have hi : {ids.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {ids.sm_tid}) [pmFinal {ids.pm_tids[0]}] 0 {_shape_text(list(ids.full_shape))} {_shape_text(list(ids.shard_shape))} at hi",
            f"  have hiShape := hi.shard_shapes (pmFinal {ids.pm_tids[0]}) (by simp)",
            f"  have hiEq : smFinal {ids.sm_tid} = pmFinal {ids.pm_tids[0]} := by",
            "    rw [hi.full_value]",
            "    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)",
            f"  have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {weight.sm_tid}) {weights} 1 {full} {shard} at hw",
            f"  have hwV : smFinal {weight.sm_tid} = allGatherPrimDimN 1 {k} 0 {weights} := by",
            "    simpa only [List.length_cons, List.length_nil] using hw.full_value",
            f"  have hSm := {sm_helper} smStore",
            f"  change smFinal {output.sm_tid} = bw_embedding (smFinal {gradient.sm_tid}) (smFinal {ids.sm_tid}) (smFinal {weight.sm_tid}) at hSm",
        ])
        for rank, helper in enumerate(pm_helpers):
            lines.extend([
                f"  have hPm{rank} := {helper} pmStore",
                f"  change pmFinal {output.pm_tids[rank]} = bw_embedding "
                f"(pmFinal {gradient.pm_tids[rank]}) (pmFinal {ids.pm_tids[0]}) (pmFinal {weight.pm_tids[rank]}) at hPm{rank}",
                f"  have houtShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
                f"    rw [hPm{rank}, bw_embedding_shape]",
                f"    exact hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
            ])
        lines.extend([
            f"  have hComm := {theorem} {k} {b} {s} {v} {d}",
            f"    {gradients} {weights} (pmFinal {ids.pm_tids[0]})",
            "    (by decide) (by decide) (by decide) (by decide) (by decide)",
            "    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape",
            "  simp only [List.zipWith] at hComm",
            f"  have hValue : smFinal {output.sm_tid} = allGatherPrimDimN 1 {k} 0 {outputs} := by",
            "    rw [hSm, hgV, hiEq, hwV, hComm]",
            "    rw [" + ", ".join(f"← hPm{rank}" for rank in range(k)) + "]",
            f"  have hValueL : smFinal {output.sm_tid} = allGatherPrimDimN 1 {outputs}.length 0 {outputs} := by",
            "    simpa only [List.length_cons, List.length_nil] using hValue",
            f"  have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
            "    rw [hSm, bw_embedding_shape]", "    exact hw.full_shape",
            f"  have hout : {output.fact_id}.Holds smFinal pmFinal := by",
            f"    change ShardedRel (smFinal {output.sm_tid}) {outputs} 1 {full} {shard}",
            "    refine {", "      full_value := hValueL", "      full_shape := hFullShape",
            "      shards_nonempty := by simp", "      gather_dim_lt := by native_decide",
            "      shard_shapes := ?_",
            "      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide", "    }",
            "    intro x hx", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx",
            "    rcases hx with " + " | ".join("rfl" for _ in range(k)),
        ])
        for rank in range(k):
            lines.append(f"    · exact houtShape{rank}")
    else:
        b,s,hidden,vocab=cert.batch_size,cert.shard_sequence,cert.hidden_size,cert.vocab_size
        ids_values='['+', '.join(f'pmFinal {t}' for t in ids.pm_tids)+']'
        weight_tid=weight.pm_tids[0]
        lines.extend([
            f"  have hg : {gradient.fact_id}.Holds smFinal pmFinal := houtA",
            f"  change ShardedRel (smFinal {gradient.sm_tid}) {gradients} 1 [{b}, {s * k}, {hidden}] [{b}, {s}, {hidden}] at hg",
            f"  have hi : {ids.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ChunkedRel (smFinal {ids.sm_tid}) {ids_values} 1 [{b}, {s * k}] [{b}, {s}] at hi",
            f"  have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {weight.sm_tid}) [pmFinal {weight_tid}] 0 [{vocab}, {hidden}] [{vocab}, {hidden}] at hw",
            f"  have hwEq : smFinal {weight.sm_tid} = pmFinal {weight_tid} := by",
            "    rw [hw.full_value]",
            f"    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal {weight_tid}) (by simp)]; native_decide)",
            f"  have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 1 {k} 0 {gradients} := by",
            "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
            f"  have hSm := {sm_helper} smStore",
            f"  change smFinal {output.sm_tid} = bw_embedding (smFinal {gradient.sm_tid})",
            f"    (smFinal {ids.sm_tid}) (smFinal {weight.sm_tid}) at hSm",
        ])
        for rank, helper in enumerate(pm_helpers):
            lines.extend([
                f"  have hPm{rank} := {helper} pmStore",
                f"  change pmFinal {output.pm_tids[rank]} =",
                f"    bw_embedding (pmFinal {gradient.pm_tids[rank]})",
                f"      (pmFinal {ids.pm_tids[rank]}) (pmFinal {weight_tid}) at hPm{rank}",
            ])
        lines.extend([
            f"  have hComm := {cert.lean_theorem} {k} {b} {s} {hidden} {vocab}",
            f"    {gradients} (smFinal {ids.sm_tid}) (pmFinal {weight_tid})",
            "    (by decide) (by decide) (by decide) (by decide) (by decide)",
            "    (by rfl) hg.shard_shapes hi.full_shape",
            f"    (hw.shard_shapes (pmFinal {weight_tid}) (by simp))",
            "  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,",
            "    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,",
            "    List.getElem?_cons_succ, Option.getD_some] at hComm",
        ])
        for rank in range(k):
            lines.extend([
                f"  have hIdChunk{rank} := hi.chunk_values {rank} (by simp)",
                f"  simp [List.getD] at hIdChunk{rank}",
            ])
        lines.extend([
            f"  have hValue : smFinal {output.sm_tid} = tensorSum {outputs} := by",
            "    rw [hSm, hgValue, hwEq, hComm]",
        ])
        for rank in range(k):
            lines.extend([
                f"    rw [← hIdChunk{rank}]",
                f"    rw [← hPm{rank}]",
            ])
        lines.extend([
            f"  have hValueReduce : smFinal {output.sm_tid} =",
            f"      allReducePrim {outputs}.length 0 {outputs} := by",
            "    rw [hValue]", "    rfl",
            f"  have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
            "    rw [hSm, bw_embedding_shape]", "    exact hw.full_shape",
        ])
        contribution_shapes = []
        for rank in range(k):
            contribution_shapes.extend([
                f"  have hShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
                f"    rw [hPm{rank}, bw_embedding_shape]",
                "    exact hw.shard_shapes _ (by simp)",
            ])
        lines.extend(contribution_shapes)
        lines.extend([
            f"  have hout : {output.fact_id}.Holds smFinal pmFinal := by",
            f"    change ReductionRel (smFinal {output.sm_tid}) {outputs} {full}",
            "    refine {", "      full_value := hValueReduce",
            "      full_shape := hFullShape", "      contributions_nonempty := by simp",
            "      contribution_shapes := ?_", "      reduced_shape := ?_", "    }",
            "    · intro contribution hmem",
            "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            "      rcases hmem with " + " | ".join("rfl" for _ in range(k)),
            *(f"      · exact hShape{rank}" for rank in range(k)),
            "    · rw [← hValueReduce]", "      exact hFullShape",
        ])
