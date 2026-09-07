"""Closed atomic sequence BW_view + dependent AllToAll→BW_div, one fold/store."""
from __future__ import annotations
import re


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_bw_flatten_alltoall_div_segment(ir, relation, segment_id):
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from .relation_compiler import KRankBWViewFlattenCertificate, KRankAllToAllRelationCertificate, KRankDivCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from relation_compiler import KRankBWViewFlattenCertificate, KRankAllToAllRelationCertificate, KRankDivCertificate
    chain=relation.dependent_chain_plan
    seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    tm={t.transition_id:t for t in relation.transition_specs}
    if seg is None or len(seg.transition_ids)!=3 or len(tm)!=len(relation.transition_specs):raise ValueError('atomic transition identity')
    try: ts={tm[u].rule_id:tm[u] for u in seg.transition_ids}
    except KeyError as exc:raise ValueError('missing transition') from exc
    keys=('bw-view-flatten-sequence-sharded-k-rank','alltoall-k-rank-layout-transport','div-sharded-k-rank-dim3')
    ths=('TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3','TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn','TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128')
    if set(ts)!=set(keys):raise ValueError('atomic family identity')
    v,a,d=(ts[key] for key in keys)
    vc,ac,dc=(_select_exact_typed_certificate(relation,ts[key],key,th,typ,lambda c:((c.input_fact,),(c.output_fact,))) for key,th,typ in zip(keys,ths,(KRankBWViewFlattenCertificate,KRankAllToAllRelationCertificate,KRankDivCertificate)))
    rec={r.source:r for r in chain.relation_facts};byid={r.fact_id:r for r in chain.relation_facts}
    if len(rec)!=len(chain.relation_facts) or len(byid)!=len(rec):raise ValueError('ambiguous fact')
    try:vi,vo,ai,ao,di,do=(rec[f] for c in (vc,ac,dc) for f in (c.input_fact,c.output_fact))
    except KeyError as exc:raise ValueError('missing fact') from exc
    k=vc.rank_count
    if type(k) is not int or k<1 or k!=ir.pm_num_ranks or ac.rank_count!=k or dc.rank_count!=k:raise ValueError('rank authority')
    if ac.output_fact!=dc.input_fact or ac.input_gather_dim!=1 or ac.output_gather_dim!=3 or dc.gather_dim!=3:raise ValueError('dependent axes')
    if type(dc.scalar_param) is not int or dc.scalar_param<0:raise ValueError('scalar parameter')
    if len(vi.shard_shape)!=4:raise ValueError('view shape')
    b,s,n,h=vi.shard_shape
    if vi.shard_shape!=(b,s,n,h) or vo.shard_shape!=(b,s,n*h) or vo.full_shape!=(b,s*k,n*h):raise ValueError('flatten shape')
    if len(ai.shard_shape)!=4 or ai.full_shape!=ao.full_shape or ao.full_shape!=do.full_shape or ao.shard_shape!=do.shard_shape or dc.full_shape!=do.full_shape or dc.shard_shape!=do.shard_shape:raise ValueError('collective/div shape')
    def resolve(ref,side):
        m=re.fullmatch(r'init:(0|[1-9][0-9]*)',ref)
        if m:return int(m[1])
        m=re.fullmatch(r'(sm|pm):(0|[1-9][0-9]*):(0|[1-9][0-9]*)',ref)
        nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
        if not m or m[1]!=side or int(m[2])>=len(nodes) or int(m[3])>=len(nodes[int(m[2])].outs):raise ValueError('source reference')
        return nodes[int(m[2])].outs[int(m[3])]
    def record(r,axis):
        f=r.source;full=list(r.shard_shape);full[axis]*=k
        if (r.kind!='sharded' or f.layout!='sharded' or r.gather_dim!=axis or f.gather_dim!=axis or tuple(full)!=r.full_shape
            or any(type(z) is not int or z<=0 for z in r.shard_shape) or len(r.pm_tids)!=k or len(set(r.pm_tids))!=k
            or len(f.step_triple)!=k+1 or r.metadata_tid is not None or r.metadata_region_id is not None or r.row_shard_shape is not None
            or r.source_tid_triples or r.joined_pm_tid is not None or f.source_step_triples or f.joined_pm_step is not None):raise ValueError('record shape/axis')
        if resolve(f.step_triple[0],'sm')!=r.sm_tid or tuple(resolve(u,'pm') for u in f.step_triple[1:])!=r.pm_tids:raise ValueError('source TID')
    for r,axis in ((vi,1),(vo,1),(ai,1),(ao,3),(do,3)):record(r,axis)
    if ai.sm_tid!=ao.sm_tid or ai.source.step_triple[0]!=ao.source.step_triple[0]:raise ValueError('collective SM authority')
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if not 0<=ss<=se<=len(ir.sm_nodes) or not 0<=ps<=pe<=len(ir.pm_nodes):raise ValueError('frame range')
    for t,c,out in ((v,vc,vo),(a,ac,ao),(d,dc,do)):
        if len(t.sm_node_indices)!=(0 if t is a else 1) or len(t.pm_node_indices)!=k or tuple(sorted(set(t.pm_node_indices)))!=t.pm_node_indices:raise ValueError('ordered footprint')
        if not set(t.sm_node_indices)<=set(range(ss,se)) or not set(t.pm_node_indices)<=set(range(ps,pe)):raise ValueError('writer outside frame')
        if c.pm_step_ids!=tuple(f'pm:{p}:0' for p in t.pm_node_indices) or out.source.step_triple[1:]!=c.pm_step_ids:raise ValueError('PM certificate footprint')
        if t is not a and (c.sm_step_id!=f'sm:{t.sm_node_indices[0]}:0' or out.source.step_triple[0]!=c.sm_step_id):raise ValueError('SM certificate footprint')
    if set(v.sm_node_indices)&set(d.sm_node_indices) or any(set(x.pm_node_indices)&set(y.pm_node_indices) for x,y in ((v,a),(v,d),(a,d))):raise ValueError('overlapping writers')
    def latest(ref,side,pos):
        tid=resolve(ref,side);nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
        writes=[(j,q) for j,node in enumerate(nodes[:pos]) for q,u in enumerate(node.outs) if u==tid]
        expected=f'{side}:{writes[-1][0]}:{writes[-1][1]}' if writes else f'init:{tid}'
        if ref!=expected:raise ValueError('source not latest before read')
    for t,c,inp,out,op in ((v,vc,vi,vo,'BW_view'),(d,dc,di,do,'BW_div')):
        for side,positions in (('sm',t.sm_node_indices),('pm',t.pm_node_indices)):
            for rank,pos in enumerate(positions):
                node=(ir.sm_nodes if side=='sm' else ir.pm_nodes)[pos]
                it=inp.sm_tid if side=='sm' else inp.pm_tids[rank];ot=out.sm_tid if side=='sm' else out.pm_tids[rank]
                params=list(out.full_shape if side=='sm' else out.shard_shape) if op=='BW_view' else [dc.scalar_param]
                if node.op!=op or node.rank!=rank or len(node.ins)!=2 or node.ins[0]!=it or node.outs!=[ot] or node.params!=params:raise ValueError('writer roles/params')
                latest(inp.source.step_triple[0 if side=='sm' else rank+1],side,pos)
    latest(ai.source.step_triple[0],'sm',ss)
    for rank,pos in enumerate(a.pm_node_indices):
        node=ir.pm_nodes[pos]
        if node.op!='AllToAllPrim' or node.rank!=rank or node.ins!=list(ai.pm_tids) or node.outs!=[ao.pm_tids[rank]] or node.params!=[1,3]:raise ValueError('AllToAll roles/params')
        for ref in ai.source.step_triple[1:]:latest(ref,'pm',pos)
    states={z.state_id:z for z in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    fresh={vo.fact_id,ao.fact_id,do.fact_id}
    if not {vi.fact_id,ai.fact_id}<=set(before.fact_ids) or fresh&set(before.fact_ids) or not {vo.fact_id,do.fact_id}<=set(after.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh:raise ValueError('state liveness')
    authority={z.fact_id:z for z in chain.authority_facts}
    if chain.anchor_fact is not None:authority[chain.anchor_fact.fact_id]=chain.anchor_fact
    def live(ids):
        sm,pm=set(),set()
        for fid in ids:
            if fid in byid:
                r=byid[fid];sm.add(r.sm_tid);pm.update(r.pm_tids)
                if r.joined_pm_tid is not None:pm.add(r.joined_pm_tid)
                if r.metadata_tid is not None:sm.add(r.metadata_tid);pm.add(r.metadata_tid)
                for x,y,z in r.source_tid_triples:sm.add(x);pm.update((y,z))
            elif fid in authority:
                z=authority[fid]
                if z.kind in ('tensor_shape','packed_cu','label_bound') and z.side in ('sm','pm'):(sm if z.side=='sm' else pm).add(z.tid)
                elif z.kind=='tensor_eq' and z.left_side in ('sm','pm') and z.right_side in ('sm','pm'):
                    (sm if z.left_side=='sm' else pm).add(z.left_tid);(sm if z.right_side=='sm' else pm).add(z.right_tid)
                elif z.kind=='gather':sm.add(z.sm_tid);pm.update((z.pm_rank0_tid,z.pm_rank1_tid))
                else:raise ValueError('unsupported live authority')
            else:raise ValueError('unknown live fact')
        return sm,pm
    old=live(before.fact_ids);alllive=live(set(before.fact_ids)|set(after.fact_ids))
    smframe=list(ir.sm_nodes[ss:se]);pmframe=list(ir.pm_nodes[ps:pe])
    for frame,start,owned,allowed,olds,lives in ((smframe,ss,set(v.sm_node_indices)|set(d.sm_node_indices),{vo.sm_tid,do.sm_tid},old[0],alllive[0]),(pmframe,ps,set(v.pm_node_indices)|set(a.pm_node_indices)|set(d.pm_node_indices),set(vo.pm_tids+ao.pm_tids+do.pm_tids),old[1],alllive[1])):
        for p,node in enumerate(frame,start):
            if set(node.outs)&(olds|(lives-(allowed if p in owned else set()))):raise ValueError('live authority overwrite')
        if any(sum(tid in node.outs for node in frame)!=1 for tid in allowed):raise ValueError('latest output writer')
    sn,pn,sf,pf=(f'{segment_id}_{z}' for z in ('sm_nodes','pm_nodes','sm_final','pm_final'))
    lines=[f"private def {sn} : List NodeDecl := [{', '.join(_node_text(z) for z in smframe)}]",f"private def {pn} : List NodeDecl := [{', '.join(_node_text(z) for z in pmframe)}]",f'@[irreducible] private def {sf} (s : Store) : Store := {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s',f'@[irreducible] private def {pf} (s : Store) : Store := {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s']
    shape=lambda z:_shape_text(list(z))
    vals=lambda r:'['+', '.join(f'pmFinal {u}' for u in r.pm_tids)+']'
    def writer(name,side,pos):
        graph,fn,nn,frame,start=(ir.sm_graph_ref,sf,sn,smframe,ss) if side=='sm' else (ir.pm_graph_ref,pf,pn,pmframe,ps)
        node=frame[pos-start];final=f'({fn} store)';out=node.outs[0]
        if node.op=='BW_view':
            expr=f'fw_view {shape(node.params)} ({{store}} {node.ins[0]})';inputs=(node.ins[0],)
            apply=f'exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {shape(node.params[1:])} {node.ins[0]} {node.ins[1]} {out}'
        elif node.op=='BW_div':
            expr=f'bw_div ({dc.scalar_param} : Scalar) ({{store}} {node.ins[0]})';inputs=(node.ins[0],)
            apply=f'exact applyNode_bw_div_out_g128 {graph} t {node.rank} {dc.scalar_param} {node.ins[0]} {node.ins[1]} {out}'
        else:
            expr=f'allToAllPrimWithDims {graph}.numRanks {node.rank} ['+', '.join(f'{{store}} {u}' for u in node.ins)+'] 1 3';inputs=tuple(node.ins)
            apply=f'simpa only [List.map] using applyNode_allToAllPrimWithDims_out {graph} t {node.rank} {list(node.ins)} {out} 1 3'
        th=f'{segment_id}_{name}'
        lines.extend([f'private theorem {th} (store : Store) : {final} {out} = {expr.format(store=final)} := by',f'  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) store := by unfold {fn}; rfl'])
        helper=_render_mixed_final_value(name='hout',graph=graph,initial_store='store',final_store=final,final_equality='hfinal',nodes_name=nn,nodes=frame,position=pos-start,output_tid=out,input_tids=inputs,written_tids={u for z in frame for u in z.outs},expression=expr,apply_lines=['rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]','simp [applyNodeDistributed, applyNodeRingAttn]',apply])
        lines.extend(z[2:] if z.startswith('  ') else z for z in helper);lines.append('  exact hout');return th
    hs=writer('hViewS','sm',v.sm_node_indices[0]);hp=[writer(f'hViewP{r}','pm',p) for r,p in enumerate(v.pm_node_indices)]
    ads=[writer(f'hA{r}','pm',p) for r,p in enumerate(a.pm_node_indices)]
    ds=writer('hDivS','sm',d.sm_node_indices[0]);dp=[writer(f'hDivP{r}','pm',p) for r,p in enumerate(d.pm_node_indices)]
    lines.extend(['set_option maxHeartbeats 500000 in',f'private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({sf} smStore) ({pf} pmStore) := by',f' let smFinal := {sf} smStore',f' let pmFinal := {pf} pmStore',f' have hframe : {before.state_id}.Holds smFinal pmFinal := by unfold smFinal pmFinal {sf} {pf}; apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide'])
    def input_fact(name,r):
        lines.extend([f' have {name} : {r.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)',f' change ShardedRel (smFinal {r.sm_tid}) {vals(r)} {r.gather_dim} {shape(r.full_shape)} {shape(r.shard_shape)} at {name}'])
    def publish(name,r,value,full,shapes):
        lines.extend([f' have {name} : {r.fact_id}.Holds smFinal pmFinal := by',f'   change ShardedRel (smFinal {r.sm_tid}) {vals(r)} {r.gather_dim} {shape(r.full_shape)} {shape(r.shard_shape)}',f'   refine {{ full_value := {value}, full_shape := {full}, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }}','   · simp only [List.forall_mem_cons]; exact ⟨'+', '.join(shapes)+', List.forall_mem_nil _⟩','   · simp only [List.length_cons,List.length_nil]; decide'])
    input_fact('hx',vi);xl,yl=vals(vi),vals(vo)
    lines.extend([f' have hVS : smFinal {vo.sm_tid} = fw_view {shape(vo.full_shape)} (smFinal {vi.sm_tid}) := {hs} smStore',f' have hxV : smFinal {vi.sm_tid} = allGatherPrimDimN 1 {k} 0 {xl} := hx.full_value'])
    for r,th in enumerate(hp):lines.append(f' have hVP{r} : pmFinal {vo.pm_tids[r]} = fw_view {shape(vo.shard_shape)} (pmFinal {vi.pm_tids[r]}) := {th} pmStore')
    lines.extend([f' have hVC := {ths[0]} {k} {b} {s} {n} {h} {xl} (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes',f' have hVV : smFinal {vo.sm_tid} = allGatherPrimDimN 1 {k} 0 {yl} := by rw [hVS,hxV,hVC]; simp only [List.map]; rw ['+', '.join(f'← hVP{r}' for r in range(k))+']',f' have hVF : (smFinal {vo.sm_tid}).shape = {shape(vo.full_shape)} := by rw [hVS]; rfl'])
    for r in range(k):lines.append(f' have hVShape{r} : (pmFinal {vo.pm_tids[r]}).shape = {shape(vo.shard_shape)} := by rw [hVP{r}]; rfl')
    publish('houtV',vo,'hVV','hVF',[f'hVShape{r}' for r in range(k)])
    input_fact('hai',ai);al,aol=vals(ai),vals(ao)
    for r,th in enumerate(ads):lines.append(f' have hA{r} : pmFinal {ao.pm_tids[r]} = allToAllPrimWithDims {k} {r} {al} 1 3 := {th} pmStore')
    lines.extend([f' have hHead : (({al}.head?.map (fun t => t.shape)).getD []) = {shape(ai.shard_shape)} := hai.shard_shapes _ (by simp)',f' have hAV : smFinal {ai.sm_tid} = allGatherPrimDimN 1 {k} 0 {al} := hai.full_value',f' have hGS : (allGatherPrimDimN 1 {k} 0 {al}).shape = {shape(ai.full_shape)} := by rw [← hAV]; exact hai.full_shape',f' have hOd : 3 < (allGatherPrimDimN 1 {k} 0 {al}).shape.length := by rw [hGS]; decide',f' have hDv : (allGatherPrimDimN 1 {k} 0 {al}).shape.getD 3 0 % {k} = 0 := by rw [hGS]; decide'])
    for r in range(k):lines.append(f' have hAS{r} : (pmFinal {ao.pm_tids[r]}).shape = {shape(ao.shard_shape)} := by rw [hA{r},allToAllPrimWithDims_shape {k} {r} {al} 1 3 {shape(ai.shard_shape)} hHead (by decide)]; decide')
    lines.extend([f' have hOrd : {aol} = List.ofFn (fun r : Fin {k} => allToAllPrimWithDims {k} r.1 {al} 1 3) := by rw ['+', '.join(f'hA{r}' for r in range(k))+']; rfl',f' have hAC : allGatherPrimDimN 3 {aol}.length 0 {aol} = allGatherPrimDimN 1 {k} 0 {al} := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using ({ths[1]} 1 3 {al} (by simp) hOd hDv)',f' have hAO : smFinal {ao.sm_tid} = allGatherPrimDimN 3 {aol}.length 0 {aol} := by rw [hAC]; exact hAV'])
    publish('houtA',ao,'hAO','hai.full_shape',[f'hAS{r}' for r in range(k)])
    lines.extend([' have hdi := houtA',f' change ShardedRel (smFinal {di.sm_tid}) {aol} 3 {shape(di.full_shape)} {shape(di.shard_shape)} at hdi',f' have hDS : smFinal {do.sm_tid} = bw_div ({dc.scalar_param} : Scalar) (smFinal {di.sm_tid}) := {ds} smStore'])
    for r,th in enumerate(dp):lines.extend([f' have hDP{r} : pmFinal {do.pm_tids[r]} = bw_div ({dc.scalar_param} : Scalar) (pmFinal {di.pm_tids[r]}) := {th} pmStore',f' have hDShape{r} : (pmFinal {do.pm_tids[r]}).shape = {shape(do.shard_shape)} := by rw [hDP{r},bw_div_shape_g128]; exact hdi.shard_shapes _ (by simp)'])
    lines.extend([f' have hDC := {ths[2]} ({dc.scalar_param} : Scalar) 3 {k} {aol} {shape(di.shard_shape)} (by decide) rfl (hdi.shard_shapes _ (by simp)) (by intro i hi; exact hdi.shard_shapes _ (List.get_mem _ _))',f' have hDV : smFinal {do.sm_tid} = allGatherPrimDimN 3 {k} 0 {vals(do)} := by rw [hDS,hdi.full_value]; simp only [List.length_cons,List.length_nil]; rw [hDC]; simp only [List.map]; rw ['+', '.join(f'← hDP{r}' for r in range(k))+']',f' have hDF : (smFinal {do.sm_tid}).shape = {shape(do.full_shape)} := by rw [hDS,bw_div_shape_g128]; exact hdi.full_shape'])
    publish('houtD',do,'hDV','hDF',[f'hDShape{r}' for r in range(k)])
    freshtext=', '.join((vo.fact_id,ao.fact_id,do.fact_id))
    lines.extend([' intro fact hfact',f' have hc : fact ∈ [{freshtext}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{freshtext}] ++ {before.state_id}.facts by native_decide) hfact',' simp only [List.mem_append] at hc',' rcases hc with fresh | old',' · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh','   rcases fresh with rfl | rfl | rfl','   · exact houtV','   · exact houtA','   · exact houtD',' · exact hframe fact old',f'private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where',f' smNodes := {sn}',f' pmNodes := {pn}',f' sound := by intro x y h; have z := {segment_id}_sound x y h; unfold {sf} {pf} at z; exact z',''])
    return '\n'.join(lines)
