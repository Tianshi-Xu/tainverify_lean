"""Atomic row-linear/head-matmul replay over one shared full-frame fold pair.

The existing family emitters provide semantic proofs, not sequential certificates:
both see the same initial state and identical ordered authority lists. Their local
store declarations are factored out before publication; no projection owns a fold.
"""
from copy import copy
from dataclasses import replace


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_bw_row_linear_head_matmul_segment(ir, relation, segment_id):
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .composer import _node_text
        from .bw_linear_dual_renderer import render_closed_k_rank_bw_linear_dual_segment as row
        from .bw_matmul_head_renderer import render_closed_bw_matmul_head_segment as head
    except ImportError:
        from composer import _node_text
        from bw_linear_dual_renderer import render_closed_k_rank_bw_linear_dual_segment as row
        from bw_matmul_head_renderer import render_closed_bw_matmul_head_segment as head
    chain=relation.dependent_chain_plan
    seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=4:
        raise ValueError('row/head atomic component requires four projections')
    tm={t.transition_id:t for t in relation.transition_specs}
    if len(tm)!=len(relation.transition_specs): raise ValueError('duplicate transition identity')
    try: selected=tuple(tm[t] for t in seg.transition_ids)
    except KeyError as exc: raise ValueError('missing transition identity') from exc
    row_rules={'bw-linear-dx-row-reduction-k-rank','bw-linear-dw-output-row-sharded-k-rank'}
    rows=tuple(t for t in selected if t.rule_id in row_rules)
    heads=tuple(sorted((t for t in selected if t.rule_id=='bw-matmul-head-sharded-k-rank'),key=lambda t:t.lean_theorem))
    if len(rows)!=2 or {t.rule_id for t in rows}!=row_rules or len(heads)!=2:
        raise ValueError('row/head exact typed family mismatch')
    rs={r.source:r for r in chain.relation_facts}; ids={r.fact_id:r for r in chain.relation_facts}
    if len(rs)!=len(chain.relation_facts) or len(ids)!=len(chain.relation_facts): raise ValueError('ambiguous materialized facts')
    states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    try:
        fresh={rs[f].fact_id for t in selected for f in t.post_facts}
        required={rs[f].fact_id for t in selected for f in t.pre_facts}
    except KeyError as exc:
        raise ValueError('unmaterialized semantic source') from exc
    if (len(fresh)!=4 or fresh & set(before.fact_ids) or not required<=set(before.fact_ids)
            or not fresh<=set(after.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh):
        raise ValueError('row/head source dependencies or live-state mismatch')
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if not (0<=ss<=se<=len(ir.sm_nodes) and 0<=ps<=pe<=len(ir.pm_nodes)):
        raise ValueError('invalid complete authority frame')
    # Independently resolve canonical sources at the appropriate frontier.  A
    # recomputed certificate digest cannot authenticate a stale materialized TID.
    def resolve(ref,side,limit):
        nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
        fields=ref.split(':')
        if len(fields)==2 and fields[0]=='init' and fields[1].isdigit():
            tid=int(fields[1]); index=None
        elif len(fields)==3 and fields[0]==side and all(x.isdigit() for x in fields[1:]):
            index,slot=map(int,fields[1:])
            if index>=limit or slot>=len(nodes[index].outs): raise ValueError('source reference outside frontier')
            tid=nodes[index].outs[slot]
        else: raise ValueError('noncanonical source reference')
        latest=next((j for j in range(limit-1,-1,-1) if tid in nodes[j].outs),None)
        if latest!=index: raise ValueError('source is not latest writer')
        return tid
    for fid in required|fresh:
        r=ids[fid];s=r.source;sl,pl=(se,pe) if fid in fresh else (ss,ps)
        if (s.layout!=r.kind or s.gather_dim!=r.gather_dim or s.source_step_triples
                or r.source_tid_triples or r.metadata_tid is not None or r.metadata_region_id is not None
                or r.row_shard_shape is not None or not s.step_triple):
            raise ValueError('source layout/axis metadata mismatch')
        if resolve(s.step_triple[0],'sm',sl)!=r.sm_tid: raise ValueError('source SM TID mismatch')
        if r.kind=='joined':
            if (len(s.step_triple)!=1 or r.pm_tids or s.joined_pm_step is None or
                    resolve(s.joined_pm_step,'pm',pl)!=r.joined_pm_tid): raise ValueError('joined source mismatch')
        elif (s.joined_pm_step is not None or r.joined_pm_tid is not None or
                tuple(resolve(ref,'pm',pl) for ref in s.step_triple[1:])!=r.pm_tids):
            raise ValueError('ordered PM source TIDs mismatch')
    # Every fresh output belongs to its exact writer in its own store. Remaining
    # frame authority (including anchor) is checked by the row backend below.
    for side,start,end,nodes in (('sm',ss,se,ir.sm_nodes),('pm',ps,pe,ir.pm_nodes)):
        allowed={}
        for t in selected:
            indices=t.sm_node_indices if side=='sm' else t.pm_node_indices
            if len(set(indices))!=len(indices) or tuple(sorted(indices))!=indices or not set(indices)<=set(range(start,end)):
                raise ValueError('unordered or out-of-frame writer footprint')
            for f in t.post_facts:
                r=rs[f];tids=(r.sm_tid,) if side=='sm' else r.pm_tids
                if len(tids)!=len(indices): raise ValueError('writer arity mismatch')
                for tid,index in zip(tids,indices):
                    if tid in allowed and allowed[tid]!=index: raise ValueError('shared output owner mismatch')
                    allowed[tid]=index
        for tid,index in allowed.items():
            if [j for j in range(start,end) if tid in nodes[j].outs]!=[index]:
                raise ValueError('frame overwrites output or output owner mismatch')
    sn,pn=f'{segment_id}_sm_nodes',f'{segment_id}_pm_nodes'
    sf,pf=f'{segment_id}_sm_final',f'{segment_id}_pm_final'
    lines=[f'private def {sn} : List NodeDecl := [{", ".join(_node_text(n) for n in ir.sm_nodes[ss:se])}]',
           f'private def {pn} : List NodeDecl := [{", ".join(_node_text(n) for n in ir.pm_nodes[ps:pe])}]',
           f'private def {sf} (s : Store) : Store := {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s',
           f'private def {pf} (s : Store) : Store := {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s']
    results=[]
    for suffix,trans,backend in (('row',rows,row),('head',heads,head)):
        local=f'{segment_id}_{suffix}'
        output=replace(after,state_id=f'{local}_post',fact_ids=tuple(dict.fromkeys((*before.fact_ids,*(rs[f].fact_id for t in trans for f in t.post_facts)))))
        local_chain=copy(chain)
        # copy supports both frozen production dataclasses and portable namespaces.
        object.__setattr__(local_chain,'states',(*chain.states,output))
        object.__setattr__(local_chain,'segments',(replace(seg,segment_id=local,post_state_id=output.state_id,transition_ids=tuple(t.transition_id for t in trans)),))
        local_rel=copy(relation);object.__setattr__(local_rel,'dependent_chain_plan',local_chain)
        source=backend(ir,local_rel,local)
        marker=f'private theorem {local}_'
        if marker not in source or f'private def {local}:' not in source.replace(f'private def {local} :',f'private def {local}:'):
            raise ValueError('semantic backend declaration boundary changed')
        source=source[source.index(marker):]
        # Discard standalone certificates: only the combined certificate is public.
        import re
        source=re.split(r'private def '+re.escape(local)+r'\s*:',source,maxsplit=1)[0]
        # A trailing scoped option belongs to the discarded certificate.
        source=re.sub(r'\nset_option maxRecDepth \d+ in\s*$','\n',source)
        for old,new in ((f'{local}_sm_nodes',sn),(f'{local}_pm_nodes',pn),(f'{local}_sm_final',sf),(f'{local}_pm_final',pf)):
            source=source.replace(old,new)
        lines.extend([f'private def {output.state_id} : RelationState where',f'  facts := [{", ".join(output.fact_ids)}]','  nonempty := by decide',source])
        results.append((local,output))
    lines.extend([f'private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where',f'  smNodes := {sn}',f'  pmNodes := {pn}','  sound := by','    intro smStore pmStore hstate'])
    for j,(local,_) in enumerate(results): lines.append(f'    have h{j} := {local}_sound smStore pmStore hstate')
    lines.extend([f'    change {after.state_id}.Holds ({sf} smStore) ({pf} pmStore)','    intro fact hfact',f'    have hc : fact ∈ {results[0][1].state_id}.facts ∨ fact ∈ {results[1][1].state_id}.facts := by',f'      have hsub : {after.state_id}.facts ⊆ {results[0][1].state_id}.facts ++ {results[1][1].state_id}.facts := by native_decide','      exact List.mem_append.mp (hsub hfact)','    rcases hc with h | h','    · exact h0 fact h','    · exact h1 fact h',''])
    return '\n'.join(lines)
