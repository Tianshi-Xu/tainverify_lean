"""Atomic positive mixed transpose/AllToAll tuples; dependency order is not execution order."""
from __future__ import annotations


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_transpose_alltoall_segment(ir, relation, segment_id: str) -> str:
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (
            KRankAllToAllRelationCertificate, KRankTransposeRelationCertificate,
        )
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (
            KRankAllToAllRelationCertificate, KRankTransposeRelationCertificate,
        )

    trule = "transpose-sharded-k-rank"
    arule = "alltoall-k-rank-layout-transport"
    atheorem = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    allowed_transpose = {
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4",
    }
    chain = relation.dependent_chain_plan
    found = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(found) != 1:
        raise ValueError("mixed layout requires one complete segment")
    segment = found[0]
    def unique(items, key):
        result = {}
        for item in items:
            value = key(item)
            if value in result: raise ValueError("duplicate mixed layout authority")
            result[value] = item
        return result
    by_id = unique(relation.transition_specs, lambda t: t.transition_id)
    if len(set(segment.transition_ids)) != len(segment.transition_ids):
        raise ValueError("duplicate transition ownership")
    try: transitions = [by_id[x] for x in segment.transition_ids]
    except KeyError as exc: raise ValueError("missing transition") from exc
    if {t.rule_id for t in transitions} != {trule, arule}:
        raise ValueError("requires positive transpose and AllToAll tuples")
    records = unique(chain.relation_facts, lambda f: f.source)
    all_facts = unique((*chain.relation_facts, *chain.authority_facts, chain.anchor_fact), lambda f: f.fact_id)
    states = unique(chain.states, lambda s: s.state_id)
    try: before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc: raise ValueError("missing state") from exc
    for state in (before, after):
        if not state.fact_ids or len(set(state.fact_ids)) != len(state.fact_ids) or not set(state.fact_ids) <= all_facts.keys():
            raise ValueError("unknown or duplicate active facts")
    if any(chain.anchor_fact.fact_id not in state.fact_ids for state in (before, after)):
        raise ValueError("closed InitGoal anchor is not active")
    ss, se = segment.sm_range; ps, pe = segment.pm_range
    if not (0 <= ss < se <= len(ir.sm_nodes) and 0 <= ps < pe <= len(ir.pm_nodes)):
        raise ValueError("invalid complete frame")
    sm_frame = list(ir.sm_nodes[ss:se]); pm_frame = list(ir.pm_nodes[ps:pe])
    for side, start, end in [('sm',ss,se),('pm',ps,pe)]:
        owned = [i for t in transitions for i in (t.sm_node_indices if side == 'sm' else t.pm_node_indices)]
        if len(set(owned)) != len(owned) or set(owned) != set(range(start,end)):
            raise ValueError("non-exhaustive or overlapping semantic ownership")
    k = ir.pm_num_ranks
    if k <= 0 or ir.sm_num_ranks != 1: raise ValueError("invalid graph rank authority")

    def resolve(ref, side):
        parts = ref.split(':')
        if len(parts) == 2 and parts[0] == 'init' and parts[1].isdigit():
            return int(parts[1]), -1
        if len(parts) != 3 or parts[0] != side or not all(x.isdigit() for x in parts[1:]):
            raise ValueError("malformed source reference")
        index, slot = map(int, parts[1:]); nodes = ir.sm_nodes if side == 'sm' else ir.pm_nodes
        if index >= len(nodes) or slot >= len(nodes[index].outs): raise ValueError("source outside graph")
        return nodes[index].outs[slot], index

    def bind(fact, sm_at, pm_ats):
        refs = fact.source.step_triple
        if (fact.source.layout != 'sharded' or fact.source.gather_dim != fact.gather_dim or len(refs) != k+1
                or fact.source.joined_pm_step is not None or fact.source.source_step_triples
                or fact.metadata_tid is not None or fact.metadata_region_id is not None):
            raise ValueError("source layout/axis/rank mismatch")
        for side, ref, tid, at in [('sm',refs[0],fact.sm_tid,sm_at), *[('pm',ref,tid,at) for ref,tid,at in zip(refs[1:],fact.pm_tids,pm_ats)]]:
            actual, origin = resolve(ref,side)
            nodes = ir.sm_nodes if side == 'sm' else ir.pm_nodes
            latest = max((i for i,n in enumerate(nodes[:at]) if tid in n.outs),default=-1)
            if actual != tid or origin != latest:
                raise ValueError("source does not bind latest writer to ordered TID")

    def shape(f):
        if f.kind != 'sharded' or len(f.pm_tids) != k or len(set(f.pm_tids)) != k:
            raise ValueError("requires ordered ShardedRel")
        dims=list(f.shard_shape)
        if not dims or any(x <= 0 for x in dims) or f.gather_dim not in range(len(dims)):
            raise ValueError("invalid sharded shape")
        dims[f.gather_dim] *= k
        if tuple(dims) != tuple(f.full_shape): raise ValueError("invalid full shape")

    rows=[]
    for t in transitions:
        if len(t.pre_facts)!=1 or len(t.post_facts)!=1 or t.authority_requirements or t.fact_only:
            raise ValueError("unsupported transition roles")
        is_t=t.rule_id==trule
        if (is_t and t.lean_theorem not in allowed_transpose) or (not is_t and t.lean_theorem!=atheorem):
            raise ValueError("unchecked theorem")
        c=_select_exact_typed_certificate(relation,t,t.rule_id,t.lean_theorem,KRankTransposeRelationCertificate if is_t else KRankAllToAllRelationCertificate,lambda c:((c.input_fact,),(c.output_fact,)))
        try: pre,post=records[c.input_fact],records[c.output_fact]
        except KeyError as exc: raise ValueError("missing materialized relation") from exc
        shape(pre);shape(post)
        if c.rank_count!=k or c.input_gather_dim!=pre.gather_dim or c.output_gather_dim!=post.gather_dim:
            raise ValueError("certificate rank/axis mismatch")
        pi=tuple(t.pm_node_indices);pn=[ir.pm_nodes[i] for i in pi]
        if len(pi)!=k or tuple(c.pm_step_ids)!=tuple(f'pm:{i}:0' for i in pi) or tuple(n.rank for n in pn)!=tuple(range(k)):
            raise ValueError("ordered rank authority mismatch")
        if is_t:
            if len(t.sm_node_indices)!=1: raise ValueError("transpose SM ownership")
            si=t.sm_node_indices[0];sn=ir.sm_nodes[si]
            axes=tuple(c.parameters)
            suffix={(1,2,3,3):'1_2_dim3',(1,2,2,1):'1_2_dim2_to_dim1',(1,2,1,2):'1_2_dim1_to_dim2',(2,3,2,3):'2_3_dim2_to_dim3',(2,3,3,2):'2_3_dim3_to_dim2',(2,3,1,1):'2_3_dim1'}.get((*axes,pre.gather_dim,post.gather_dim))
            if suffix is None or t.lean_theorem != 'TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_'+suffix+'_rank4':
                raise ValueError("axis-specific theorem mismatch")
            if (len(pre.full_shape)!=4 or c.sm_step_id!=f'sm:{si}:0' or sn.rank!=0
                    or sn.op not in ('FW_transpose','BW_transpose') or sn.ins[0]!=pre.sm_tid or sn.outs!=[post.sm_tid]):
                raise ValueError("transpose SM roles mismatch")
            arity=1 if sn.op=='FW_transpose' else 2
            if any(n.op!=sn.op or len(n.ins)!=arity or len(n.outs)!=1 or tuple(n.params or ())!=axes for n in [sn,*pn]):
                raise ValueError("transpose operation/arity/parameters mismatch")
            if tuple(n.ins[0] for n in pn)!=pre.pm_tids or tuple(n.outs[0] for n in pn)!=post.pm_tids:
                raise ValueError("transpose PM role mismatch")
            if (tuple(c.input_full_shape) != pre.full_shape or tuple(c.input_shard_shape) != pre.shard_shape
                    or tuple(c.output_full_shape) != post.full_shape or tuple(c.output_shard_shape) != post.shard_shape):
                raise ValueError("transpose certificate shape mismatch")
            for a,b in [(pre.full_shape,post.full_shape),(pre.shard_shape,post.shard_shape)]:
                dims=list(a);dims[axes[0]],dims[axes[1]]=dims[axes[1]],dims[axes[0]]
                if tuple(dims)!=tuple(b): raise ValueError("transpose shape permutation mismatch")
            bind(pre,si,pi)
        else:
            if t.sm_node_indices or pre.sm_tid!=post.sm_tid or pre.full_shape!=post.full_shape:
                raise ValueError("AllToAll SM role mismatch")
            if any(n.op!='AllToAllPrim' or tuple(n.ins)!=pre.pm_tids or n.outs!=[post.pm_tids[r]] or tuple(n.params or ())!=(pre.gather_dim,post.gather_dim) for r,n in enumerate(pn)):
                raise ValueError("AllToAll PM roles mismatch")
            bind(pre,se,pi)
        bind(post,se,(pe,)*k)
        rows.append((t,c,pre,post))
    fresh=unique(rows,lambda row:row[3].fact_id)
    if not set(after.fact_ids) <= set(before.fact_ids)|fresh.keys(): raise ValueError("unproved post fact")
    # Validate the entire active frame, including retained relations and the InitGoal anchor.
    written={'sm':{x for n in sm_frame for x in n.outs},'pm':{x for n in pm_frame for x in n.outs}}
    for fid in before.fact_ids:
        f=all_facts[fid]
        if f.kind in ('sharded','joined','reduction','replicated','ordinary','chunked'):
            reads=[('sm',f.sm_tid),*(('pm',x) for x in f.pm_tids)]
            if f.joined_pm_tid is not None: reads.append(('pm',f.joined_pm_tid))
            if f.metadata_tid is not None: reads += [('sm',f.metadata_tid),('pm',f.metadata_tid)]
        elif f.kind=='tensor_shape': reads=[(f.side,f.tid)]
        elif f.kind=='tensor_eq': reads=[(f.left_side,f.left_tid),(f.right_side,f.right_tid)]
        else: raise ValueError("unsupported active fact framing kind")
        if any(side not in written or tid in written[side] for side,tid in reads): raise ValueError("active fact overwritten in its store")
    ordered=[]; live=set(before.fact_ids); pending=list(rows)
    while pending:
        ready=[row for row in pending if row[2].fact_id in live]
        if not ready: raise ValueError("internal dependency cycle or missing actual pre-state fact")
        for row in ready:
            ordered.append(row);live.add(row[3].fact_id);pending.remove(row)
    smn, pmn = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    smf, pmf = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {smf} (z : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",
        f"@[irreducible] private def {pmf} (z : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z",
        "",
    ]
    written_sm = {tid for n in sm_frame for tid in n.outs}
    written_pm = {tid for n in pm_frame for tid in n.outs}

    def helper(name, side, node, index, kind, input_tids):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        initial = "smStore" if side == "sm" else "pmStore"
        final_def = smf if side == "sm" else pmf
        nodes_name = smn if side == "sm" else pmn
        frame = sm_frame if side == "sm" else pm_frame
        start = ss if side == "sm" else ps
        final = f"({final_def} {initial})"
        if kind == "transpose":
            expr = f"transposeAxes {node.params[0]} {node.params[1]} ({{store}} {node.ins[0]})"
            if node.op == "FW_transpose":
                apply = f"exact applyNode_fw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {node.params[0]} {node.params[1]}"
            else:
                apply = f"exact applyNode_bw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]} {node.params[0]} {node.params[1]}"
        else:
            tids = "[" + ", ".join(str(t) for t in pa.pm_tids) + "]"
            mapped = "[" + ", ".join(f"({{store}}) {tid}" for tid in pa.pm_tids) + "]"
            expr = f"allToAllPrimWithDims {graph}.numRanks {node.rank} {mapped} {certa.input_gather_dim} {certa.output_gather_dim}"
            apply = f"simpa only [List.map] using applyNode_allToAllPrimWithDims_out {graph} t {node.rank} {tids} {node.outs[0]} {certa.input_gather_dim} {certa.output_gather_dim}"
        theorem = f"{segment_id}_{name}"
        lines.extend([
            f"private theorem {theorem} ({initial} : Store) : {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {final_def}; rfl",
        ])
        body = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=index - start, output_tid=node.outs[0],
            input_tids=tuple(input_tids), written_tids=written_sm if side == "sm" else written_pm,
            expression=expr,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                apply,
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in body)
        lines.extend(["  exact hout", ""])
        return theorem

    def values(fact, store="pmFinal"):
        return "[" + ", ".join(f"{store} {t}" for t in fact.pm_tids) + "]"

    def symbolic_full(fact):
        dims = [str(x) for x in fact.shard_shape]
        dims[fact.gather_dim] = f"{fact.shard_shape[fact.gather_dim]} * {values(fact)}.length"
        return "[" + ", ".join(dims) + "]"

    writer_proofs={}
    for number,(t,c,pre,post) in enumerate(ordered):
        pa,certa=pre,c
        is_t=t.rule_id==trule
        hs=helper(f'hSm{number}', 'sm', ir.sm_nodes[t.sm_node_indices[0]],t.sm_node_indices[0],'transpose',(pre.sm_tid,)) if is_t else None
        hp=[helper(f'hPm{number}_{r}','pm',ir.pm_nodes[i],i,'transpose' if is_t else 'alltoall',(pre.pm_tids[r],) if is_t else pre.pm_tids) for r,i in enumerate(t.pm_node_indices)]
        writer_proofs[number]=(hs,hp)
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  let smFinal := {smf} smStore", f"  let pmFinal := {pmf} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
    ])
    proved={}
    for number,(t,c,pre,post) in enumerate(ordered):
        hs,hp=writer_proofs[number]
        premise=proved.get(pre.fact_id,'hframe _ (by native_decide)')
        lines.extend([f"  have hin{number} : {pre.fact_id}.Holds smFinal pmFinal := {premise}",f"  change ShardedRel (smFinal {pre.sm_tid}) {values(pre)} {pre.gather_dim} {symbolic_full(pre)} {_shape_text(list(pre.shard_shape))} at hin{number}"])
        if t.rule_id==trule:
            ax0, ax1 = c.parameters
            lines.append(f"  have hws{number} : smFinal {post.sm_tid} = transposeAxes {ax0} {ax1} (smFinal {pre.sm_tid}) := {hs} smStore")
            for r in range(k):lines.append(f"  have hwp{number}_{r} : pmFinal {post.pm_tids[r]} = transposeAxes {ax0} {ax1} (pmFinal {pre.pm_tids[r]}) := {hp[r]} pmStore")
            lines.extend([f"  have ht{number} := {c.lean_theorem} hin{number}",f"  have hOut{number} : {post.fact_id}.Holds smFinal pmFinal := by",f"    change ShardedRel (smFinal {post.sm_tid}) {values(post)} {post.gather_dim} {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",f"    rw [hws{number}, {', '.join(f'hwp{number}_{r}' for r in range(k))}]",f"    simpa using ht{number}"])
        else:
            pa,qa,certa=pre,post,c
            lines.append(f"  have hpa := hin{number}")
            for r in range(k):
                lines.extend([f"  have hwa{r} := {hp[r]} pmStore",f"  change pmFinal {qa.pm_tids[r]} = allToAllPrimWithDims {k} {r} {values(pa)} {certa.input_gather_dim} {certa.output_gather_dim} at hwa{r}"])
            in_shape = _shape_text(list(pa.shard_shape)); out_shape = _shape_text(list(qa.shard_shape)); full_shape = _shape_text(list(pa.full_shape))
            lines.extend([
                f"  have hHead : (({values(pa)}.head?.map (fun t => t.shape)).getD []) = {in_shape} := by",
                f"    exact hpa.shard_shapes _ (by simp)",
                f"  have hpaValue : smFinal {pa.sm_tid} = allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)} := by simpa only [List.length_cons, List.length_nil] using hpa.full_value",
                f"  have hGatherShape : (allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)}).shape = {full_shape} := by",
                f"    rw [← hpaValue]; exact hpa.full_shape",
                f"  have hOdim : {qa.gather_dim} < (allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)}).shape.length := by rw [hGatherShape]; native_decide",
                f"  have hDiv : (allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)}).shape.getD {qa.gather_dim} 0 % {k} = 0 := by rw [hGatherShape]; native_decide",
            ])
            for r in range(k):
                lines.extend([
                    f"  have hAShape{r} : (pmFinal {qa.pm_tids[r]}).shape = {out_shape} := by",
                    f"    rw [hwa{r}, allToAllPrimWithDims_shape {k} {r} {values(pa)} {pa.gather_dim} {qa.gather_dim} {in_shape} hHead (by native_decide)]",
                    "    native_decide",
                ])
            lines.extend([
                f"  have hOrdered : {values(qa)} = List.ofFn (fun r : Fin {k} => allToAllPrimWithDims {k} r.1 {values(pa)} {pa.gather_dim} {qa.gather_dim}) := by",
                f"    rw [{', '.join(f'hwa{r}' for r in range(k))}]",
                "    rfl",
                f"  have hcomm := {atheorem} {pa.gather_dim} {qa.gather_dim} {values(pa)} (by simp) hOdim hDiv",
                f"  have hcommExact : allGatherPrimDimN {qa.gather_dim} {values(qa)}.length 0 {values(qa)} = allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)} := by",
                "    rw [hOrdered]",
                "    simpa only [List.length_cons, List.length_nil, List.length_ofFn] using hcomm",
                f"  have hOut{number} : {qa.fact_id}.Holds smFinal pmFinal := by",
                f"    change ShardedRel (smFinal {qa.sm_tid}) {values(qa)} {qa.gather_dim} {full_shape} {out_shape}",
                "    refine { full_value := ?_, full_shape := hpa.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide }",
                "    · rw [hcommExact]",
                "      exact hpaValue",
                "    · intro shard hmem",
                "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
                f"      rcases hmem with {' | '.join(f'h{r}' for r in range(k))}",
            ])
            for r in range(k):
                lines.extend(["      · subst shard", f"        exact hAShape{r}"])
        proved[post.fact_id]=f'hOut{number}'
    fresh_ids=list(proved)
    lines.extend(["  intro fact hfact",f"  have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",f"    exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact","  simp only [List.mem_append] at covered","  rcases covered with fresh | old","  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",f"    rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}"])
    lines.extend(f"    · exact {proved[f]}" for f in fresh_ids)
    lines.extend(["  · exact hframe fact old","",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}",f"  sound := by intro smStore pmStore hstate; have h := {segment_id}_sound smStore pmStore hstate; unfold {smf} {pmf} at h; exact h",""])
    return "\n".join(lines)
