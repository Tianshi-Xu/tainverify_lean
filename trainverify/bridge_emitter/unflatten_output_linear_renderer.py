"""Independent unflatten/output-linear tuples, one complete fold per axis.

Inputs must already hold before the atomic frame. Writer order is recovered
independently from each graph; transition enumeration has no execution meaning.
"""
from __future__ import annotations


def render_closed_unflatten_output_linear_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _select_exact_typed_certificate
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate
        from relation_compiler import get_closed_rule_spec
    chain=relation.dependent_chain_plan
    segments=[s for s in chain.segments if s.segment_id==segment_id]
    if not chain.complete or len(segments)!=1:
        raise ValueError('one complete atomic segment required')
    seg=segments[0]
    ts={t.transition_id:t for t in relation.transition_specs}
    if len(ts)!=len(relation.transition_specs) or len(set(seg.transition_ids))!=len(seg.transition_ids):
        raise ValueError('duplicate transition identity')
    transitions=[ts[t] for t in seg.transition_ids]
    view='fw-view-unflatten-sequence-sharded-k-rank';linear='linear-output-sharded-k-rank'
    family={t.rule_id for t in transitions}
    if family!={view,linear}:
        raise ValueError('positive independent unflatten/output-linear tuple required')
    states={s.state_id:s for s in chain.states};before=states[seg.pre_state_id];after=states[seg.post_state_id]
    records={r.source:r for r in chain.relation_facts};byid={r.fact_id:r for r in chain.relation_facts}
    if len(records)!=len(chain.relation_facts) or len(byid)!=len(records):
        raise ValueError('duplicate relation identity')
    fresh=[];used={};selected={};sm_owned=[];pm_owned=[]
    for t in transitions:
        spec=get_closed_rule_spec(t.rule_id)
        project=(lambda c:((c.input_fact,),(c.output_fact,))) if t.rule_id==view else (lambda c:(tuple(sorted((c.activation_fact,c.weight_fact))),(c.output_fact,)))
        c=_select_exact_typed_certificate(relation,t,spec.rule_id,spec.lean_theorems[0],spec.certificate_type,project)
        selected[t.transition_id]=c
        if (c.rank_count!=ir.pm_num_ranks or c.rank_count<1 or ir.sm_num_ranks!=1
                or len(t.sm_node_indices)!=1 or len(t.pm_node_indices)!=c.rank_count
                or c.sm_step_id!=f'sm:{t.sm_node_indices[0]}:0'
                or c.pm_step_ids!=tuple(f'pm:{i}:0' for i in t.pm_node_indices)):
            raise ValueError('rank/writer certificate mismatch')
        if any(records[f].fact_id not in before.fact_ids for f in t.pre_facts):
            raise ValueError('independent inputs must be in the pre-state')
        for f in t.post_facts:
            r=records[f]
            if r.fact_id not in after.fact_ids or r.fact_id in before.fact_ids:
                raise ValueError('fresh output must be published')
            fresh.append(r.fact_id)
        used.update((records[f].fact_id,records[f]) for f in (*t.pre_facts,*t.post_facts))
        sm_owned.extend(t.sm_node_indices);pm_owned.extend(t.pm_node_indices)
    if len(set(fresh))!=len(fresh) or not set(after.fact_ids)<=set(before.fact_ids)|set(fresh):
        raise ValueError('post-state is outside exact old/fresh coverage')
    for owned,bounds,nodes in ((sm_owned,seg.sm_range,ir.sm_nodes),(pm_owned,seg.pm_range,ir.pm_nodes)):
        if not 0<=bounds[0]<=bounds[1]<=len(nodes) or len(set(owned))!=len(owned) or not set(owned)<=set(range(*bounds)):
            raise ValueError('writer/frame ownership mismatch')
    def source(ref,side,tid,limit,rank=None):
        nodes=ir.sm_nodes if side=='sm' else ir.pm_nodes
        parts=ref.split(':')
        if ref==f'init:{tid}':writer=-1
        elif len(parts)==3 and parts[0]==side and all(p.isdigit() for p in parts[1:]):
            writer,projection=map(int,parts[1:])
            if (ref!=f'{side}:{writer}:{projection}' or not 0<=writer<limit
                    or projection>=len(nodes[writer].outs) or nodes[writer].outs[projection]!=tid
                    or (rank is not None and nodes[writer].rank!=rank)):
                raise ValueError('source writer/projection/rank mismatch')
        else:raise ValueError('source axis/canonical reference mismatch')
        if any(tid in node.outs for node in nodes[writer+1:limit]):
            raise ValueError('source is not the latest writer')
    for r in used.values():
        f=r.source
        if (f.layout!=r.kind or f.gather_dim!=r.gather_dim or f.source_step_triples or r.source_tid_triples
                or r.metadata_tid is not None or r.metadata_region_id is not None
                or len(f.step_triple)!=1+len(r.pm_tids)):
            raise ValueError('source layout/axis/arity mismatch')
        initial=r.fact_id in before.fact_ids
        sl=seg.sm_range[0 if initial else 1];pl=seg.pm_range[0 if initial else 1]
        source(f.step_triple[0],'sm',r.sm_tid,sl,0)
        for rank,(ref,tid) in enumerate(zip(f.step_triple[1:],r.pm_tids)):source(ref,'pm',tid,pl,rank)
        if r.kind=='joined':
            if f.joined_pm_step is None or r.joined_pm_tid is None:raise ValueError('missing joined source')
            source(f.joined_pm_step,'pm',r.joined_pm_tid,pl)
        elif f.joined_pm_step is not None or r.joined_pm_tid is not None:raise ValueError('unexpected joined source')
    protected={'sm':set(),'pm':set()}
    authorities={a.fact_id:a for a in (*chain.authority_facts,chain.anchor_fact)}
    if len(authorities)!=len(chain.authority_facts)+1 or set(authorities)&set(byid):raise ValueError('duplicate authority ID')
    for fid in set(before.fact_ids)|{chain.anchor_fact.fact_id}:
        if fid in byid:
            r=byid[fid];protected['sm'].add(r.sm_tid);protected['pm'].update(r.pm_tids)
            if r.joined_pm_tid is not None:protected['pm'].add(r.joined_pm_tid)
            if r.metadata_tid is not None:protected['pm'].add(r.metadata_tid)
            for triple in r.source_tid_triples:
                protected['sm'].add(triple[0]);protected['pm'].update(triple[1:])
        elif fid in authorities:
            a=authorities[fid]
            if a.kind=='tensor_eq':
                protected[a.left_side].add(a.left_tid);protected[a.right_side].add(a.right_tid)
            elif a.kind in ('tensor_shape','packed_cu','label_bound'):protected[a.side].add(a.tid)
            elif a.kind=='gather':
                protected['sm'].add(a.sm_tid);protected['pm'].update((a.pm_rank0_tid,a.pm_rank1_tid))
            else:raise ValueError('unsupported active authority')
        else:raise ValueError('unmaterialized pre-state fact')
    for side,nodes,bounds in (('sm',ir.sm_nodes,seg.sm_range),('pm',ir.pm_nodes,seg.pm_range)):
        if any(protected[side].intersection(node.outs) for node in nodes[slice(*bounds)]):
            raise ValueError('component overwrites protected input/authority/anchor')
    sn,pn=f'{segment_id}_smNodes',f'{segment_id}_pmNodes'
    sf,pf=f'{segment_id}_smFinal',f'{segment_id}_pmFinal'
    lines=[f"private def {sn} : List NodeDecl := [{', '.join(_node_text(n) for n in ir.sm_nodes[slice(*seg.sm_range)])}]",
           f"private def {pn} : List NodeDecl := [{', '.join(_node_text(n) for n in ir.pm_nodes[slice(*seg.pm_range)])}]",
           f'@[irreducible] private def {sf}(z:Store):Store := {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z',
           f'@[irreducible] private def {pf}(z:Store):Store := {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z']
    ordered=sorted(transitions,key=lambda t:t.sm_node_indices)
    for j,t in enumerate(ordered):
        lines.append((_view if t.rule_id==view else _linear)(ir,relation,segment_id,t,f'{segment_id}_t{j}'))
    lines.extend([f'private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where',
        f'  smNodes := {sn}',f'  pmNodes := {pn}','  sound := by','    intro smStore pmStore hstate',
        f'    have hframe : {before.state_id}.Holds ({sf} smStore) ({pf} pmStore) := by',
        f'      unfold {sf} {pf}',f'      apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide'])
    for j,t in enumerate(ordered):
        c=selected[t.transition_id]
        args='hframe' if t.rule_id==view else ' '.join(f'(hframe {records[f].fact_id} (by native_decide))' for f in (c.activation_fact,c.weight_fact))
        lines.append(f'    have h{j} := {segment_id}_t{j}_out smStore pmStore {args}')
    outs=[records[t.post_facts[0]].fact_id for t in ordered]
    fl='['+', '.join(outs)+']'
    lines.extend(['    have result : '+after.state_id+f'.Holds ({sf} smStore) ({pf} pmStore) := by',
        '      intro fact hfact',f'      have covered : fact ∈ {fl} ++ {before.state_id}.facts :=',
        f'        (show {after.state_id}.facts ⊆ {fl} ++ {before.state_id}.facts by native_decide) hfact',
        '      simp only [List.mem_append] at covered','      rcases covered with fresh | old',
        '      · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh',
        '        rcases fresh with '+' | '.join('rfl' for _ in outs)])
    lines.extend(f'        · exact h{j}' for j in range(len(outs)))
    lines.extend(['      · exact hframe fact old',f'    simpa only [{sf}, {pf}] using result',''])
    return '\n'.join(lines)


def _linear(ir, relation, segment_id, transition, local_id):
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("linear-output-sharded-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next(x for x in chain.segments if x.segment_id == segment_id)
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda c: (tuple(sorted((c.activation_fact, c.weight_fact))), (c.output_fact,)),
    )
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    activation, weight, output = (records[cert.activation_fact], records[cert.weight_fact],
                                  records[cert.output_fact])
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    k = cert.rank_count
    if (k <= 0 or cert.output_gather_dim != 2
            or activation.kind != "joined" or activation.joined_pm_tid is None
            or weight.kind != "sharded" or weight.gather_dim != 0
            or output.kind != "sharded" or output.gather_dim != 2
            or len(weight.pm_tids) != k or len(output.pm_tids) != k
            or tuple(cert.activation_shape) != tuple(activation.full_shape)
            or tuple(cert.weight_full_shape) != tuple(weight.full_shape)
            or tuple(cert.weight_shard_shape) != tuple(weight.shard_shape)
            or tuple(cert.output_full_shape) != tuple(output.full_shape)
            or tuple(cert.output_shard_shape) != tuple(output.shard_shape)):
        raise ValueError("sparse output linear relation metadata mismatch")
    sm_start, sm_end = segment.sm_range; pm_start, pm_end = segment.pm_range
    if (len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k
            or not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("sparse output linear writer/frame partition mismatch")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
    if (sm_node.op != spec.op or sm_node.rank != 0 or sm_node.params
            or tuple(node.rank for node in pm_nodes) != tuple(range(k))
            or any(node.op != spec.op or node.params for node in pm_nodes)
            or sm_node.ins != [activation.sm_tid, weight.sm_tid]
            or sm_node.outs != [output.sm_tid]
            or any(node.ins != [activation.joined_pm_tid, weight.pm_tids[r]]
                   or node.outs != [output.pm_tids[r]] for r, node in enumerate(pm_nodes))):
        raise ValueError("sparse output linear writer signatures mismatch")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end]); pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    if any(output.sm_tid in node.outs for i, node in enumerate(ir.sm_nodes)
           if sm_start <= i < sm_end and i not in transition.sm_node_indices):
        raise ValueError("sparse output linear SM frame overwrites output")
    if any(set(output.pm_tids).intersection(node.outs) for i, node in enumerate(ir.pm_nodes)
           if pm_start <= i < pm_end and i not in transition.pm_node_indices):
        raise ValueError("sparse output linear PM frame overwrites output")

    activation_shape = tuple(activation.full_shape)
    weight_full, weight_shard = tuple(weight.full_shape), tuple(weight.shard_shape)
    output_full, output_shard = tuple(output.full_shape), tuple(output.shard_shape)
    if (len(activation_shape) != 3 or len(weight_full) != 2 or len(weight_shard) != 2
            or len(output_full) != 3 or len(output_shard) != 3):
        raise ValueError("sparse output linear shape ranks mismatch")
    b, seq, inner = activation_shape; local_out = weight_shard[0]
    if min(b, seq, inner, local_out) <= 0:
        raise ValueError("positive output-linear dimensions required")
    if (weight_shard != (local_out, inner) or weight_full != (local_out * k, inner)
            or output_shard != (b, seq, local_out)
            or output_full != (b, seq, local_out * k)):
        raise ValueError("sparse output linear shape contract mismatch")

    shape = lambda xs: _shape_text(list(xs))
    sm_nodes_name=f"{segment_id}_smNodes"; pm_nodes_name=f"{segment_id}_pmNodes"
    sm_final_name=f"{segment_id}_smFinal"; pm_final_name=f"{segment_id}_pmFinal"
    lines = []

    def add_writer(name, graph, initial, final_name, nodes_name, frame, pos, node):
        final=f"({final_name} {initial})"; theorem_name=f"{local_id}_{name}"
        expr=f"fw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame, position=pos,
            output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={t for n in frame for t in n.outs}, expression=expr,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_fw_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            ])
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = add_writer("smWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                           sm_nodes_name, sm_frame, transition.sm_node_indices[0]-sm_start, sm_node)
    pm_helpers=[]
    for rank,(index,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)):
        pm_helpers.append(add_writer(f"pmWriter{rank}", ir.pm_graph_ref, "pmStore",
                                     pm_final_name, pm_nodes_name, pm_frame, index-pm_start, node))

    pm_weights="["+", ".join(f"({pm_final_name} pmStore) {tid}" for tid in weight.pm_tids)+"]"
    pm_outputs="["+", ".join(f"({pm_final_name} pmStore) {tid}" for tid in output.pm_tids)+"]"
    lines.extend([
        f"private theorem {local_id}_out (smStore pmStore : Store)",
        f"    (hActivation : {activation.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore))",
        f"    (hWeight : {weight.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore)) :",
        f"    {output.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  change ({sm_final_name} smStore) {activation.sm_tid} = ({pm_final_name} pmStore) {activation.joined_pm_tid} ∧",
        f"    (({sm_final_name} smStore) {activation.sm_tid}).shape = {shape(activation_shape)} ∧",
        f"    (({pm_final_name} pmStore) {activation.joined_pm_tid}).shape = {shape(activation_shape)} at hActivation",
        f"  change ShardedRel (({sm_final_name} smStore) {weight.sm_tid}) {pm_weights} 0 {shape(weight_full)} {shape(weight_shard)} at hWeight",
        f"  have hSm := {sm_helper} smStore",
    ])
    for rank,helper in enumerate(pm_helpers): lines.append(f"  have hPm{rank} := {helper} pmStore")
    lines.extend([
        f"  have hComm := ({theorem}",
        f"    (K := {pm_weights}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {local_out})",
        f"    (x := ({pm_final_name} pmStore) {activation.joined_pm_tid}) (ws := {pm_weights})",
        "    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        "    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))",
        f"  have hValue : ({sm_final_name} smStore) {output.sm_tid} = allGatherPrimDimN 2 {pm_outputs}.length 0 {pm_outputs} := by",
        "    rw [hSm, hActivation.1, hWeight.full_value, hComm]",
        "    simp only [List.map, List.length_cons, List.length_nil]",
        f"    rw [{', '.join('← hPm'+str(r) for r in range(k))}]",
    ])
    for rank,node in enumerate(pm_nodes):
        lines.extend([
            f"  have hOutShape{rank} : (({pm_final_name} pmStore) {node.outs[0]}).shape = {shape(output_shard)} := by",
            f"    rw [hPm{rank}]",
            f"    exact fw_linear_3d_shape {b} {seq} {inner} {local_out} _ _ hActivation.2.2",
            f"      (hWeight.shard_shapes (({pm_final_name} pmStore) {weight.pm_tids[rank]}) (by simp))",
        ])
    lines.extend([
        f"  unfold {output.fact_id} RelationFact.Holds",
        f"  change ShardedRel (({sm_final_name} smStore) {output.sm_tid}) {pm_outputs} 2 {shape(output_full)} {shape(output_shard)}",
        "  refine {", "    full_value := hValue", "    full_shape := ?_",
        "    shards_nonempty := by simp", "    gather_dim_lt := by native_decide",
        "    shard_shapes := ?_", "    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide", "  }",
        "  · rw [hValue]",
        f"    rw [allGatherPrimDimN_shape 2 {pm_outputs}.length {pm_outputs} {shape(output_shard)}]",
        "    · simp only [List.length_cons, List.length_nil]", "      native_decide",
        "    · simp only [List.head?, Option.map, Option.getD]", "      exact hOutShape0",
        "  · intro shard hmem", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with "+" | ".join("rfl" for _ in range(k)),
    ])
    for rank in range(k): lines.append(f"    · exact hOutShape{rank}")
    lines.append("")

    return "\n".join(lines)


def _view(ir, relation, segment_id, tr, local_id):
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from relation_compiler import get_closed_rule_spec
    chain=relation.dependent_chain_plan
    seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    axes={"bw-view-flatten-sequence-sharded-k-rank":1,"bw-view-flatten-head-sharded-k-rank":2,
          "fw-view-flatten-sequence-sharded-k-rank":1,"fw-view-flatten-head-sharded-k-rank":2,
          "fw-view-unflatten-sequence-sharded-k-rank":1,"fw-view-unflatten-head-sharded-k-rank":2,
          "bw-view-unflatten-sequence-sharded-k-rank":1,"bw-view-unflatten-head-sharded-k-rank":2}
    if tr.rule_id not in axes:
        raise ValueError("BW_view flatten rule is unsupported")
    dim=axes[tr.rule_id]
    inverse=tr.rule_id in {"fw-view-unflatten-sequence-sharded-k-rank","fw-view-unflatten-head-sharded-k-rank",
                           "bw-view-unflatten-sequence-sharded-k-rank","bw-view-unflatten-head-sharded-k-rank"}
    spec=get_closed_rule_spec(tr.rule_id)
    arity=2 if spec.op=="BW_view" else 1
    c=_select_exact_typed_certificate(relation,tr,spec.rule_id,spec.lean_theorems[0],spec.certificate_type,
        lambda c:((c.input_fact,),(c.output_fact,)))
    records={r.source:r for r in chain.relation_facts}
    x,y=records[c.input_fact],records[c.output_fact]
    if any(r.source.layout!="sharded" or r.source.gather_dim!=dim for r in (x,y)):
        raise ValueError("view source/record axis mismatch")
    k=c.rank_count
    shape4=y.shard_shape if inverse else x.shard_shape
    if k<1 or len(shape4)!=4:
        raise ValueError("BW_view flatten rank/shape domain mismatch")
    b,s,n,d=shape4
    full_in=(b,s*k,n,d) if dim==1 else (b,s,n*k,d)
    full_out=(b,s*k,n*d) if dim==1 else (b,s,n*k*d)
    shard_in=(b,s,n,d);shard_out=(b,s,n*d)
    if inverse:
        full_in,full_out=full_out,full_in
        shard_in,shard_out=shard_out,shard_in
    if (any(v<=0 for v in (b,s,n,d)) or x.kind!="sharded" or y.kind!="sharded"
            or x.gather_dim!=dim or y.gather_dim!=dim
            or x.full_shape!=full_in or y.full_shape!=full_out or x.shard_shape!=shard_in or y.shard_shape!=shard_out
            or len(x.pm_tids)!=k or len(y.pm_tids)!=k):
        raise ValueError("BW_view flatten exact shape/axis authority mismatch")
    states={st.state_id:st for st in chain.states}
    before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if (x.fact_id not in before.fact_ids or y.fact_id not in after.fact_ids
):
        raise ValueError("BW_view flatten pre/post liveness mismatch")
    if len(tr.sm_node_indices)!=1 or len(tr.pm_node_indices)!=k:
        raise ValueError("BW_view flatten exact 1+K footprint required")
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if (not set(tr.sm_node_indices)<=set(range(ss,se)) or not set(tr.pm_node_indices)<=set(range(ps,pe))
            or c.sm_step_id!=f"sm:{tr.sm_node_indices[0]}:0"
            or c.pm_step_ids!=tuple(f"pm:{i}:0" for i in tr.pm_node_indices)):
        raise ValueError("BW_view flatten writer footprint mismatch")
    sm=ir.sm_nodes[tr.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in tr.pm_node_indices)
    for node,rank,inp,out,shape in ((sm,0,x.sm_tid,y.sm_tid,y.full_shape),*(
            (node,r,x.pm_tids[r],y.pm_tids[r],y.shard_shape) for r,node in enumerate(pms))):
        if (node.rank!=rank or node.op!=spec.op or len(node.ins)!=arity or node.ins[0]!=inp
                or node.outs!=[out] or tuple(node.params)!=shape):
            raise ValueError("BW_view flatten writer roles/order/parameters mismatch")
    sf=ir.sm_nodes[ss:se];pf=ir.pm_nodes[ps:pe]
    sn,pn=f"{segment_id}_smNodes",f"{segment_id}_pmNodes"
    smf,pmf=f"{segment_id}_smFinal",f"{segment_id}_pmFinal"
    lines=[]
    def writer(name,graph,initial,final_name,nodes_name,frame,index,node):
        theorem=f"{local_id}_{name}";final=f"({final_name} {initial})"
        target=_shape_text(list(node.params));expr=f"fw_view {target} ({{store}} {node.ins[0]})"
        lines.extend([f"private theorem {theorem}({initial}:Store):{final} {node.outs[0]}={expr.format(store=final)}:=by",
            f"  have hfinal:{final}={nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {final_name};rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=index,output_tid=node.outs[0],
            input_tids=(node.ins[0],),written_tids={tid for item in frame for tid in item.outs},expression=expr,
            apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]",
                "simp [applyNodeDistributed,applyNodeRingAttn]",
                f"exact {'applyNode_bw_view_out' if arity==2 else 'applyNode_fw_view_out'} {graph} t {node.rank} {node.params[0]} {_shape_text(list(node.params[1:]))} {' '.join(str(tid) for tid in node.ins)} {node.outs[0]}"])
        lines.extend(line[2:] if line.startswith("  ") else line for line in helper)
        lines.append("  exact hout")
        return theorem
    hs=writer("hSmWriter",ir.sm_graph_ref,"smStore",smf,sn,sf,tr.sm_node_indices[0]-ss,sm)
    hp=[writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pmf,pn,pf,index-ps,node) for r,(index,node) in enumerate(zip(tr.pm_node_indices,pms))]
    xl="["+", ".join(f"pmFinal {tid}" for tid in x.pm_tids)+"]"
    yl="["+", ".join(f"pmFinal {tid}" for tid in y.pm_tids)+"]"
    xf,xs,yf,ys=(_shape_text(list(sh)) for sh in (x.full_shape,x.shard_shape,y.full_shape,y.shard_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",
        f"private theorem {local_id}_out(smStore pmStore:Store)(hframe:{before.state_id}.Holds ({smf} smStore) ({pmf} pmStore)):",
        f"    {y.fact_id}.Holds ({smf} smStore) ({pmf} pmStore):=by",
        f"    let smFinal:={smf} smStore",f"    let pmFinal:={pmf} pmStore",
        f"    have hx:{x.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {x.sm_tid}) {xl} {dim} {xf} {xs} at hx",
        f"    have hxV:smFinal {x.sm_tid}=allGatherPrimDimN {dim} {k} 0 {xl}:=by simpa only [List.length_cons,List.length_nil] using hx.full_value",
        f"    have hSm:smFinal {y.sm_tid}=fw_view {yf} (smFinal {x.sm_tid}):={hs} smStore"])
    for r in range(k):
        lines.append(f"    have hPm{r}:pmFinal {y.pm_tids[r]}=fw_view {ys} (pmFinal {x.pm_tids[r]}):={hp[r]} pmStore")
    lines.extend([f"    have hcomm:={c.lean_theorem} {k} {b} {s} {n} {d} {xl}",
        "      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes",
        f"    have hvalue:smFinal {y.sm_tid}=allGatherPrimDimN {dim} {k} 0 {yl}:=by",
        "      rw [hSm,hxV,hcomm]","      simp only [List.map]",
        "      rw ["+", ".join(f"← hPm{r}" for r in range(k))+"]",
        f"    have hout:{y.fact_id}.Holds smFinal pmFinal:=by",
        f"      change ShardedRel (smFinal {y.sm_tid}) {yl} {dim} {yf} {ys}",
        "      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}",
        "      · rw [hSm]; rfl",
        "      · intro piece hmem",
        "        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem",
        "        rcases hmem with "+" | ".join(f"h{r}" for r in range(k))])
    for r in range(k):
        lines.extend([f"        · subst piece; rw [hPm{r}]; rfl"])
    lines.extend(["      · simp only [List.length_cons,List.length_nil]; native_decide",
        "    exact hout"])
    return "\n".join(lines)
