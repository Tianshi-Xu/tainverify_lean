"""Singleton ordinary-sharded → zigzag-K entry with actual collective writers."""
from . import composer as c
from . import relation_compiler as rc
from .proof_compiler import compile_proof_plan, build_default_registry


def render_closed_k_shuffle_entry_segment(ir, relation, segment_id):
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("K shuffle requires a complete dependent chain")
    segments = [s for s in chain.segments if s.segment_id == segment_id]
    if len(segments) != 1 or len(segments[0].transition_ids) != 1:
        raise ValueError("K shuffle requires one singleton segment")
    transitions = [t for t in relation.transition_specs if t.transition_id == segments[0].transition_ids[0]]
    if len(transitions) != 1:
        raise ValueError("K shuffle transition is not unique")
    rule = rc.CLOSED_RULE_REGISTRY[transitions[0].rule_id]
    segment, transition, cert, pre, post, before, after = c._k_rank_segment_context(
        ir, relation, segment_id, rule.rule_id, rule.lean_theorems[0],
        rc.KRankShuffleEntryCertificate, lambda x: ((x.input_fact,), (x.output_fact,)))
    proof = compile_proof_plan(ir, build_default_registry())
    try:
        authentic, _, _ = rc.advance_k_rank_shuffle_entry_frontiers(
            ir, proof, (cert.output_step_triple,), ("zigzag_k",))
    except rc.RelationCompositionError as exc:
        raise ValueError(str(exc)) from exc
    if authentic != (cert,):
        raise ValueError("K shuffle certificate does not match graph authority")
    if (transition.sm_node_indices != tuple(range(*segment.sm_range))
            or transition.pm_node_indices != tuple(range(*segment.pm_range))):
        raise ValueError("K shuffle footprint mismatch")
    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    by_step = {s.step_id: s for s in proof.steps}
    ordered_steps = [by_step[s] for s in cert.output_step_triple]
    ordered = [ir.sm_nodes[s.node_index] if s.side == "sm" else ir.pm_nodes[s.node_index] for s in ordered_steps]
    sm, buddies = ordered[0], ordered[1:]
    k, tid = cert.num_ranks, cert.node_metadata_tid
    if (len(sms) != 1 or len(pms) != k or sms[0] != sm
            or set(transition.pm_node_indices) != {s.node_index for s in ordered_steps[1:]}):
        raise ValueError("K shuffle missing writer")
    if (pre.kind != "sharded" or pre.gather_dim != 0 or post.kind != "zigzag_k"
            or (pre.sm_tid, *pre.pm_tids) != tuple(n.ins[0] for n in ordered)
            or (post.sm_tid, *post.pm_tids) != tuple(n.outs[0] for n in ordered)
            or any(f.full_shape != cert.full_shape or f.shard_shape != cert.shard_shape for f in (pre,post))
            or post.metadata_tid != tid):
        raise ValueError("K shuffle fact authority mismatch")
    regions = [r for r in relation.zigzag_regions if r.region_id == post.metadata_region_id]
    if (len(regions) != 1 or cert.output_step_triple not in regions[0].frontier_triples
            or (regions[0].metadata_source, regions[0].contract_metadata_tid, regions[0].num_ranks, regions[0].total_tokens)
            != (cert.metadata_source, cert.contract_metadata_tid, k, cert.total_tokens)
            or tid not in regions[0].alias_tids):
        raise ValueError("K shuffle metadata region authority mismatch")
    packed = [a for a in chain.authority_facts if a.kind == "packed_cu"
              and (a.side,a.tid,a.total_tokens,a.num_ranks) == ("pm",cert.contract_metadata_tid,cert.total_tokens,k)]
    aliases = [a for a in chain.authority_facts if a.kind == "tensor_eq"
               and (a.left_side,a.left_tid,a.right_side,a.right_tid) == ("pm",tid,"pm",cert.contract_metadata_tid)]
    if len(packed) != 1 or len(aliases) != 1 or not {packed[0].fact_id,aliases[0].fact_id} <= set(before.fact_ids):
        raise ValueError("K shuffle packed/alias authority not live")
    fs, ss = c._shape_text(cert.full_shape), c._shape_text(cert.shard_shape)
    smg, pmg = ir.sm_graph_ref, ir.pm_graph_ref
    if not smg or not pmg:
        raise ValueError("K shuffle requires concrete graph declarations")
    nodes_text = lambda nodes: '[' + ', '.join(c._node_text(n) for n in nodes) + ']'
    sources = '[' + ', '.join(f'pmStore {n.ins[0]}' for n in buddies) + ']'
    outputs = '[' + ', '.join(f'pmFinal {n.outs[0]}' for n in buddies) + ']'
    lines = [
        f'private def {segment_id} :',
        f'    ClosedDepSegmentCertificate {smg} {pmg} {before.state_id} {after.state_id} where',
        f'  smNodes := {nodes_text(sms)}', f'  pmNodes := {nodes_text(pms)}',
        '  sound := by', '    intro smStore pmStore hstate',
        f'    let smNodes : List NodeDecl := {nodes_text(sms)}',
        f'    let pmNodes : List NodeDecl := {nodes_text(pms)}',
        f'    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {smg}) smStore',
        f'    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore',
        f'    have hframe : {before.state_id}.Holds smFinal pmFinal := by',
        '      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate',
        *['      · native_decide']*4,
        f'    have hSource : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)',
        f'    change ShardedRel (smStore {sm.ins[0]}) {sources} 0 {fs} {ss} at hSource',
        f'    have hPacked : {packed[0].fact_id}.Holds smStore pmStore := hstate _ (by native_decide)',
        f'    have hAlias : {aliases[0].fact_id}.Holds smStore pmStore := hstate _ (by native_decide)',
        f'    change ZigzagCollective.PackedCuSeqlensWF (pmStore {cert.contract_metadata_tid}) {cert.total_tokens} {k} at hPacked',
        f'    change pmStore {tid} = pmStore {cert.contract_metadata_tid} at hAlias',
        f'    have hPackedActual : ZigzagCollective.PackedCuSeqlensWF (pmStore {tid}) {cert.total_tokens} {k} := by',
        '      rw [hAlias]', '      exact hPacked',
        f'    have hCu : ZigzagCollective.ZigzagCuWF (decodeCuSeqlens (pmStore {tid})) {sources} {k} := by',
        '      apply hPackedActual.toZigzagCuWF rfl',
        '      · intro x hx', '        rw [hSource.shard_shapes x hx]', '        decide',
        '      · intro x hx',
        f'        change x.shape = (pmStore {buddies[0].ins[0]}).shape',
        f'        rw [hSource.shard_shapes x hx, hSource.shard_shapes (pmStore {buddies[0].ins[0]}) (by simp)]',
        f'      · change (pmStore {buddies[0].ins[0]}).shape.getD 0 0 * {k} = {cert.total_tokens}',
        f'        rw [hSource.shard_shapes (pmStore {buddies[0].ins[0]}) (by simp)]',
        '        rfl',
        '    have core := ZigzagKRel.of_sharded hSource hCu',
    ]
    def writer(name, side, graph, all_nodes, node, actual_buddies):
        store, final = side+'Store', side+'Final'
        index = all_nodes.index(node)
        prefix, suffix = nodes_text(all_nodes[:index]), nodes_text(all_nodes[index+1:])
        reads = [n.ins[0] for n in actual_buddies]
        expr = lambda s: f'ZigzagCollective.fw_maybe_shuffle_collective [{", ".join(f"{s} {t}" for t in reads)}] (decodeCuSeqlens ({s} {tid})) {node.params[0]} {node.params[1]}'
        prefix_store = f'({prefix}.foldl (applyNodeDistributedFaithful {graph}) {store})'
        result = [
            f'    have {name} : {final} {node.outs[0]} = {expr(store)} := by',
            f'      have hw : {final} {node.outs[0]} = {expr(prefix_store)} := by',
            f'        simpa [{final}, {side}Nodes] using',
            f'          (foldl_faithful_middle_writer {graph} {store} {prefix} {suffix} {c._node_text(node)} {node.outs[0]}',
            f'            (fun t => {expr("t")}) (by', '              intro t',
        ]
        if cert.op == 'BW_maybe_unshuffle':
            result += [
                '              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]',
                '              rw [applyNodeDistributed_bw_maybe_unshuffle_out]',
                '              unfold applyNodeBWMaybeUnshuffleValue',
                '              rw [ZigzagCollective.bw_maybe_unshuffle_collective_eq_fw_shuffle]',
            ]
        else:
            result += ['              rw [applyNodeDistributedFaithful_shuffle_out]', '              unfold applyNodeFaithfulShuffleValue']
        result += [
            f'              rw [show {graph}.replicaBuddies {c._node_text(node)} = {nodes_text(actual_buddies)} by native_decide]',
            '              rfl) (by native_decide) (by native_decide))',
        ]
        for t in dict.fromkeys([*reads,tid]):
            result += [f'      rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {t} (by native_decide) (by native_decide)] at hw']
        return result + ['      exact hw']
    lines += writer('hSm', 'sm', smg, sms, sm, [sm])
    for rank, node in enumerate(buddies):
        lines += writer(f'hPm{rank}', 'pm', pmg, pms, node, buddies)
    lines += [
        f'    have hSmValue : smFinal {sm.outs[0]} = smStore {sm.ins[0]} := by',
        '      simpa [ZigzagCollective.fw_maybe_shuffle_collective] using hSm',
        f'    have hMetadataFinal : pmFinal {tid} = pmStore {tid} :=',
        f'      foldl_applyNodeDistributedFaithful_at_not_written {pmg} pmNodes pmStore {tid} (by native_decide) (by native_decide)',
        f'    have hOut : {post.fact_id}.Holds smFinal pmFinal := by',
        f'      change ZigzagKRel (smFinal {sm.outs[0]}) {outputs} (pmFinal {tid}) {fs} {ss}',
        '      rw [hSmValue, '+', '.join(f'hPm{r}' for r in range(k))+', hMetadataFinal]',
        '      exact core',
        '    intro fact hfact',
        f'    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := by',
        f'      exact (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact',
        '    simp only [List.mem_append] at covered',
        '    rcases covered with fresh | hold',
        '    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh',
        '      rcases fresh with rfl', '      exact hOut', '    · exact hframe fact hold', '',
    ]
    return '\n'.join(lines)
