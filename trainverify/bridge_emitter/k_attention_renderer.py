"""One ordered-K attention transition, with graph writers and source refinement."""
from . import composer as c
from . import relation_compiler as rc
from .proof_compiler import build_default_registry, compile_proof_plan


def render_closed_k_attention_segment(ir, relation, segment_id):
    rule_id = "fw-attention-zigzag-k-sharded-kv"
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("K attention requires a complete dependent chain")
    segments = [s for s in chain.segments if s.segment_id == segment_id]
    if len(segments) != 1 or len(segments[0].transition_ids) != 1:
        raise ValueError("K attention requires one singleton segment")
    segment = segments[0]
    matches = [t for t in relation.transition_specs if t.transition_id == segment.transition_ids[0]]
    if len(matches) != 1:
        raise ValueError("K attention transition is not unique")
    transition = matches[0]
    rule = rc.CLOSED_RULE_REGISTRY[rule_id]
    cert = c._select_exact_typed_certificate(
        relation, transition, rule_id, rule.lean_theorems[0], rc.KRankAttentionCertificate,
        lambda x: (tuple(sorted(set(x.input_facts))), (x.output_fact,)))
    if len(transition.pre_facts) != 3 or len(transition.post_facts) != 1:
        raise ValueError("K attention requires Q/K/V and one output")
    records = {f.source: f for f in chain.relation_facts}
    try:
        pre = tuple(records[f] for f in cert.input_facts)
        post = records[transition.post_facts[0]]
    except KeyError as exc:
        raise ValueError("K attention fact not materialized") from exc
    states = {s.state_id: s for s in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if (not {f.fact_id for f in pre} <= set(before.fact_ids)
            or post.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= (set(before.fact_ids) | {post.fact_id})):
        raise ValueError("K attention pre/post facts are not live")
    proof = compile_proof_plan(ir, build_default_registry())
    try:
        authentic, _, _ = rc.advance_k_rank_attention_frontiers(
            ir, proof, (cert.output_step_triple,), ("zigzag_k",))
    except rc.RelationCompositionError as exc:
        raise ValueError(str(exc)) from exc
    if authentic != (cert,):
        raise ValueError("K attention certificate does not match graph authority")
    if (transition.sm_node_indices != tuple(range(*segment.sm_range))
            or transition.pm_node_indices != tuple(range(*segment.pm_range))):
        raise ValueError("K attention footprint mismatch")
    by_step = {s.step_id: s for s in proof.steps}
    steps = [by_step[s] for s in cert.output_step_triple]
    ordered = [ir.sm_nodes[s.node_index] if s.side == "sm" else ir.pm_nodes[s.node_index]
               for s in steps]
    sm, buddies = ordered[0], ordered[1:]
    sms, pms = ir.sm_nodes[slice(*segment.sm_range)], ir.pm_nodes[slice(*segment.pm_range)]
    k, tid = cert.num_ranks, cert.node_metadata_tid
    if (len(sms) != 1 or len(pms) != k or sms[0] != sm
            or set(transition.pm_node_indices) != {s.node_index for s in steps[1:]}):
        raise ValueError("K attention missing writer")
    for index, fact in enumerate(pre):
        if ((fact.sm_tid, *fact.pm_tids) != tuple(n.ins[index] for n in ordered)
                or fact.full_shape != cert.input_full_shapes[index]
                or fact.shard_shape != cert.input_shard_shapes[index]
                or fact.kind != ("zigzag_k" if index == 0 else "sharded")
                or (index > 0 and fact.gather_dim != 0)):
            raise ValueError("K attention input fact authority mismatch")
    if (pre[0].metadata_tid != tid or post.metadata_tid != tid or post.kind != "zigzag_k"
            or (post.sm_tid, *post.pm_tids) != tuple(n.outs[0] for n in ordered)
            or post.full_shape != cert.full_shape or post.shard_shape != cert.shard_shape
            or pre[0].metadata_region_id != post.metadata_region_id):
        raise ValueError("K attention output/metadata fact authority mismatch")
    regions = [r for r in relation.zigzag_regions if r.region_id == post.metadata_region_id]
    if (len(regions) != 1
            or not {cert.input_step_triples[0], cert.output_step_triple} <= set(regions[0].frontier_triples)
            or tid not in regions[0].alias_tids
            or (regions[0].metadata_source, regions[0].contract_metadata_tid,
                regions[0].num_ranks, regions[0].total_tokens)
            != (cert.metadata_source, cert.contract_metadata_tid, k, cert.total_tokens)):
        raise ValueError("K attention metadata region authority mismatch")

    def authority(predicate, label):
        found = [a for a in chain.authority_facts if predicate(a)]
        if len(found) != 1 or found[0].fact_id not in before.fact_ids:
            raise ValueError("K attention " + label + " authority not live")
        return found[0]

    packed = authority(lambda a: a.kind == "packed_cu" and
                       (a.side, a.tid, a.total_tokens, a.num_ranks) ==
                       ("pm", cert.contract_metadata_tid, cert.total_tokens, k), "packed")
    alias = authority(lambda a: a.kind == "tensor_eq" and
                      (a.left_side, a.left_tid, a.right_side, a.right_tid) ==
                      ("pm", tid, "pm", cert.contract_metadata_tid), "alias")
    cross = authority(lambda a: a.kind == "tensor_eq" and
                      (a.left_side, a.left_tid, a.right_side, a.right_tid) ==
                      ("sm", tid, "pm", tid), "cross metadata")
    smg, pmg = ir.sm_graph_ref, ir.pm_graph_ref
    if not smg or not pmg:
        raise ValueError("K attention requires concrete graph declarations")
    qh, kvh, qd, vd, _, _ = cert.parameters
    half = cert.shard_shape[0] // 2
    nodes_text = lambda nodes: '[' + ', '.join(c._node_text(n) for n in nodes) + ']'
    tensors = lambda index, store="pmStore": '[' + ', '.join(f'{store} {n.ins[index]}' for n in buddies) + ']'
    outputs = '[' + ', '.join(f'pmFinal {n.outs[0]}' for n in buddies) + ']'
    math_args = (f'(smStore {sm.ins[0]}) (smStore {sm.ins[1]}) (smStore {sm.ins[2]}) '
                 f'(pmStore {tid}) (pmStore {tid}) {tensors(0)} {tensors(1)} {tensors(2)} '
                 f'{k} {half} {qh} {kvh} {qd} {vd}')
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
        *['      · native_decide'] * 4,
    ]
    for index, name in enumerate(('hQ', 'hK', 'hV')):
        f = pre[index]
        relation_type = (f'ZigzagKRel (smStore {sm.ins[index]}) {tensors(index)} (pmStore {tid})'
                         if index == 0 else f'ShardedRel (smStore {sm.ins[index]}) {tensors(index)} 0')
        lines += [f'    have {name} : {f.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)',
                  f'    change {relation_type} {c._shape_text(f.full_shape)} {c._shape_text(f.shard_shape)} at {name}']
    lines += [
        f'    have hPacked := hstate {packed.fact_id} (by native_decide)',
        f'    have hAlias := hstate {alias.fact_id} (by native_decide)',
        f'    have hCross := hstate {cross.fact_id} (by native_decide)',
        f'    change ZigzagCollective.PackedCuSeqlensWF (pmStore {cert.contract_metadata_tid}) {cert.total_tokens} {k} at hPacked',
        f'    change pmStore {tid} = pmStore {cert.contract_metadata_tid} at hAlias',
        f'    change smStore {tid} = pmStore {tid} at hCross',
        f'    have hDecode : decodeCuSeqlens (pmStore {tid}) = [0, {k} * (2 * {half})] := by',
        '      rw [hAlias]', '      exact hPacked.decoded_single',
        f'    have core := ZigzagKRel.attn_zigzag_sharded_kv_single {math_args}',
        '      hQ hK hV rfl rfl rfl hDecode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
    ]

    def writer(name, side, graph, all_nodes, node, actual_buddies):
        store, final = side + 'Store', side + 'Final'
        index = all_nodes.index(node)
        prefix, suffix = nodes_text(all_nodes[:index]), nodes_text(all_nodes[index + 1:])
        reads = list(dict.fromkeys(t for n in actual_buddies for t in n.ins))
        def expr(s):
            if side == 'sm':
                return f'fw_attn_varlen ({s} {node.ins[0]}) ({s} {node.ins[1]}) ({s} {node.ins[2]}) ({s} {tid}) ({s} {tid}) {qh} {kvh} {qd} {vd} true 0'
            return (f'ZigzagCollective.fw_attn_zigzag_collective_sharded_kv '
                    f'{tensors(0, s)} {tensors(1, s)} {tensors(2, s)} '
                    f'({s} {tid}) ({s} {tid}) {qh} {kvh} {qd} {vd} true 0 {k} {node.rank}')
        prefix_store = f'({prefix}.foldl (applyNodeDistributedFaithful {graph}) {store})'
        out = [
            f'    have {name} : {final} {node.outs[0]} = {expr(store)} := by',
            f'      have hw : {final} {node.outs[0]} = {expr(prefix_store)} := by',
            f'        simpa [{final}, {side}Nodes] using',
            f'          (foldl_faithful_middle_writer {graph} {store} {prefix} {suffix} {c._node_text(node)} {node.outs[0]}',
            f'            (fun t => {expr("t")}) (by', '              intro t',
            '              rw [applyNodeDistributedFaithful_zigzag_attn_out]',
            '              dsimp only [applyNodeFaithfulZigzagAttnValue]',
            f'              rw [show zigzagAttnUsesReplicatedKV {graph} {c._node_text(node)} = {"true" if side == "sm" else "false"} by native_decide]',
            f'              rw [show {graph}.replicaBuddies {c._node_text(node)} = {nodes_text(actual_buddies)} by native_decide]',
            f'              rw [show {graph}.numRanks = {1 if side == "sm" else k} by native_decide]',
            '              rfl) (by native_decide) (by native_decide))',
        ]
        for t in reads:
            out += [f'      rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {t} (by native_decide) (by native_decide)] at hw']
        return out + ['      exact hw']

    lines += writer('hSm', 'sm', smg, sms, sm, [sm])
    for rank, node in enumerate(buddies):
        lines += writer(f'hPm{rank}', 'pm', pmg, pms, node, buddies)
        ref_args = (f'(smStore {sm.ins[0]}) (smStore {sm.ins[1]}) (smStore {sm.ins[2]}) '
                    f'(pmStore {tid}) {tensors(0)} {tensors(1)} {tensors(2)} '
                    f'{k} {rank} {half} {qh} {kvh} {qd} {vd}')
        lines += [
            f'    have hRef{rank} := ZigzagKRel.sourceOutput_eq_collective {ref_args}',
            '      hQ hK hV rfl rfl rfl hDecode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
            f'    have hPmSource{rank} := hPm{rank}.trans hRef{rank}.symm',
        ]
    lines += [
        f'    have hMetadataFinal : pmFinal {tid} = pmStore {tid} :=',
        f'      foldl_applyNodeDistributedFaithful_at_not_written {pmg} pmNodes pmStore {tid} (by native_decide) (by native_decide)',
        f'    have hOut : {post.fact_id}.Holds smFinal pmFinal := by',
        f'      change ZigzagKRel (smFinal {sm.outs[0]}) {outputs} (pmFinal {tid}) {c._shape_text(cert.full_shape)} {c._shape_text(cert.shard_shape)}',
        '      rw [hSm, hCross, ' + ', '.join(f'hPmSource{r}, hRef{r}' for r in range(k)) + ', hMetadataFinal]',
        '      exact core',
        '    intro fact hfact',
        f'    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := by',
        f'      exact (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact',
        '    simp only [List.mem_append] at covered', '    rcases covered with fresh | hold',
        '    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh',
        '      rcases fresh with rfl', '      exact hOut', '    · exact hframe fact hold', '',
    ]
    return '\n'.join(lines)
