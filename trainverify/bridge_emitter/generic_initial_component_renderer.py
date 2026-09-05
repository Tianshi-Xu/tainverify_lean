"""Validation and named fold authority for generic initial E/F/G components."""
from __future__ import annotations

from dataclasses import dataclass

try:
    from .relation_compiler import (
        InitChunkBoundaryCertificate,
        JoinedInitMultirefGroupCertificate,
        KRankVocabShardedEmbeddingProducerCertificate,
        RelationFactSpec,
    )
except ImportError:
    from relation_compiler import (
        InitChunkBoundaryCertificate,
        JoinedInitMultirefGroupCertificate,
        KRankVocabShardedEmbeddingProducerCertificate,
        RelationFactSpec,
    )


@dataclass(frozen=True)
class GenericInitialContext:
    chain: object
    segment: object
    before: object
    after: object
    records: dict
    authority: dict
    embedding: tuple
    chunks: tuple
    groups: tuple
    sm_nodes: tuple
    pm_nodes: tuple


def validate_generic_initial_context(ir, relation, segment_id: str) -> GenericInitialContext:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("generic initial component requires a complete chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None:
        raise ValueError(f"unknown generic initial segment: {segment_id}")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    if len(transition_map) != len(relation.transition_specs):
        raise ValueError("generic initial transition identities are duplicated")
    transitions = tuple(transition_map[item] for item in segment.transition_ids)
    e = tuple(item for item in transitions if item.rule_id == "embedding-vocab-sharded-reduction-k-rank")
    fs = tuple(item for item in transitions if item.rule_id == "init-lineage-full-to-two-chunks")
    gs = tuple(item for item in transitions if item.rule_id == "joined-init-multiref-alias-group")
    if len(e) != 1 or not fs or not gs or transitions != (*e, *fs, *gs):
        raise ValueError("generic initial component is not exact E/F+/G+")
    records = {item.source: item for item in chain.relation_facts}
    if len(records) != len(chain.relation_facts):
        raise ValueError("generic initial relation facts are duplicated")
    authority = {item.fact_id: item for item in chain.authority_facts}
    authority[chain.anchor_fact.fact_id] = chain.anchor_fact
    if len(authority) != len(chain.authority_facts) + 1:
        raise ValueError("generic initial authority facts are duplicated")
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    sm_nodes = tuple(ir.sm_nodes[slice(*segment.sm_range)])
    pm_nodes = tuple(ir.pm_nodes[slice(*segment.pm_range)])

    def select(transition, cls, fact_pair):
        found = [
            item for item in relation.certificates
            if type(item) is cls and item.rule_id == transition.rule_id
            and item.lean_theorem == transition.lean_theorem
            and fact_pair(item) == (transition.pre_facts, transition.post_facts)
        ]
        if len(found) != 1:
            raise ValueError(f"{transition.rule_id} lacks one exact typed certificate")
        return found[0]

    et = e[0]
    ec = select(et, KRankVocabShardedEmbeddingProducerCertificate,
                lambda item: ((item.weight_fact,), (item.output_fact,)))
    ep = records[ec.output_fact]
    ew = records[ec.weight_fact]
    if (ew.kind != "sharded" or ew.gather_dim != 0
            or tuple(ew.full_shape) != tuple(ec.full_weight_shape)
            or tuple(ew.shard_shape) != tuple(ec.shard_weight_shape)
            or ep.kind != "reduction"
            or tuple(ep.full_shape) != tuple(ec.ids_shape) + (ec.hidden_size,)):
        raise ValueError("initial vocab embedding fact payload disagrees")
    if len(et.sm_node_indices) != 1 or len(et.pm_node_indices) != ec.rank_count:
        raise ValueError("initial vocab embedding writer footprint disagrees")
    if ec.sm_step_id != f"sm:{et.sm_node_indices[0]}:0" or ec.pm_step_ids != tuple(
        f"pm:{index}:0" for index in et.pm_node_indices
    ):
        raise ValueError("initial vocab embedding certificate writer identity disagrees")
    sm_node = ir.sm_nodes[et.sm_node_indices[0]]
    pm_writers = tuple(ir.pm_nodes[index] for index in et.pm_node_indices)
    if (sm_node.rank != 0 or sm_node.op != "FW_embedding"
            or sm_node.ins != [ec.ids_tid, ew.sm_tid] or sm_node.outs != [ep.sm_tid]
            or sm_node.params):
        raise ValueError("initial vocab embedding SM writer disagrees")
    if tuple(node.rank for node in pm_writers) != tuple(range(ec.rank_count)) or any(
        node.op != "FW_embedding" or node.ins != [ec.ids_tid, ew.pm_tids[rank]]
        or node.outs != [ep.pm_tids[rank]] or node.params != [rank * ec.shard_rows]
        for rank, node in enumerate(pm_writers)
    ):
        raise ValueError("initial vocab embedding PM writers disagree")
    ids_eq = [item for item in chain.authority_facts if item.kind == "tensor_eq"
              and (item.left_side, item.left_tid, item.right_side, item.right_tid)
              == ("sm", ec.ids_tid, "pm", ec.ids_tid)]
    ids_shape = [item for item in chain.authority_facts if item.kind == "tensor_shape"
                 and (item.side, item.tid, tuple(item.shape))
                 == ("pm", ec.ids_tid, tuple(ec.ids_shape))]
    if len(ids_eq) != 1 or len(ids_shape) != 1:
        raise ValueError("initial vocab embedding IDs authority is not unique")

    chunk_rows = []
    for transition in fs:
        def f_facts(item):
            refs = (f"init:{item.sm_tid}", *item.chunk_step_pair)
            posts = {RelationFactSpec(item.relation_kind, refs), RelationFactSpec("label_chunks", refs)}
            return (), tuple(sorted(posts))
        found = [item for item in relation.certificates
                 if type(item) is InitChunkBoundaryCertificate
                 and item.rule_id == transition.rule_id
                 and item.lean_theorem == transition.lean_theorem
                 and f_facts(item) == (transition.pre_facts, transition.post_facts)
                 and item.chunk_step_pair == tuple(f"pm:{index}:0" for index in transition.pm_node_indices)]
        if len(found) != 1 or transition.pre_facts or len(transition.pm_node_indices) != 2:
            raise ValueError("initial chunk transition is not exact")
        cert = found[0]
        posts = tuple(records[spec] for spec in transition.post_facts)
        relation_post = next(item for item in posts if item.kind == cert.relation_kind)
        label_post = next(item for item in posts if item.kind == "label_chunks")
        indices = transition.pm_node_indices
        nodes = tuple(ir.pm_nodes[index] for index in indices)
        lineage_tids = tuple(tid for _rank, tid in cert.lineage_pm_rank_tids)
        if (transition.sm_node_indices or len(lineage_tids) != 1
                or tuple(node.rank for node in nodes) != (0, 1)
                or any(node.op != "ChunkPrim" or node.params != [0]
                       or node.ins != [lineage_tids[0]] for node in nodes)
                or tuple(node.outs[0] for node in nodes) != relation_post.pm_tids
                or tuple(relation_post.full_shape) != tuple(cert.full_shape)
                or tuple(relation_post.shard_shape) != tuple(cert.shard_shape)):
            raise ValueError("initial chunk topology/fact payload disagrees")
        eq = [item for item in chain.authority_facts if item.kind == "tensor_eq"
              and (item.left_side, item.left_tid, item.right_side, item.right_tid)
              == ("sm", cert.sm_tid, "pm", lineage_tids[0])]
        shape = [item for item in chain.authority_facts if item.kind == "tensor_shape"
                 and (item.side, item.tid, tuple(item.shape))
                 == ("pm", lineage_tids[0], tuple(cert.full_shape))]
        if len(eq) != 1 or len(shape) != 1:
            raise ValueError("initial chunk authority is not unique")
        chunk_rows.append((transition, cert, relation_post, label_post, eq[0], shape[0]))

    group_rows = []
    for transition in gs:
        cert = select(transition, JoinedInitMultirefGroupCertificate,
                      lambda item: ((item.input_fact,), item.output_facts))
        if transition.sm_node_indices or len(transition.pm_node_indices) != 1:
            raise ValueError("grouped initial multiref must own one PM writer")
        index = transition.pm_node_indices[0]
        node = ir.pm_nodes[index]
        pre = records[cert.input_fact]
        posts = tuple(records[x] for x in cert.output_facts)
        if (node.op != "FW_multiref" or len(node.ins) != 1
                or node.ins[0] != pre.joined_pm_tid
                or tuple(node.params or ()) != (cert.arity,)
                or len(node.outs) != cert.arity
                or cert.pm_step_ids != tuple(f"pm:{index}:{p}" for p in cert.projections)):
            raise ValueError("grouped initial multiref writer/projection identity disagrees")
        if any(node.outs[p] != post.joined_pm_tid for p, post in zip(cert.projections, posts)):
            raise ValueError("grouped initial multiref output TIDs disagree")
        group_rows.append((transition, cert, pre, posts))

    produced = {ep.fact_id}
    for _t, _c, relation_post, label_post, _eq, _shape in chunk_rows:
        produced.update((relation_post.fact_id, label_post.fact_id))
    for _t, _c, _pre, posts in group_rows:
        produced.update(item.fact_id for item in posts)
    required = {
        ew.fact_id, ids_eq[0].fact_id, ids_shape[0].fact_id,
        *(pre.fact_id for _t, _c, pre, _posts in group_rows),
        *(eq.fact_id for _t, _c, _r, _l, eq, _s in chunk_rows),
        *(shape.fact_id for _t, _c, _r, _l, _e, shape in chunk_rows),
    }
    if not required <= set(before.fact_ids):
        raise ValueError("generic initial prerequisites are not live")
    segment_ids = set(segment.transition_ids)
    externally_consumed = {fact for transition in relation.transition_specs
                           if transition.transition_id not in segment_ids for fact in transition.pre_facts}
    must_publish = {records[fact].fact_id for fact in externally_consumed
                    if fact in records and records[fact].fact_id in produced}
    must_publish.add(ep.fact_id)
    if not must_publish <= set(after.fact_ids):
        raise ValueError("generic initial live outputs are not published")
    if not set(after.fact_ids) <= set(before.fact_ids) | produced:
        raise ValueError("generic initial post-state contains an unproved fact")
    return GenericInitialContext(chain, segment, before, after, records, authority,
                                 (et, ec, ep), tuple(chunk_rows), tuple(group_rows),
                                 sm_nodes, pm_nodes)


def render_generic_initial_named_authority(ir, context: GenericInitialContext) -> str:
    """Emit shared named folds and one terminal-writer theorem per G projection."""
    try:
        from .composer import _node_text, _shape_text
    except ImportError:
        from composer import _node_text, _shape_text
    sid = context.segment.segment_id
    smn, pmn, smf, pmf = (f"{sid}_smNodes", f"{sid}_pmNodes", f"{sid}_smFinal", f"{sid}_pmFinal")
    sm_text = "[" + ", ".join(_node_text(node) for node in context.sm_nodes) + "]"
    pm_text = "[" + ", ".join(_node_text(node) for node in context.pm_nodes) + "]"
    lines = [
        f"private def {smn} : List NodeDecl := {sm_text}",
        f"private def {pmn} : List NodeDecl := {pm_text}",
        f"@[irreducible] private def {smf} (s : Store) : Store :=",
        f"  {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) : Store :=",
        f"  {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
        "",
    ]
    for group_no, (transition, cert, pre, posts) in enumerate(context.groups):
        index = transition.pm_node_indices[0]
        position = index - context.segment.pm_range[0]
        node = context.pm_nodes[position]
        if any(pre.joined_pm_tid in item.outs for item in context.pm_nodes[:position]):
            raise ValueError("grouped multiref prefix overwrites its input")
        input_helper = f"{sid}_G{group_no}_input"
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {input_helper} (pmStore : Store) :",
            f"    ({pmf} pmStore) {pre.joined_pm_tid} = pmStore {pre.joined_pm_tid} := by",
            f"  unfold {pmf}",
            f"  exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
            f"    {pmn} pmStore {pre.joined_pm_tid} (by native_decide) (by native_decide)",
            "",
        ])
        for row_no, (projection, post) in enumerate(zip(cert.projections, posts)):
            if any(post.joined_pm_tid in item.outs for item in context.pm_nodes[position + 1:]):
                raise ValueError("grouped multiref selected writer is not terminal")
            if (post.kind != "joined" or post.sm_tid != pre.sm_tid
                    or tuple(post.full_shape) != tuple(pre.full_shape)):
                raise ValueError("grouped multiref semantic payload disagrees")
            helper = f"{sid}_G{group_no}_{row_no}_writer"
            semantic = f"{sid}_G{group_no}_{row_no}_semantic"
            shape = _shape_text(list(pre.full_shape))
            lines.extend([
                "set_option maxHeartbeats 500000 in",
                f"private theorem {helper} (pmStore : Store) :",
                f"    ({pmf} pmStore) {post.joined_pm_tid} = pmStore {pre.joined_pm_tid} := by",
                f"  unfold {pmf}",
                f"  rw [show {pmn} = ({pmn}.take {position}) ++ [{_node_text(node)}] ++ ({pmn}.drop {position + 1}) by native_decide]",
                f"  exact foldl_faithful_multiref_middle_writer {ir.pm_graph_ref} pmStore",
                f"    ({pmn}.take {position}) ({pmn}.drop {position + 1})",
                f"    {node.rank} {pre.joined_pm_tid} {_shape_text(list(node.outs))} {cert.arity} {post.joined_pm_tid}",
                "    rfl (by native_decide) (by native_decide) (by native_decide)",
                "    (by native_decide) (by native_decide)",
                "",
            ])
            lines.extend([
                "set_option maxHeartbeats 500000 in",
                f"private theorem {semantic} (smStore pmStore : Store)",
                f"    (hPre : {pre.fact_id}.Holds ({smf} smStore) ({pmf} pmStore)) :",
                f"    {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
                f"  unfold {pre.fact_id} RelationFact.Holds StoreSide.read at hPre",
                f"  unfold {post.fact_id} RelationFact.Holds StoreSide.read",
                f"  change ({smf} smStore) {pre.sm_tid} = ({pmf} pmStore) {pre.joined_pm_tid} ∧",
                f"    (({smf} smStore) {pre.sm_tid}).shape = {shape} ∧",
                f"    (({pmf} pmStore) {pre.joined_pm_tid}).shape = {shape} at hPre",
                f"  change ({smf} smStore) {post.sm_tid} = ({pmf} pmStore) {post.joined_pm_tid} ∧",
                f"    (({smf} smStore) {post.sm_tid}).shape = {shape} ∧",
                f"    (({pmf} pmStore) {post.joined_pm_tid}).shape = {shape}",
                f"  have hInput := {input_helper} pmStore",
                f"  have hWriter := {helper} pmStore",
                "  refine ⟨hPre.1.trans (hInput.trans hWriter.symm), hPre.2.1, ?_⟩",
                "  rw [hWriter, ← hInput]",
                "  exact hPre.2.2",
                "",
            ])
    return "\n".join(lines)


def render_generic_initial_e_helpers(
    ir, context: GenericInitialContext
) -> tuple[str, str]:
    """Emit exact E writer/preservation helpers and its semantic theorem."""
    try:
        from .composer import _node_text, _shape_text
    except ImportError:
        from composer import _node_text, _shape_text

    transition, cert, post = context.embedding
    weight = context.records[cert.weight_fact]

    if (
        ir.sm_num_ranks != 1
        or ir.pm_num_ranks != cert.rank_count
        or cert.rank_count < 1
        or len(weight.pm_tids) != cert.rank_count
        or len(post.pm_tids) != cert.rank_count
        or cert.shard_rows <= 0
        or cert.hidden_size <= 0
        or cert.lean_theorem
        != "TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards"
    ):
        raise ValueError("generic initial E certificate/domain disagrees")

    sid = context.segment.segment_id
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"

    sm_position = (
        transition.sm_node_indices[0] - context.segment.sm_range[0]
    )
    pm_positions = tuple(
        index - context.segment.pm_range[0]
        for index in transition.pm_node_indices
    )
    if (
        not 0 <= sm_position < len(context.sm_nodes)
        or len(pm_positions) != cert.rank_count
        or any(
            not 0 <= position < len(context.pm_nodes)
            for position in pm_positions
        )
    ):
        raise ValueError("generic initial E writers lie outside the frame")

    sm_node = context.sm_nodes[sm_position]
    pm_nodes = tuple(
        context.pm_nodes[position] for position in pm_positions
    )

    # IDs and weight shards are external authority. They must survive the
    # complete named folds, rather than merely the prefixes seen by writers.
    if (
        any(
            cert.ids_tid in node.outs or weight.sm_tid in node.outs
            for node in context.sm_nodes
        )
        or any(
            cert.ids_tid in node.outs
            or any(tid in node.outs for tid in weight.pm_tids)
            for node in context.pm_nodes
        )
    ):
        raise ValueError("generic initial E IDs/weight authority is overwritten")

    # The selected embedding outputs must be the terminal writers of those
    # exact TIDs in the complete component frame.
    if any(
        post.sm_tid in node.outs
        for node in context.sm_nodes[sm_position + 1 :]
    ):
        raise ValueError("generic initial E SM output has a later writer")
    for position, tid in zip(pm_positions, post.pm_tids):
        if any(
            tid in node.outs
            for node in context.pm_nodes[position + 1 :]
        ):
            raise ValueError(
                "generic initial E PM output has a later writer"
            )

    ids_eq = [
        item
        for item in context.authority.values()
        if item.kind == "tensor_eq"
        and (
            item.left_side,
            item.left_tid,
            item.right_side,
            item.right_tid,
        )
        == ("sm", cert.ids_tid, "pm", cert.ids_tid)
    ]
    ids_shape = [
        item
        for item in context.authority.values()
        if item.kind == "tensor_shape"
        and item.side == "pm"
        and item.tid == cert.ids_tid
        and tuple(item.shape) == tuple(cert.ids_shape)
    ]
    if len(ids_eq) != 1 or len(ids_shape) != 1:
        raise ValueError("generic initial E IDs authority is not unique")

    def preservation(name, graph, final, nodes_name, tid):
        return "\n".join(
            [
                "set_option maxHeartbeats 500000 in",
                f"private theorem {name} (s : Store) :",
                f"    ({final} s) {tid} = s {tid} := by",
                f"  unfold {final}",
                "  exact "
                "foldl_applyNodeDistributedFaithful_at_not_written",
                f"    {graph} {nodes_name} s {tid}",
                "    (by native_decide) (by native_decide)",
            ]
        )

    def embedding_apply(graph, node, offset):
        if offset is None:
            apply = (
                f"applyNode_fw_embedding_out {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.outs[0]}"
            )
        else:
            apply = (
                f"applyNode_fw_embedding_offset_out {graph} t "
                f"{node.rank} {offset} {node.ins[0]} {node.ins[1]} "
                f"{node.outs[0]}"
            )
        return [
            "      · intro t",
            "        rw "
            "[applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
            "(hshuffle := by native_decide) "
            "(hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "        unfold applyNodeDistributed",
            "        rw [if_neg (by native_decide), "
            "applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"        · exact {apply}",
            "        · native_decide",
            "        · native_decide",
        ]

    def writer(
        name,
        graph,
        store_name,
        final,
        nodes_name,
        nodes,
        position,
        node,
        offset,
        ids_preserved,
        weight_preserved,
    ):
        prefix = f"({nodes_name}.take {position})"
        suffix = f"({nodes_name}.drop {position + 1})"
        if offset is None:
            function = "fw_embedding"
            expression = (
                f"fw_embedding (({final} {store_name}) {node.ins[0]}) "
                f"(({final} {store_name}) {node.ins[1]})"
            )
        else:
            function = f"(fw_embedding_offset {offset})"
            expression = (
                f"fw_embedding_offset {offset} "
                f"(({final} {store_name}) {node.ins[0]}) "
                f"(({final} {store_name}) {node.ins[1]})"
            )

        lines = [
            "set_option maxHeartbeats 500000 in",
            f"private theorem {name} ({store_name} : Store) :",
            f"    ({final} {store_name}) {node.outs[0]} = "
            f"{expression} := by",
            "  calc",
            f"    ({final} {store_name}) {node.outs[0]} =",
            (
                f"        {function} ({store_name} {node.ins[0]}) "
                f"({store_name} {node.ins[1]}) := by"
            ),
            f"      unfold {final}",
            f"      rw [show {nodes_name} = {prefix} ++ "
            f"[{_node_text(node)}] ++ {suffix} by native_decide]",
            "      apply foldl_faithful_binary_middle_writer",
            f"        {graph} {store_name} {prefix} {suffix}",
            f"        {_node_text(node)} {node.ins[0]} {node.ins[1]} "
            f"{node.outs[0]} {function}",
        ]
        lines.extend(embedding_apply(graph, node, offset))
        lines.extend(
            [
                "      · native_decide",
                "      · native_decide",
                "      · native_decide",
                "      · native_decide",
                "      · native_decide",
                f"    _ = {expression} := by",
                f"      rw [{ids_preserved} {store_name}, "
                f"{weight_preserved} {store_name}]",
            ]
        )
        return "\n".join(lines)

    sm_ids = f"{sid}_E_ids_sm_preserved"
    sm_weight = f"{sid}_E_weight_sm_preserved"
    pm_ids = f"{sid}_E_ids_pm_preserved"
    pm_weights = tuple(
        f"{sid}_E_weight_pm_{rank}_preserved"
        for rank in range(cert.rank_count)
    )
    sm_writer = f"{sid}_E_sm_writer"
    pm_writers = tuple(
        f"{sid}_E_pm_writer_{rank}"
        for rank in range(cert.rank_count)
    )

    writers = [
        preservation(
            sm_ids, ir.sm_graph_ref, smf, smn, cert.ids_tid
        ),
        preservation(
            sm_weight, ir.sm_graph_ref, smf, smn, weight.sm_tid
        ),
        preservation(
            pm_ids, ir.pm_graph_ref, pmf, pmn, cert.ids_tid
        ),
    ]
    writers.extend(
        preservation(
            name, ir.pm_graph_ref, pmf, pmn, tid
        )
        for name, tid in zip(pm_weights, weight.pm_tids)
    )
    writers.append(
        writer(
            sm_writer,
            ir.sm_graph_ref,
            "smStore",
            smf,
            smn,
            context.sm_nodes,
            sm_position,
            sm_node,
            None,
            sm_ids,
            sm_weight,
        )
    )
    writers.extend(
        writer(
            name,
            ir.pm_graph_ref,
            "pmStore",
            pmf,
            pmn,
            context.pm_nodes,
            position,
            node,
            node.params[0],
            pm_ids,
            weight_helper,
        )
        for name, weight_helper, position, node in zip(
            pm_writers, pm_weights, pm_positions, pm_nodes
        )
    )

    weight_tids = (
        "[" + ", ".join(str(tid) for tid in weight.pm_tids) + "]"
    )
    output_tids = (
        "[" + ", ".join(str(tid) for tid in post.pm_tids) + "]"
    )
    weight_values = f"({weight_tids}.map ({pmf} pmStore))"
    output_values = f"({output_tids}.map ({pmf} pmStore))"
    ids_shape_text = _shape_text(list(cert.ids_shape))
    full_weight_shape = _shape_text(list(cert.full_weight_shape))
    shard_weight_shape = _shape_text(list(cert.shard_weight_shape))
    output_shape = _shape_text(list(post.full_shape))
    semantic = f"{sid}_E_semantic"

    semantic_lines = [
        "set_option maxHeartbeats 500000 in",
        f"private theorem {semantic} (smStore pmStore : Store)",
        f"    (hWeight : {weight.fact_id}.Holds "
        f"({smf} smStore) ({pmf} pmStore))",
        f"    (hIdsEq : {ids_eq[0].fact_id}.Holds "
        f"({smf} smStore) ({pmf} pmStore))",
        f"    (hIdsShape : {ids_shape[0].fact_id}.Holds "
        f"({smf} smStore) ({pmf} pmStore)) :",
        f"    {post.fact_id}.Holds "
        f"({smf} smStore) ({pmf} pmStore) := by",
        f"  unfold {ids_eq[0].fact_id} RelationFact.Holds "
        "StoreSide.read at hIdsEq",
        f"  change ({smf} smStore) {cert.ids_tid} = "
        f"({pmf} pmStore) {cert.ids_tid} at hIdsEq",
        f"  unfold {ids_shape[0].fact_id} RelationFact.Holds "
        "StoreSide.read at hIdsShape",
        f"  change ShardedRel (({smf} smStore) {weight.sm_tid})",
        f"    {weight_values} 0 {full_weight_shape} "
        f"{shard_weight_shape} at hWeight",
        f"  have hFullWriter : ({smf} smStore) {post.sm_tid} =",
        f"      fw_embedding (({pmf} pmStore) {cert.ids_tid})",
        f"        (({smf} smStore) {weight.sm_tid}) := by",
        f"    rw [{sm_writer} smStore, hIdsEq]",
    ]
    for rank, helper in enumerate(pm_writers):
        semantic_lines.append(
            f"  have hPmWriter{rank} := {helper} pmStore"
        )
    semantic_lines.extend(
        [
            f"  have hOrdered : {output_values} =",
            "      List.ofFn (fun r : Fin "
            f"{weight_values}.length =>",
            f"        fw_embedding_offset "
            f"(r.val * {cert.shard_rows})",
            f"          (({pmf} pmStore) {cert.ids_tid})",
            f"          ({weight_values}.getD r.val",
            f"            (zeroTensor "
            f"[{cert.shard_rows}, {cert.hidden_size}]))) := by",
            "    simp only [List.map, List.length_cons, "
            "List.length_nil, List.ofFn_succ, List.ofFn_zero, "
            "List.getD]",
            "    rw ["
            + ", ".join(
                f"hPmWriter{rank}"
                for rank in range(cert.rank_count)
            )
            + "]",
            "    simp",
            f"  unfold {post.fact_id} RelationFact.Holds",
            f"  change ReductionRel "
            f"(({smf} smStore) {post.sm_tid})",
            f"    {output_values} {output_shape}",
            "  exact ShardedRel.fw_embedding_vocab_to_reduction",
            f"    (Ws := {weight_values})",
            f"    (contributions := {output_values})",
            f"    (ids := ({pmf} pmStore) {cert.ids_tid})",
            f"    (fullOut := ({smf} smStore) {post.sm_tid})",
            f"    hWeight (by native_decide) (by native_decide)",
            f"    hIdsShape hFullWriter hOrdered",
        ]
    )

    return "\n\n".join(writers), "\n".join(semantic_lines)

def render_generic_initial_publication(
    ir, context: GenericInitialContext
) -> str:
    """Emit the final E/F/G publication, sound theorem, and certificate."""
    sid = context.segment.segment_id
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"

    _transition, embedding_cert, embedding_post = context.embedding
    embedding_weight = context.records[embedding_cert.weight_fact]

    ids_eq = [
        fact
        for fact in context.authority.values()
        if fact.kind == "tensor_eq"
        and (
            fact.left_side,
            fact.left_tid,
            fact.right_side,
            fact.right_tid,
        )
        == ("sm", embedding_cert.ids_tid, "pm", embedding_cert.ids_tid)
    ]
    ids_shape = [
        fact
        for fact in context.authority.values()
        if fact.kind == "tensor_shape"
        and fact.side == "pm"
        and fact.tid == embedding_cert.ids_tid
        and tuple(fact.shape) == tuple(embedding_cert.ids_shape)
    ]
    if len(ids_eq) != 1 or len(ids_shape) != 1:
        raise ValueError(
            "generic initial publication lacks unique E IDs authority"
        )

    before_ids = set(context.before.fact_ids)
    fresh_ids = tuple(
        fact_id
        for fact_id in context.after.fact_ids
        if fact_id not in before_ids
    )

    # Bind proof names by exact fact identity. Helper order and fact-number
    # allocation are deliberately irrelevant. Label-chunk facts are published
    # only when a later certificate consumes them.
    proof_pairs = [(embedding_post.fact_id, "hE")]
    proof_pairs.extend(
        (ordinary.fact_id, f"hF{number}")
        for number, (
            _transition,
            _cert,
            ordinary,
            _label,
            _eq,
            _shape,
        ) in enumerate(context.chunks)
    )
    proof_pairs.extend(
        (label.fact_id, f"hFLabel{number}")
        for number, (
            _transition,
            _cert,
            _ordinary,
            label,
            _eq,
            _shape,
        ) in enumerate(context.chunks)
        if label.fact_id in fresh_ids
    )
    proof_pairs.extend(
        (post.fact_id, f"hG{group_no}_{row_no}")
        for group_no, (
            _transition,
            _cert,
            _pre,
            posts,
        ) in enumerate(context.groups)
        for row_no, post in enumerate(posts)
    )

    proof_pairs = [pair for pair in proof_pairs if pair[0] in fresh_ids]
    proof_by_fact = dict(proof_pairs)
    if len(proof_by_fact) != len(proof_pairs):
        raise ValueError(
            "generic initial publication has duplicate E/F/G fact identity"
        )

    missing = tuple(
        fact_id
        for fact_id in fresh_ids
        if fact_id not in proof_by_fact
    )
    extra = tuple(
        fact_id
        for fact_id in proof_by_fact
        if fact_id not in set(fresh_ids)
    )
    if missing or extra:
        raise ValueError(
            "generic initial publication/proof map mismatch: "
            f"missing={missing!r}, extra={extra!r}"
        )

    # Current Goal 2 instance: 1 E + 30 F + 120 G = 151.
    expected_count = (
        1
        + len(context.chunks)
        + sum(len(posts) for _t, _c, _pre, posts in context.groups)
    )
    if len(fresh_ids) != expected_count:
        raise ValueError(
            "generic initial publication cardinality disagrees: "
            f"expected {expected_count}, got {len(fresh_ids)}"
        )

    proof_names = tuple(proof_by_fact[fact_id] for fact_id in fresh_ids)
    fresh_list = "[" + ", ".join(fresh_ids) + "]"

    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store)",
        f"    (hstate : {context.before.state_id}.Holds "
        "smStore pmStore) :",
        f"    {context.after.state_id}.Holds "
        f"({smf} smStore) ({pmf} pmStore) := by",

        # Frame all retained initial facts onto the two named final stores.
        f"  have hframe : {context.before.state_id}.Holds",
        f"      ({smf} smStore) ({pmf} pmStore) := by",
        f"    unfold {smf} {pmf}",
        "    apply RelationState.Holds.fold_frame",
        f"      {smn} {pmn} smStore pmStore hstate",
        "    · native_decide",
        "    · native_decide",
        "    · native_decide",
        "    · native_decide",

        # E: vocabulary-sharded embedding reduction.
        f"  have hEWeight := hframe {embedding_weight.fact_id} "
        "(by native_decide)",
        f"  have hEIdsEq := hframe {ids_eq[0].fact_id} "
        "(by native_decide)",
        f"  have hEIdsShape := hframe {ids_shape[0].fact_id} "
        "(by native_decide)",
        f"  have hE := {sid}_E_semantic smStore pmStore",
        "    hEWeight hEIdsEq hEIdsShape",
    ]

    # F ordinary relations consume their equality/shape authority at the
    # original stores; their helper transports the result to named finals.
    for number, (
        _transition,
        _cert,
        _ordinary,
        label,
        eq,
        shape,
    ) in enumerate(context.chunks):
        lines.extend([
            f"  have hF{number} := {sid}_F{number}_ordinary",
            "    smStore pmStore",
            f"    (hstate {eq.fact_id} (by native_decide))",
            f"    (hstate {shape.fact_id} (by native_decide))",
        ])
        if label.fact_id in fresh_ids:
            lines.extend([
                f"  have hFLabel{number} := {sid}_F{number}_labels",
                "    smStore pmStore",
                f"    (hstate {shape.fact_id} (by native_decide))",
                f"    hF{number}",
            ])

    # G multiref projections consume their joined pre-facts at named finals.
    for group_no, (
        _transition,
        _cert,
        pre,
        posts,
    ) in enumerate(context.groups):
        for row_no, _post in enumerate(posts):
            lines.extend([
                f"  have hG{group_no}_{row_no} :=",
                f"    {sid}_G{group_no}_{row_no}_semantic",
                "      smStore pmStore",
                f"      (hframe {pre.fact_id} (by native_decide))",
            ])

    # Publish in exact after.fact_ids order. This makes publication independent
    # of helper generation order and canonical fact-number allocation.
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ {fresh_list} ++ "
        f"{context.before.state_id}.facts := by",
        f"    exact (show {context.after.state_id}.facts ⊆",
        f"      {fresh_list} ++ {context.before.state_id}.facts by",
        "        native_decide) hfact",
        "  simp only [List.mem_append] at covered",
        "  rcases covered with fresh | old",
    ])

    if fresh_ids:
        lines.extend([
            "  · simp only [List.mem_cons, List.not_mem_nil, "
            "or_false] at fresh",
            "    rcases fresh with "
            + " | ".join("rfl" for _ in fresh_ids),
            *(f"    · exact {name}" for name in proof_names),
        ])
    else:
        lines.extend([
            "  · simp only [List.not_mem_nil] at fresh",
        ])

    lines.extend([
        "  · exact hframe fact old",
        "",
        "set_option maxRecDepth 32768 in",
        f"private def {sid} :",
        "    ClosedDepSegmentCertificate",
        f"      {ir.sm_graph_ref} {ir.pm_graph_ref}",
        f"      {context.before.state_id} {context.after.state_id} where",
        f"  smNodes := {smn}",
        f"  pmNodes := {pmn}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{smf}, {pmf}] using",
        f"      {sid}_sound smStore pmStore hstate",
        "",
    ])

    return "\n".join(lines)


def render_generic_initial_f_helpers(ir, context: GenericInitialContext) -> tuple[str, str]:
    """Emit named F writer declarations and separate semantic declarations."""
    try:
        from .composer import _node_text, _shape_text
    except ImportError:
        from composer import _node_text, _shape_text
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2 or not context.chunks:
        raise ValueError("generic initial F requires positive 1x2 chunk authority")
    sid = context.segment.segment_id
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"
    writers, semantics = [], []
    for number, (transition, cert, post, label, eq, shape) in enumerate(context.chunks):
        if (cert.rule_id != "init-lineage-full-to-two-chunks"
                or cert.lean_theorem != "TrainVerify.Denote.allGatherPrimDimN_chunkPrimDimN_id_dim0_2"
                or cert.relation_kind != "ordinary" or post.kind != "ordinary"
                or label.kind != "label_chunks" or len(cert.lineage_pm_rank_tids) != 1
                or len(cert.full_shape) != 1 or len(cert.shard_shape) != 1
                or cert.full_shape != (2 * cert.shard_shape[0],)
                or cert.shard_shape[0] <= 0):
            raise ValueError("generic initial F is not exact 1-D dim-0 authority")
        source_tid = cert.lineage_pm_rank_tids[0][1]
        if cert.lineage_pm_rank_tids[0][0] != 0 or transition.sm_node_indices:
            raise ValueError("generic initial F source/SM ownership disagrees")
        positions = tuple(index - context.segment.pm_range[0]
                          for index in transition.pm_node_indices)
        if len(positions) != 2 or any(not 0 <= p < len(context.pm_nodes) for p in positions):
            raise ValueError("generic initial F writers lie outside the frame")
        nodes = tuple(context.pm_nodes[position] for position in positions)
        if any(node.rank != rank or node.op != "ChunkPrim" or node.ins != [source_tid]
               or node.params != [0] or len(node.outs) != 1
               for rank, node in enumerate(nodes)):
            raise ValueError("generic initial F writer signature disagrees")
        if (tuple(node.outs[0] for node in nodes) != (post.pm_rank0_tid, post.pm_rank1_tid)
                or label.sm_tid != source_tid
                or (label.pm_rank0_tid, label.pm_rank1_tid) != (post.pm_rank0_tid, post.pm_rank1_tid)
                or tuple(post.full_shape) != tuple(cert.full_shape)
                or tuple(post.shard_shape) != tuple(cert.shard_shape)
                or (label.full_shape, label.shard_shape) != (post.full_shape, post.shard_shape)):
            raise ValueError("generic initial F fact payload disagrees")
        if any(cert.sm_tid in node.outs for node in context.sm_nodes) or any(
            source_tid in node.outs for node in context.pm_nodes
        ):
            raise ValueError("generic initial F source is overwritten")
        writer = f"{sid}_F{number}_writers"
        ordinary = f"{sid}_F{number}_ordinary"
        labels = f"{sid}_F{number}_labels"
        full_shape, shard_shape = _shape_text(list(cert.full_shape)), _shape_text(list(cert.shard_shape))
        writer_lines = [
            "set_option maxHeartbeats 500000 in",
            f"private theorem {writer} (smStore pmStore : Store) :",
            f"    ({smf} smStore) {cert.sm_tid} = smStore {cert.sm_tid} ∧",
            f"    ({pmf} pmStore) {source_tid} = pmStore {source_tid} ∧",
            f"    ({pmf} pmStore) {nodes[0].outs[0]} = chunkPrimDimN 0 2 0 (pmStore {source_tid}) ∧",
            f"    ({pmf} pmStore) {nodes[1].outs[0]} = chunkPrimDimN 0 2 1 (pmStore {source_tid}) := by",
            "  refine ⟨?_, ?_, ?_, ?_⟩",
            f"  · unfold {smf}",
            f"    exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} {smn} smStore {cert.sm_tid} (by native_decide) (by native_decide)",
            f"  · unfold {pmf}",
            f"    exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} {pmn} pmStore {source_tid} (by native_decide) (by native_decide)",
        ]
        for rank, (position, node) in enumerate(zip(positions, nodes)):
            writer_lines.extend([
                f"  · unfold {pmf}",
                f"    rw [show {pmn} = ({pmn}.take {position}) ++ [{_node_text(node)}] ++ ({pmn}.drop {position + 1}) by native_decide]",
                f"    exact foldl_faithful_chunk_middle_writer {ir.pm_graph_ref} pmStore",
                f"      ({pmn}.take {position}) ({pmn}.drop {position + 1})",
                f"      {rank} {source_tid} {node.outs[0]} 0 rfl",
                "      (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
            ])
        writers.append("\n".join(writer_lines))
        semantics.append("\n".join([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {ordinary} (smStore pmStore : Store)",
            f"    (hEq : {eq.fact_id}.Holds smStore pmStore)",
            f"    (hShape : {shape.fact_id}.Holds smStore pmStore) :",
            f"    {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"  rcases {writer} smStore pmStore with ⟨hSm, _, h0, h1⟩",
            f"  unfold {eq.fact_id} RelationFact.Holds StoreSide.read at hEq",
            f"  unfold {shape.fact_id} RelationFact.Holds StoreSide.read at hShape",
            f"  unfold {post.fact_id} RelationFact.Holds StoreSide.read",
            f"  change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {post.sm_tid}) (({pmf} pmStore) {post.pm_rank0_tid}) (({pmf} pmStore) {post.pm_rank1_tid}) {full_shape} {shard_shape}",
            "  rw [hSm, h0, h1]",
            f"  exact TrainVerify.Denote.RelationCompiler.Ordinary2Rel.of_eq_chunk2_dim0_1d _ _ {cert.shard_shape[0]} hEq (by simpa using hShape) (by decide)",
            "",
            "set_option maxHeartbeats 500000 in",
            f"private theorem {labels} (smStore pmStore : Store)",
            f"    (hShape : {shape.fact_id}.Holds smStore pmStore)",
            f"    (hOrd : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore)) :",
            f"    {label.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"  rcases {writer} smStore pmStore with ⟨_, hFull, h0, h1⟩",
            f"  unfold {shape.fact_id} RelationFact.Holds StoreSide.read at hShape",
            f"  unfold {label.fact_id} RelationFact.Holds StoreSide.read",
            "  have h0Shape := hOrd.rank0_shape",
            "  have h1Shape := hOrd.rank1_shape",
            "  rw [h0] at h0Shape",
            "  rw [h1] at h1Shape",
            f"  change ({pmf} pmStore) {post.pm_rank0_tid} = chunkPrimDimN 0 2 0 (({pmf} pmStore) {source_tid}) ∧ _",
            "  rw [h0, h1, hFull]",
            "  exact ⟨rfl, rfl, hShape, h0Shape, h1Shape⟩",
        ]))
    return "\n\n".join(writers), "\n\n".join(semantics)


def render_closed_generic_initial_component_segment(ir, relation, segment_id: str) -> str:
    """Render one exact typed E/F+/G+ atomic component."""
    context = validate_generic_initial_context(ir, relation, segment_id)
    e_writers, e_semantics = render_generic_initial_e_helpers(ir, context)
    f_writers, f_semantics = render_generic_initial_f_helpers(ir, context)
    return "\n\n".join((
        render_generic_initial_named_authority(ir, context),
        e_writers,
        f_writers,
        e_semantics,
        f_semantics,
        render_generic_initial_publication(ir, context),
    ))
