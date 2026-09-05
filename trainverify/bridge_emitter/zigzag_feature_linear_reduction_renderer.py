"""One-fold CP2 zigzag-feature row-parallel reduction renderer (draft)."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(certificate):
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        sort_keys=True, separators=(",", ":"),
    ).encode()).hexdigest()
def render_closed_zigzag_feature_linear_reduction_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate
        from .relation_compiler import ZigzagFeatureLinearReductionCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate
        from relation_compiler import ZigzagFeatureLinearReductionCertificate

    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("zigzag-feature reduction requires a complete chain")
    segment = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("zigzag-feature reduction requires one transition")
    transition = {t.transition_id: t for t in relation.transition_specs}[segment.transition_ids[0]]
    rule = "zigzag-feature-linear-dim1-allreduce-chunks-cp2"
    theorem = "TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.mix_precision_linear_dim1_allReduce_chunks_cp2"
    if transition.rule_id != rule or transition.lean_theorem != theorem:
        raise ValueError("zigzag-feature reduction theorem identity disagrees")
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem, ZigzagFeatureLinearReductionCertificate,
        lambda c: ((c.input_fact, c.weight_fact), (c.output_fact,)),
    )
    if _digest(cert) != transition.certificate_digest:
        raise ValueError("zigzag-feature reduction certificate digest mismatch")
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("zigzag-feature reduction fact/state identity is ambiguous")
    pre, weight, post = records[cert.input_fact], records[cert.weight_fact], records[cert.output_fact]
    before, after = states[segment.pre_state_id], states[segment.post_state_id]

    if (ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2 or pre.kind != "zigzag_feature"
            or weight.kind != "sharded" or post.kind != "zigzag"
            or pre.gather_dim != 1 or weight.gather_dim != 1
            or len(pre.pm_tids) != 2 or len(weight.pm_tids) != 2 or len(post.pm_tids) != 2
            or pre.metadata_tid is None or pre.metadata_tid != post.metadata_tid
            or pre.metadata_region_id != post.metadata_region_id
            or cert.rows <= 0 or cert.feature_features <= 0 or cert.output_features <= 0
            or cert.input_features != 2 * cert.feature_features
            or pre.full_shape != (2 * cert.rows, cert.input_features)
            or pre.row_shard_shape != (cert.rows, cert.input_features)
            or pre.shard_shape != (2 * cert.rows, cert.feature_features)
            or weight.full_shape != (cert.output_features, cert.input_features)
            or weight.shard_shape != (cert.output_features, cert.feature_features)
            or post.full_shape != (2 * cert.rows, cert.output_features)
            or post.shard_shape != (cert.rows, cert.output_features)
            or weight.sm_tid != cert.full_weight_tid
            or weight.pm_tids != cert.weight_shard_tids):
        raise ValueError("zigzag-feature reduction typed relation contract disagrees")

    sm_indices = tuple(range(*segment.sm_range)); pm_indices = tuple(range(*segment.pm_range))
    if transition.sm_node_indices != sm_indices or transition.pm_node_indices != pm_indices:
        raise ValueError("zigzag-feature reduction footprint does not exactly partition the component")
    if len(sm_indices) != 2 or len(pm_indices) != 7:
        raise ValueError("zigzag-feature reduction requires an exact 2x7 frame")
    sm_linear, sm_view = (ir.sm_nodes[i] for i in sm_indices)
    pm0, pm1, reduce, view0, view1, chunk0, chunk1 = (ir.pm_nodes[i] for i in pm_indices)
    full_shape = tuple(post.full_shape)
    if ((sm_linear.op, sm_view.op) != ("FW_mix_precision_linear", "FW_view")
            or tuple(n.op for n in (pm0, pm1, reduce, view0, view1, chunk0, chunk1))
               != ("FW_mix_precision_linear", "FW_mix_precision_linear", "AllReducePrim",
                   "FW_view", "FW_view", "ChunkPrim", "ChunkPrim")
            or tuple(n.rank for n in (sm_linear, sm_view, pm0, pm1, reduce, view0, view1, chunk0, chunk1))
               != (0, 0, 0, 1, 0, 0, 1, 0, 1)
            or any(n.params not in (None, []) for n in (sm_linear, pm0, pm1, reduce))
            or (sm_linear.ins, sm_linear.outs) != ([pre.sm_tid, weight.sm_tid], [reduce.outs[0]])
            or (pm0.ins, pm1.ins) != ([pre.pm_tids[0], weight.pm_tids[0]], [pre.pm_tids[1], weight.pm_tids[1]])
            or reduce.ins != [pm0.outs[0], pm1.outs[0]] or len(reduce.outs) != 1
            or any(n.ins != reduce.outs or n.outs != [post.sm_tid] or tuple(n.params or ()) != full_shape
                   for n in (view0, view1))
            or sm_view.ins != sm_linear.outs or sm_view.outs != [post.sm_tid]
            or tuple(sm_view.params or ()) != full_shape
            or any(n.ins != [post.sm_tid] or n.params != [0] for n in (chunk0, chunk1))
            or (chunk0.outs[0], chunk1.outs[0]) != post.pm_tids
            or cert.pm_output_identity_writer_indices != (pm_indices[3], pm_indices[4])):
        raise ValueError("zigzag-feature reduction literal writer topology disagrees")

    required = {pre.fact_id, weight.fact_id}
    if (not required <= set(before.fact_ids) or post.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= set(before.fact_ids) | {post.fact_id}):
        raise ValueError("zigzag-feature reduction liveness disagrees")

    sid = segment_id
    sm_nodes = f"[{', '.join(_node_text(n) for n in (sm_linear, sm_view))}]"
    pm_nodes = f"[{', '.join(_node_text(n) for n in (pm0, pm1, reduce, view0, view1, chunk0, chunk1))}]"
    fs, row, feat = (_shape_text(list(x)) for x in (post.full_shape, post.shard_shape, pre.shard_shape))
    wfs, wss = _shape_text(list(weight.full_shape)), _shape_text(list(weight.shard_shape))
    def linear_writer(name, graph, store, final, nodes, frame, pos, node):
        prefix = f"({nodes}.take {pos})"; suffix = f"({nodes}.drop {pos + 1})"
        lemma = "applyNode_fw_mix_precision_linear_out_1p"
        return "\n".join([
            f"    have {name} : {final} {node.outs[0]} = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            "      calc",
            f"        {final} {node.outs[0]} = fw_linear ({prefix}.foldl (applyNodeDistributedFaithful {graph}) {store} {node.ins[0]}) ({prefix}.foldl (applyNodeDistributedFaithful {graph}) {store} {node.ins[1]}) := by",
            f"          change ({nodes}.foldl (applyNodeDistributedFaithful {graph}) {store}) {node.outs[0]} = _",
            f"          rw [show {nodes} = {prefix} ++ [{_node_text(node)}] ++ {suffix} by native_decide]",
            f"          apply foldl_faithful_middle_writer {graph} {store} {prefix} {suffix} {_node_text(node)} {node.outs[0]} (fun t => fw_linear (t {node.ins[0]}) (t {node.ins[1]}))",
            "          · intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "            unfold applyNodeDistributed",
            "            rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"            · exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "            · native_decide", "            · native_decide",
            "          · native_decide", "          · native_decide",
            f"        _ = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {node.ins[0]} (by native_decide) (by native_decide)]",
            f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {node.ins[1]} (by native_decide) (by native_decide)]",
        ])
    h_sm_linear = linear_writer("hSmLinear", ir.sm_graph_ref, "smStore", "smFinal", "smNodes", (sm_linear, sm_view), 0, sm_linear)
    h_pm_linear0 = linear_writer("hPmLinear0", ir.pm_graph_ref, "pmStore", "pmFinal", "pmNodes", (pm0, pm1, reduce, view0, view1, chunk0, chunk1), 0, pm0)
    h_pm_linear1 = linear_writer("hPmLinear1", ir.pm_graph_ref, "pmStore", "pmFinal", "pmNodes", (pm0, pm1, reduce, view0, view1, chunk0, chunk1), 1, pm1)
    def chunk_writer(name, pos, node, rank):
        prefix = f"(pmNodes.take {pos})"; suffix = f"(pmNodes.drop {pos + 1})"
        return "\n".join([
            f"    have {name} : pmFinal {node.outs[0]} = chunkPrimDimN 0 2 {rank} (pmFinal {node.ins[0]}) := by",
            f"      have hWriter : pmFinal {node.outs[0]} = chunkPrimDimN 0 2 {rank} ({prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore {node.ins[0]}) := by",
            f"        change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {node.outs[0]} = _",
            f"        rw [show pmNodes = {prefix} ++ [{_node_text(node)}] ++ {suffix} by native_decide]",
            f"        apply foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix} {_node_text(node)} {node.outs[0]} (fun t => chunkPrimDimN 0 2 {rank} (t {node.ins[0]}))",
            "        · intro t",
            "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "          unfold applyNodeDistributed",
            "          rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"          · simpa only [show {ir.pm_graph_ref}.numRanks = 2 by native_decide] using (applyNode_chunkPrimDimN_out {ir.pm_graph_ref} t {rank} {node.ins[0]} {node.outs[0]} 0)",
            "          · native_decide", "          · native_decide", "        · native_decide", "        · native_decide",
            f"      have hRead := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore {prefix} ({_node_text(node)} :: {suffix}) {node.ins[0]} (by native_decide) (by native_decide)",
            f"      change ({prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {node.ins[0]} = pmFinal {node.ins[0]} at hRead",
            "      rw [hWriter, hRead]",
        ])
    h_chunk0 = chunk_writer("hChunk0", 5, chunk0, 0)
    h_chunk1 = chunk_writer("hChunk1", 6, chunk1, 1)
    return f'''private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := {sm_nodes}
  pmNodes := {pm_nodes}
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := {sm_nodes}
    let pmNodes : List NodeDecl := {pm_nodes}
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide
    have hInput : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hWeight : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagFeatureRel (smStore {pre.sm_tid}) [pmStore {pre.pm_tids[0]}, pmStore {pre.pm_tids[1]}]
      (pmStore {pre.metadata_tid}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.row_shard_shape))} {feat} at hInput
    change ShardedRel (smStore {weight.sm_tid}) [pmStore {weight.pm_tids[0]}, pmStore {weight.pm_tids[1]}]
      1 {wfs} {wss} at hWeight
    have hCore := {theorem} {cert.rows} {cert.input_features} {cert.feature_features} {cert.output_features}
      hInput (by simpa only using hWeight) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    obtain ⟨z0, z1, hRow, hFeature⟩ := hInput
{h_sm_linear}
{h_pm_linear0}
{h_pm_linear1}
    have hReduce : pmFinal {reduce.outs[0]} = allReducePrim 2 0
        [fw_linear (pmStore {pre.pm_tids[0]}) (pmStore {weight.pm_tids[0]}),
         fw_linear (pmStore {pre.pm_tids[1]}) (pmStore {weight.pm_tids[1]})] := by
      have hWriter : pmFinal {reduce.outs[0]} = allReducePrim 2 0
          [((pmNodes.take 2).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {pm0.outs[0]},
           ((pmNodes.take 2).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {pm1.outs[0]}] := by
        change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {reduce.outs[0]} = _
        rw [show pmNodes = (pmNodes.take 2) ++ [{_node_text(reduce)}] ++ (pmNodes.drop 3) by native_decide]
        apply foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore (pmNodes.take 2) (pmNodes.drop 3)
          {_node_text(reduce)} {reduce.outs[0]}
          (fun t => allReducePrim 2 0 [t {pm0.outs[0]}, t {pm1.outs[0]}])
        · intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          unfold applyNodeDistributed
          rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
          · exact applyNode_allReducePrim_out {ir.pm_graph_ref} t 0 [{pm0.outs[0]}, {pm1.outs[0]}] {reduce.outs[0]}
          · native_decide
          · native_decide
        · native_decide
        · native_decide
      have hRead0 := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore
        (pmNodes.take 2) ({_node_text(reduce)} :: (pmNodes.drop 3)) {pm0.outs[0]} (by native_decide) (by native_decide)
      have hRead1 := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore
        (pmNodes.take 2) ({_node_text(reduce)} :: (pmNodes.drop 3)) {pm1.outs[0]} (by native_decide) (by native_decide)
      change ((pmNodes.take 2).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {pm0.outs[0]} = pmFinal {pm0.outs[0]} at hRead0
      change ((pmNodes.take 2).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {pm1.outs[0]} = pmFinal {pm1.outs[0]} at hRead1
      rw [hWriter, hRead0, hRead1, hPmLinear0, hPmLinear1]
    have hSmLinearShape : (fw_linear (smStore {pre.sm_tid}) (smStore {weight.sm_tid})).shape = {fs} :=
      TrainVerify.Denote.GeneratedPatterns.fw_linear_shape_2d' _ _ _ _ _ hRow.full_shape hWeight.full_shape
    have hPmLinear0Shape : (fw_linear (pmStore {pre.pm_tids[0]}) (pmStore {weight.pm_tids[0]})).shape = {fs} :=
      TrainVerify.Denote.GeneratedPatterns.fw_linear_shape_2d' _ _ _ _ _
        (hFeature.shard_shapes _ (by simp)) (hWeight.shard_shapes _ (by simp))
    have hReduceShape : (allReducePrim 2 0
        [fw_linear (pmStore {pre.pm_tids[0]}) (pmStore {weight.pm_tids[0]}),
         fw_linear (pmStore {pre.pm_tids[1]}) (pmStore {weight.pm_tids[1]})]).shape = {fs} := by
      rw [allReducePrim_shape 2 0 _ _ rfl]
      exact hPmLinear0Shape
    have hSmOut : smFinal {post.sm_tid} = fw_linear (smStore {pre.sm_tid}) (smStore {weight.sm_tid}) := by
      have hWriter : smFinal {post.sm_tid} = fw_view {fs}
          (((smNodes.take 1).foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) {sm_linear.outs[0]}) := by
        change (smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) {post.sm_tid} = _
        rw [show smNodes = (smNodes.take 1) ++ [{_node_text(sm_view)}] ++ (smNodes.drop 2) by native_decide]
        apply foldl_faithful_middle_writer {ir.sm_graph_ref} smStore (smNodes.take 1) (smNodes.drop 2)
          {_node_text(sm_view)} {post.sm_tid} (fun t => fw_view {fs} (t {sm_linear.outs[0]}))
        · intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          unfold applyNodeDistributed
          rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
          · exact applyNode_fw_view_out {ir.sm_graph_ref} t 0 {sm_view.params[0]} {_shape_text(sm_view.params[1:])} {sm_view.ins[0]} {sm_view.outs[0]}
          · native_decide
          · native_decide
        · native_decide
        · native_decide
      have hRead := foldl_faithful_prefix_read_eq_final {ir.sm_graph_ref} smStore
        (smNodes.take 1) ({_node_text(sm_view)} :: (smNodes.drop 2)) {sm_linear.outs[0]} (by native_decide) (by native_decide)
      change ((smNodes.take 1).foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) {sm_linear.outs[0]} = smFinal {sm_linear.outs[0]} at hRead
      rw [hWriter, hRead, hSmLinear, fw_view_id_of_shape _ _ hSmLinearShape]
    have hPmView : pmFinal {post.sm_tid} = allReducePrim 2 0
        [fw_linear (pmStore {pre.pm_tids[0]}) (pmStore {weight.pm_tids[0]}),
         fw_linear (pmStore {pre.pm_tids[1]}) (pmStore {weight.pm_tids[1]})] := by
      have hWriter : pmFinal {post.sm_tid} = fw_view {fs}
          (((pmNodes.take 4).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {reduce.outs[0]}) := by
        change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {post.sm_tid} = _
        rw [show pmNodes = (pmNodes.take 4) ++ [{_node_text(view1)}] ++ (pmNodes.drop 5) by native_decide]
        apply foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore (pmNodes.take 4) (pmNodes.drop 5)
          {_node_text(view1)} {post.sm_tid} (fun t => fw_view {fs} (t {reduce.outs[0]}))
        · intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          unfold applyNodeDistributed
          rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
          · exact applyNode_fw_view_out {ir.pm_graph_ref} t 1 {view1.params[0]} {_shape_text(view1.params[1:])} {view1.ins[0]} {view1.outs[0]}
          · native_decide
          · native_decide
        · native_decide
        · native_decide
      have hRead := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore
        (pmNodes.take 4) ({_node_text(view1)} :: (pmNodes.drop 5)) {reduce.outs[0]} (by native_decide) (by native_decide)
      change ((pmNodes.take 4).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {reduce.outs[0]} = pmFinal {reduce.outs[0]} at hRead
      rw [hWriter, hRead, hReduce, fw_view_id_of_shape _ _ hReduceShape]
{h_chunk0}
{h_chunk1}
    have hMeta : pmFinal {post.metadata_tid} = pmStore {pre.metadata_tid} := by
      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)
    have hOut : {post.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Zigzag2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_tids[0]})
        (pmFinal {post.pm_tids[1]}) (pmFinal {post.metadata_tid}) {fs} {row}
      rw [hSmOut, hChunk0, hChunk1, hPmView, hMeta]
      exact hCore
    intro fact hfact
    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with rfl | old
    · exact hOut
    · exact hframe fact old
'''
