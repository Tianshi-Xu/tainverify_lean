import denote.SourceScopedEval
import denote.BWEmbeddingSequenceShardK

namespace TrainVerify.Denote.SourceDPGradientRelations

set_option maxHeartbeats 500000
noncomputable section
open scoped BigOperators

/-!
A batch-to-sequence adapter for embedding **weight** gradients. No dX claim.

Source domain: runtime_source_authority.py:959-983 admits SUM/zero0/nreplicas1;
nnscaler/runtime/adapter/reducer.py:237-250 performs SUM and writes the buffer.
`cross_dp_wred` is `tensorSum` (Denote.lean:2185). There is no division by the
DP group size here. Any loss normalization must already occur in the supplied
cotangents. Non-unit replica scaling and reducer hooks are not justified here.

The input relation below is deliberately about IDs and incoming cotangents,
not a relation asserting the desired equality of summed weight gradients.
It preserves rank-list order, including noncontiguous/nonzero world ranks.
-/

private theorem view_valAt (sh : Shape) (x : Tensor)
    (hp : prodShape sh = prodShape x.shape) (i : Nat) :
    valAt (fw_view sh x) i = valAt x i := by
  by_cases hi : i < prodShape sh
  · rw [valAt_of_lt _ _ hi]
    rfl
  · have hx : ¬ i < prodShape x.shape := by rwa [← hp]
    simp only [valAt, fw_view, Tensor.mkShape, hi, hx, ↓reduceDIte]

/-- Reshaping IDs and incoming cotangents without changing their flat lengths
preserves the embedding weight gradient. This is not a dX theorem. -/
theorem bw_embedding_view (g ids w : Tensor) (gsh ish : Shape)
    (hg : prodShape gsh = prodShape g.shape)
    (hi : prodShape ish = prodShape ids.shape) :
    bw_embedding (fw_view gsh g) (fw_view ish ids) w = bw_embedding g ids w := by
  apply Tensor.ext
  · rw [bw_embedding_shape, bw_embedding_shape]
  · intro idx hidx
    have hwidx : idx < prodShape w.shape := by
      rwa [bw_embedding_shape] at hidx
    rw [bw_embedding_valAt _ _ _ _ hwidx, bw_embedding_valAt _ _ _ _ hwidx]
    change (∑ k ∈ Finset.range (prodShape ish),
      if scalarToNat (valAt (fw_view ish ids) k) = idx / lastD w.shape then
        valAt (fw_view gsh g) (k * lastD w.shape + idx % lastD w.shape) else 0) = _
    rw [hi]
    apply Finset.sum_congr rfl
    intro k _
    rw [view_valAt ish ids hi, view_valAt gsh g hg]

private theorem map_ordered_positions {α β : Type} (xs : List α) (d : α) (f : α → β) :
    xs.map f = (List.range xs.length).map (fun j => f (xs.getD j d)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro j hj _
    have hj' : j < xs.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rfl

/-- Explicit contiguous DP-batch decomposition, expressed by size-preserving
flat views so the existing arbitrary-K sequence proof can be reused.

Each rank owns `B` whole examples of length `S`. The full batch has `B*K`
examples. Flattening gives rank-major token blocks of length `B*S`; it does
not interleave the batch axis as a raw dimension-1 gather would for `B > 1`.
`flatGs` is only a witness for ordered incoming cotangents. Its production by
the model's backward prefix is a separate caller obligation. -/
structure EmbeddingBatchDecomposition (rs : List Nat) (B S H V : Nat)
    (fullG fullIds w : Tensor) (localG localIds : Nat → Tensor) (flatGs : List Tensor) : Prop where
  batch_pos : 0 < B
  sequence_pos : 0 < S
  hidden_pos : 0 < H
  vocab_pos : 0 < V
  weight_shape : w.shape = [V, H]
  full_grad_shape : fullG.shape = [B * rs.length, S, H]
  full_ids_shape : fullIds.shape = [B * rs.length, S]
  local_grad_shape : ∀ r ∈ rs, (localG r).shape = [B, S, H]
  local_ids_shape : ∀ r ∈ rs, (localIds r).shape = [B, S]
  flat_length : flatGs.length = rs.length
  flat_shapes : ∀ g ∈ flatGs, g.shape = [1, B * S, H]
  full_grad_view : fw_view [1, B * S * rs.length, H] fullG =
    allGatherPrimDimN 1 rs.length 0 flatGs
  local_grad_view : ∀ j, j < rs.length →
    fw_view [1, B * S, H] (localG (rs.getD j 0)) =
      flatGs.getD j (zeroTensor [1, B * S, H])
  local_ids_view : ∀ j, j < rs.length →
    fw_view [1, B * S] (localIds (rs.getD j 0)) =
      chunkPrimDimN 1 rs.length j (fw_view [1, B * S * rs.length] fullIds)

/-- The local dW sum is derived from the explicit batch decomposition, using
`bw_embedding_seqchunk_K`; it is not an assumption of this theorem. -/
theorem embedding_batch_sum
    (rs : List Nat) (B S H V : Nat) (fullG fullIds w : Tensor)
    (localG localIds : Nat → Tensor) (flatGs : List Tensor)
    (hne : rs ≠ [])
    (h : EmbeddingBatchDecomposition rs B S H V fullG fullIds w localG localIds flatGs) :
    cross_dp_wred (rs.map (fun r => bw_embedding (localG r) (localIds r) w)) =
      bw_embedding fullG fullIds w := by
  have hK : 0 < rs.length := List.length_pos_iff.mpr hne
  have hBS : 0 < B * S := Nat.mul_pos h.batch_pos h.sequence_pos
  have hfull := bw_embedding_view fullG fullIds w
    [1, B * S * rs.length, H] [1, B * S * rs.length]
    (by rw [h.full_grad_shape]; simp only [prodShape, List.foldl, Nat.one_mul]; ring)
    (by rw [h.full_ids_shape]; simp only [prodShape, List.foldl, Nat.one_mul]; ring)
  rw [h.full_grad_view] at hfull
  have hseq := bw_embedding_seqchunk_K rs.length 1 (B * S) H V flatGs
    (fw_view [1, B * S * rs.length] fullIds) w hK (by decide) hBS
    h.hidden_pos h.vocab_pos h.flat_length h.flat_shapes rfl h.weight_shape
  have hlocal : ∀ j, j < rs.length →
      bw_embedding (flatGs.getD j (zeroTensor [1, B * S, H]))
        (chunkPrimDimN 1 rs.length j (fw_view [1, B * S * rs.length] fullIds)) w =
      bw_embedding (localG (rs.getD j 0)) (localIds (rs.getD j 0)) w := by
    intro j hj
    have hr : rs.getD j 0 ∈ rs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem hj
    rw [← h.local_grad_view j hj, ← h.local_ids_view j hj]
    exact bw_embedding_view _ _ w [1, B * S, H] [1, B * S]
      (by rw [h.local_grad_shape _ hr]; simp only [prodShape, List.foldl, Nat.one_mul])
      (by rw [h.local_ids_shape _ hr]; simp only [prodShape, List.foldl, Nat.one_mul])
  have hlist :
      (List.range rs.length).map (fun j =>
        bw_embedding (flatGs.getD j (zeroTensor [1, B * S, H]))
          (chunkPrimDimN 1 rs.length j (fw_view [1, B * S * rs.length] fullIds)) w) =
      rs.map (fun r => bw_embedding (localG r) (localIds r) w) := by
    rw [map_ordered_positions rs 0 (fun r => bw_embedding (localG r) (localIds r) w)]
    apply List.map_congr_left
    intro j hj
    exact hlocal j (List.mem_range.mp hj)
  rw [hlist] at hseq
  exact hseq.symm.trans hfull

/-- Publish the derived global embedding dW through the existing source-scoped
single-output WRED step, retaining its checked group/shape contract and frame.
`hreads` binds each unreduced input to its local BW producer, not to a sum. -/
theorem embedding_wred_output
    (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid) (state : Store)
    (rank out B S H V : Nat) (fullG fullIds w : Tensor)
    (localG localIds : Nat → Tensor) (flatGs : List Tensor)
    (hw : GroupScopedEval.WellFormed g.numRanks rank rs)
    (hc : SourceScopedEval.WredContract rs peer state
      {rank := rank, op := "OpName.CROSS_DP_WRED", ins := rs.map peer, outs := [out]})
    (h : EmbeddingBatchDecomposition rs B S H V fullG fullIds w localG localIds flatGs)
    (hreads : ∀ r ∈ rs, state (peer r) = bw_embedding (localG r) (localIds r) w) :
    ∃ state', SourceScopedEval.step g (.group (some rs)) peer state
        {rank := rank, op := "OpName.CROSS_DP_WRED", ins := rs.map peer, outs := [out]} = some state' ∧
      state' out = bw_embedding fullG fullIds w ∧
      (∀ tid, tid ∉ ([out] : List Tid) → state' tid = state tid) := by
  obtain ⟨state', hstep, hout, hframe⟩ :=
    SourceScopedEval.wred_output g rs peer state rank (rs.map peer) out hw hc
  refine ⟨state', hstep, ?_, hframe⟩
  have hinputs : (rs.map peer).map state =
      rs.map (fun r => bw_embedding (localG r) (localIds r) w) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    exact hreads r hr
  rw [hout, hinputs]
  exact embedding_batch_sum rs B S H V fullG fullIds w localG localIds flatGs hw.1 h

#print axioms bw_embedding_view
#print axioms embedding_batch_sum
#print axioms embedding_wred_output

end
end TrainVerify.Denote.SourceDPGradientRelations
