import denote.AllToAllSourceFaithful
import denote.KRankAllToAll
import denote.KRankLinearGather

namespace TrainVerify.Denote.SourceSequenceHiddenExchange

noncomputable section
set_option maxHeartbeats 500000

-- ScalarTensorDenote library facts only: no source-renderer, Torch, or DP
-- ownership claim. Sender order and destination order are both significant.
private theorem head_shape (T : Nat) (xs : List Tensor) (sh : Shape)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = sh) :
    (xs.head?.map Tensor.shape).getD [] = sh := by
  cases xs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons x rest =>
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact hxs x (List.mem_cons_self ..)

private theorem flat_lt {a A b B : Nat} (ha : a < A) (hb : b < B) :
    a * B + b < A * B := by
  calc
    a * B + b < a * B + B := Nat.add_lt_add_left hb _
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B ha

private theorem split_index (i A D : Nat) (hD : 0 < D) (hi : i < A * D) :
    ∃ a c : Nat, a < A ∧ c < D ∧ i = a * D + c := by
  refine ⟨i / D, i % D, ?_, Nat.mod_lt _ hD, ?_⟩
  · apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hi
  · simpa only [Nat.mul_comm] using (Nat.div_add_mod i D).symm

private theorem hidden_chunk_shape (T B S H destination : Nat) (x : Tensor)
    (hT : 0 < T) (hx : x.shape = [B, S, H * T]) :
    (chunkPrimDimN 2 T destination x).shape = [B, S, H] := by
  rw [chunkPrimDimN_shape 2 T destination x _ hx (Nat.ne_of_gt hT)]
  simp [List.set, List.getD, Nat.ne_of_gt hT]

-- The destination chooses a contiguous hidden block in each original sender.
private theorem hidden_chunk_valAt
    (T B S H : Nat) (x : Tensor) (dst : Fin T) (b s j : Nat)
    (hT : 0 < T) (hH : 0 < H)
    (hx : x.shape = [B, S, H * T]) (hb : b < B) (hs : s < S) (hj : j < H) :
    valAt (chunkPrimDimN 2 T dst.val x) ((b * S + s) * H + j) =
      valAt x ((b * S + s) * (H * T) + (dst.val * H + j)) := by
  have hbound : (b * S + s) * H + j < B * S * H :=
    flat_lt (flat_lt hb hs) hj
  have hout : (b * S + s) * H + j <
      prodShape (chunkPrimDimN 2 T dst.val x).shape := by
    rw [hidden_chunk_shape T B S H dst.val x hT hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  have hdiv : ((b * S + s) * H + j) / H = b * S + s := by
    rw [show (b * S + s) * H + j = j + H * (b * S + s) by ring,
      Nat.add_mul_div_left _ _ hH, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : ((b * S + s) * H + j) % H = j := by
    rw [show (b * S + s) * H + j = j + H * (b * S + s) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [valAt_of_lt _ _ hout]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.drop, List.foldl, Nat.ne_of_gt hT, ite_false,
    Nat.mul_div_cancel _ hT, Nat.mul_one, Nat.ne_of_gt hH,
    Nat.mod_eq_of_lt dst.isLt, hdiv, hmod, Nat.div_one, Nat.mod_one,
    Nat.add_zero, Nat.one_ne_zero]

private theorem sequence_gather_shape (T B S H : Nat) (xs : List Tensor)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H]) :
    (allGatherPrimDimN 1 T 0 xs).shape = [B, S * T, H] := by
  rw [allGatherPrimDimN_shape 1 T xs _ (head_shape T xs _ hT hlen hxs)]
  simp [List.set, List.getD]

/-- Each faithful AA(1,2) destination gathers the ordered senders' hidden chunks. -/
theorem destination_shape (T B S H : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T]) :
    (AllToAllSourceFaithful.tensor T dst.val 1 2 xs).shape = [B, S * T, H] := by
  unfold AllToAllSourceFaithful.tensor
  apply sequence_gather_shape T B S H _ hT (by rw [List.length_map, hlen])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hidden_chunk_shape T B S H dst.val y hT (hxs y hy)

-- Value equality is derived from the actual split/gather flow, not used as
-- its definition. The sequence coordinate selects the sender, not destination.
private theorem destination_eq_hidden_chunk
    (T B S H : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T]) :
    AllToAllSourceFaithful.tensor T dst.val 1 2 xs =
      chunkPrimDimN 2 T dst.val (allGatherPrimDimN 1 T 0 xs) := by
  let pieces := xs.map (chunkPrimDimN 2 T dst.val)
  have hplen : pieces.length = T := by rw [List.length_map, hlen]
  have hpieces : ∀ x ∈ pieces, x.shape = [B, S, H] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hidden_chunk_shape T B S H dst.val y hT (hxs y hy)
  have hphead := head_shape T pieces [B, S, H] hT hplen hpieces
  have hxhead := head_shape T xs [B, S, H * T] hT hlen hxs
  have hgshape := sequence_gather_shape T B S (H * T) xs hT hlen hxs
  have hlshape := destination_shape T B S H xs dst hT hlen hxs
  have hrshape := hidden_chunk_shape T B (S * T) H dst.val
    (allGatherPrimDimN 1 T 0 xs) hT hgshape
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < B * (S * T) * H := by
    rw [hlshape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  obtain ⟨row, j, hrow, hj, hidxEq⟩ := split_index idx (B * (S * T)) H hH hbound
  obtain ⟨b, q, hb, hq, hrowEq⟩ :=
    split_index row B (S * T) (Nat.mul_pos hS hT) hrow
  obtain ⟨r, s, hr, hs, hqEq⟩ := split_index q T S hS
    (by simpa only [Nat.mul_comm] using hq)
  have hseq : r * S + s < S * T := by rw [← hqEq]; exact hq
  have hdstj : dst.val * H + j < H * T := by
    simpa only [Nat.mul_comm] using flat_lt dst.isLt hj
  have hrlen : r < xs.length := by rw [hlen]; exact hr
  let sender := xs.get ⟨r, hrlen⟩
  have hsender : sender.shape = [B, S, H * T] :=
    hxs sender (List.get_mem xs ⟨r, hrlen⟩)
  have hget : xs.getD r (zeroTensor [B, S, H * T]) = sender := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, sender]
  have hpget : pieces.getD r (zeroTensor [B, S, H]) =
      chunkPrimDimN 2 T dst.val sender := by
    have hrl : r < pieces.length := by rw [hplen]; exact hr
    simp [List.getD, List.getElem?_eq_getElem hrl, pieces, sender]
  rw [hrowEq, hqEq] at hidxEq
  rw [hidxEq]
  unfold AllToAllSourceFaithful.tensor
  change valAt (allGatherPrimDimN 1 T 0 pieces) _ = _
  rw [allGatherPrimDimN1_3d_valAt T B S H pieces
    hT hB hS hH hphead b hb r hr s hs j hj, hpget]
  rw [hidden_chunk_valAt T B S H sender dst b s j hT hH hsender hb hs hj]
  rw [hidden_chunk_valAt T B (S * T) H (allGatherPrimDimN 1 T 0 xs)
    dst b (r * S + s) j hT hH hgshape hb hseq hj]
  rw [allGatherPrimDimN1_3d_valAt T B S (H * T) xs
    hT hB hS (Nat.mul_pos hH hT) hxhead b hb r hr s hs (dst.val * H + j) hdstj,
    hget]

/-- Gathering faithful destinations in destination order on the hidden axis
reconstructs the sequence gather of arbitrary ordered rank-3 senders. -/
theorem sequence_to_hidden_exchange
    (T B S H : Nat) (xs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T]) :
    allGatherPrimDimN 2 T 0
        (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 1 2 xs) =
      allGatherPrimDimN 1 T 0 xs := by
  have hdest :
      (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 1 2 xs) =
        List.ofFn (fun dst : Fin T =>
          chunkPrimDimN 2 T dst.val (allGatherPrimDimN 1 T 0 xs)) := by
    apply congrArg List.ofFn
    funext dst
    exact destination_eq_hidden_chunk T B S H xs dst hT hB hS hH hlen hxs
  rw [hdest]
  apply allGatherPrimDimN_chunks_ofFn 2 T (allGatherPrimDimN 1 T 0 xs) hT
  · rw [sequence_gather_shape T B S (H * T) xs hT hlen hxs]
    change 2 < 3
    decide
  · rw [sequence_gather_shape T B S (H * T) xs hT hlen hxs]
    simp [List.getD]

/-- Preserve the unchanged global input and predecessor DP reconstruction.
Local output shapes and hidden-axis reconstruction are conclusions, not premises. -/
theorem output_facts
    (D u T B S H : Nat) (full : Tensor) (xs ys : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T])
    (hfullshape : full.shape = [B * D, S * T, H * T])
    (hpre : chunkPrimDimN 0 D u full = allGatherPrimDimN 1 T 0 xs)
    (houtputs : ys = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 1 2 xs)) :
    full.shape = [B * D, S * T, H * T] ∧
    (∀ x ∈ ys, x.shape = [B, S * T, H]) ∧
    chunkPrimDimN 0 D u full = allGatherPrimDimN 2 T 0 ys := by
  refine ⟨hfullshape, ?_, ?_⟩
  · rw [houtputs]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    exact destination_shape T B S H xs dst hT hlen hxs
  · rw [houtputs]
    exact hpre.trans (sequence_to_hidden_exchange T B S H xs hT hB hS hH hlen hxs).symm

#print axioms destination_shape
#print axioms sequence_to_hidden_exchange
#print axioms output_facts

end
end TrainVerify.Denote.SourceSequenceHiddenExchange
