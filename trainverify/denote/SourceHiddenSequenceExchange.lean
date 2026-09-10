import denote.AllToAllSourceFaithful
import denote.KRankAllToAll
import denote.KRankLinearGather

namespace TrainVerify.Denote.SourceHiddenSequenceExchange

noncomputable section
set_option maxHeartbeats 500000

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

private theorem divmod_mul_add (a d c : Nat) (hd : 0 < d) (hc : c < d) :
    (a * d + c) / d = a ∧ (a * d + c) % d = c := by
  constructor
  · rw [show a * d + c = c + d * a by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [show a * d + c = c + d * a by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- Sequence splitting preserves the batch and local hidden dimensions. -/
theorem sequence_chunk_shape (T B S H destination : Nat) (x : Tensor)
    (hT : 0 < T) (hx : x.shape = [B, S * T, H]) :
    (chunkPrimDimN 1 T destination x).shape = [B, S, H] := by
  rw [chunkPrimDimN_shape 1 T destination x _ hx (Nat.ne_of_gt hT)]
  simp [List.set, List.getD, Nat.ne_of_gt hT]

/-- Coordinate read of the actual sender split, not a gather-then-chunk model. -/
theorem sequence_chunk_valAt
    (T B S H : Nat) (x : Tensor) (dst : Fin T) (b s j : Nat)
    (hT : 0 < T) (hS : 0 < S) (hH : 0 < H)
    (hx : x.shape = [B, S * T, H]) (hb : b < B) (hs : s < S) (hj : j < H) :
    valAt (chunkPrimDimN 1 T dst.val x) ((b * S + s) * H + j) =
      valAt x ((b * (S * T) + (dst.val * S + s)) * H + j) := by
  have hlocal : s * H + j < S * H := flat_lt hs hj
  have hbound : (b * S + s) * H + j < B * S * H :=
    flat_lt (flat_lt hb hs) hj
  have hout : (b * S + s) * H + j <
      prodShape (chunkPrimDimN 1 T dst.val x).shape := by
    rw [sequence_chunk_shape T B S H dst.val x hT hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  have heq : (b * S + s) * H + j = b * (S * H) + (s * H + j) := by ring
  have houter := divmod_mul_add b (S * H) (s * H + j) (Nat.mul_pos hS hH) hlocal
  have hinner := divmod_mul_add s H j hH hj
  rw [valAt_of_lt _ _ hout]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.drop, List.foldl, Nat.one_mul, Nat.ne_of_gt hT, ite_false,
    Nat.mul_div_cancel _ hT, Nat.ne_of_gt hH,
    Nat.ne_of_gt (Nat.mul_pos hS hH), Nat.mod_eq_of_lt dst.isLt,
    heq, houter.1, houter.2, hinner.1, hinner.2]
  congr 1
  ring

/-- The hidden gather of arbitrary ordered senders has the full hidden width. -/
theorem hidden_gather_shape (T B S H : Nat) (xs : List Tensor)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H]) :
    (allGatherPrimDimN 2 T 0 xs).shape = [B, S * T, H * T] := by
  rw [allGatherPrimDimN_shape 2 T xs _ (head_shape T xs _ hT hlen hxs)]
  simp [List.set, List.getD]

/-- Each faithful receiver concatenates the ordered senders' sequence chunks. -/
theorem destination_shape (T B S H : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H]) :
    (AllToAllSourceFaithful.tensor T dst.val 2 1 xs).shape = [B, S, H * T] := by
  have hp : ∀ x ∈ xs.map (chunkPrimDimN 1 T dst.val), x.shape = [B, S, H] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact sequence_chunk_shape T B S H dst.val y hT (hxs y hy)
  unfold AllToAllSourceFaithful.tensor
  rw [allGatherPrimDimN_shape 2 T _ _ (head_shape T _ _ hT
    (by rw [List.length_map, hlen]) hp)]
  simp [List.set, List.getD]

/-- Hidden-to-sequence exchange for arbitrary ordered tensor inputs.
The left side is the source-faithful sender-split then receiver-gather flow.
The equality to gather-then-chunk is proved, never used as a definition. -/
theorem destination_eq_sequence_chunk
    (T B S H : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H]) :
    AllToAllSourceFaithful.tensor T dst.val 2 1 xs =
      chunkPrimDimN 1 T dst.val (allGatherPrimDimN 2 T 0 xs) := by
  let pieces := xs.map (chunkPrimDimN 1 T dst.val)
  have hplen : pieces.length = T := by rw [List.length_map, hlen]
  have hpieces : ∀ x ∈ pieces, x.shape = [B, S, H] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact sequence_chunk_shape T B S H dst.val y hT (hxs y hy)
  have hphead := head_shape T pieces [B, S, H] hT hplen hpieces
  have hxhead := head_shape T xs [B, S * T, H] hT hlen hxs
  have hgshape := hidden_gather_shape T B S H xs hT hlen hxs
  have hlshape := destination_shape T B S H xs dst hT hlen hxs
  have hrshape := sequence_chunk_shape T B S (H * T) dst.val
    (allGatherPrimDimN 2 T 0 xs) hT hgshape
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < B * S * (H * T) := by
    rw [hlshape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hHT : 0 < H * T := Nat.mul_pos hH hT
  let row := idx / (H * T)
  let col := idx % (H * T)
  let b := row / S
  let s := row % S
  let r := col / H
  let j := col % H
  have hrow : row < B * S := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hbound
  have hcol : col < H * T := Nat.mod_lt _ hHT
  have hb : b < B := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hrow
  have hs : s < S := Nat.mod_lt _ hS
  have hr : r < T := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hcol
  have hj : j < H := Nat.mod_lt _ hH
  have hrowEq : row = b * S + s := by
    simpa only [b, s, Nat.mul_comm] using (Nat.div_add_mod row S).symm
  have hcolEq : col = r * H + j := by
    simpa only [r, j, Nat.mul_comm] using (Nat.div_add_mod col H).symm
  have hidxEq : idx = (b * S + s) * (H * T) + (r * H + j) := by
    calc
      idx = row * (H * T) + col := by
        simpa only [row, col, Nat.mul_comm] using (Nat.div_add_mod idx (H * T)).symm
      _ = (b * S + s) * (H * T) + (r * H + j) := by rw [hrowEq, hcolEq]
  have hpre : b * S + s < B * S := flat_lt hb hs
  have hseq : dst.val * S + s < S * T := by
    simpa only [Nat.mul_comm] using flat_lt dst.isLt hs
  have hfullpre : b * (S * T) + (dst.val * S + s) < B * (S * T) :=
    flat_lt hb hseq
  have hrlen : r < xs.length := by rw [hlen]; exact hr
  let sender := xs.get ⟨r, hrlen⟩
  have hsender : sender.shape = [B, S * T, H] :=
    hxs sender (List.get_mem xs ⟨r, hrlen⟩)
  have hget : xs.getD r (zeroTensor [B, S * T, H]) = sender := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, sender]
  have hpget : pieces.getD r (zeroTensor [B, S, H]) =
      chunkPrimDimN 1 T dst.val sender := by
    have hrl : r < pieces.length := by rw [hplen]; exact hr
    simp [List.getD, List.getElem?_eq_getElem hrl, pieces, sender]
  rw [hidxEq]
  change valAt (allGatherPrimDimN 2 T 0 pieces) _ = _
  rw [allGatherPrimDimN_dim2_3d_valAt pieces T B S H (b * S + s) r j
    hT hH hpre hr hj hphead, hpget]
  rw [sequence_chunk_valAt T B S H sender dst b s j hT hS hH hsender hb hs hj]
  rw [sequence_chunk_valAt T B S (H * T) (allGatherPrimDimN 2 T 0 xs)
    dst b s (r * H + j) hT hS hHT hgshape hb hs
    (by rw [← hcolEq]; exact hcol)]
  rw [allGatherPrimDimN_dim2_3d_valAt xs T B (S * T) H
    (b * (S * T) + (dst.val * S + s)) r j
    hT hH hfullpre hr hj hxhead, hget]

/-- Gathering the faithful destinations in destination order reconstructs the
hidden gather of the original ordered sender list. No output-value premise is
needed; only input shapes, length, and positive dimensions are assumed. -/
theorem hidden_to_sequence_exchange
    (T B S H : Nat) (xs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H]) :
    allGatherPrimDimN 1 T 0
        (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 2 1 xs) =
      allGatherPrimDimN 2 T 0 xs := by
  have hdest :
      (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 2 1 xs) =
        List.ofFn (fun dst : Fin T =>
          chunkPrimDimN 1 T dst.val (allGatherPrimDimN 2 T 0 xs)) := by
    apply congrArg List.ofFn
    funext dst
    exact destination_eq_sequence_chunk T B S H xs dst hT hB hS hH hlen hxs
  rw [hdest]
  apply allGatherPrimDimN_chunks_ofFn 1 T (allGatherPrimDimN 2 T 0 xs) hT
  · rw [hidden_gather_shape T B S H xs hT hlen hxs]
    change 1 < 3
    decide
  · rw [hidden_gather_shape T B S H xs hT hlen hxs]
    simp [List.getD]

/-- Output-name adapter retaining the global shape, all destination shapes and
value reconstruction. The input reconstruction is a predecessor fact; each
output is tied to its faithful exchange, not assumed to reconstruct globally. -/
theorem output_facts
    (D u T B S H : Nat) (global : Tensor) (xs outputs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H])
    (hglobal : global.shape = [B * D, S * T, H * T])
    (hpre : chunkPrimDimN 0 D u global = allGatherPrimDimN 2 T 0 xs)
    (houtputs : outputs = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 2 1 xs)) :
    global.shape = [B * D, S * T, H * T] ∧
    (∀ x ∈ outputs, x.shape = [B, S, H * T]) ∧
    chunkPrimDimN 0 D u global = allGatherPrimDimN 1 T 0 outputs := by
  refine ⟨hglobal, ?_, ?_⟩
  · rw [houtputs]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    exact destination_shape T B S H xs dst hT hlen hxs
  · rw [houtputs]
    exact hpre.trans (hidden_to_sequence_exchange T B S H xs hT hB hS hH hlen hxs).symm

#print axioms output_facts
#print axioms sequence_chunk_valAt
#print axioms destination_shape
#print axioms destination_eq_sequence_chunk
#print axioms hidden_to_sequence_exchange

end
end TrainVerify.Denote.SourceHiddenSequenceExchange
