import denote.AllToAllSourceFaithful
import denote.KRankAllToAll
import denote.KRankMatmulQueryAxis

namespace TrainVerify.Denote.SourceRank4MiddleExchange

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

private theorem split_index (i A D : Nat) (hD : 0 < D) (hi : i < A * D) :
    ∃ a c : Nat, a < A ∧ c < D ∧ i = a * D + c := by
  refine ⟨i / D, i % D, ?_, Nat.mod_lt _ hD, ?_⟩
  · apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hi
  · simpa only [Nat.mul_comm] using (Nat.div_add_mod i D).symm

private theorem coordinates4 (i B S H C : Nat)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hi : i < B * S * H * C) :
    ∃ b s h c : Nat, b < B ∧ s < S ∧ h < H ∧ c < C ∧
      i = ((b * S + s) * H + h) * C + c := by
  obtain ⟨row, c, hrow, hc, hiEq⟩ := split_index i (B * S * H) C hC hi
  obtain ⟨pre, h, hpre, hh, hrowEq⟩ := split_index row (B * S) H hH hrow
  obtain ⟨b, s, hb, hs, hpreEq⟩ := split_index pre B S hS hpre
  refine ⟨b, s, h, c, hb, hs, hh, hc, ?_⟩
  rw [hiEq, hrowEq, hpreEq]

private theorem chunk1_shape (T B S H C destination : Nat) (x : Tensor)
    (hT : 0 < T) (hx : x.shape = [B, S * T, H, C]) :
    (chunkPrimDimN 1 T destination x).shape = [B, S, H, C] := by
  rw [chunkPrimDimN_shape 1 T destination x _ hx (Nat.ne_of_gt hT)]
  simp [List.set, List.getD, Nat.ne_of_gt hT]

-- Read the actual sender's sequence chunk, retaining both trailing coordinates.
private theorem chunk1_valAt
    (T B S H C : Nat) (x : Tensor) (dst : Fin T) (b s h c : Nat)
    (hT : 0 < T) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hx : x.shape = [B, S * T, H, C])
    (hb : b < B) (hs : s < S) (hh : h < H) (hc : c < C) :
    valAt (chunkPrimDimN 1 T dst.val x) (((b * S + s) * H + h) * C + c) =
      valAt x (((b * (S * T) + (dst.val * S + s)) * H + h) * C + c) := by
  have hHC : 0 < H * C := Nat.mul_pos hH hC
  have htail : h * C + c < H * C := flat_lt hh hc
  have hlocal : s * (H * C) + (h * C + c) < S * (H * C) := flat_lt hs htail
  have hbound : ((b * S + s) * H + h) * C + c < B * S * H * C :=
    flat_lt (flat_lt (flat_lt hb hs) hh) hc
  have hout : ((b * S + s) * H + h) * C + c <
      prodShape (chunkPrimDimN 1 T dst.val x).shape := by
    rw [chunk1_shape T B S H C dst.val x hT hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  have heq : ((b * S + s) * H + h) * C + c =
      b * (S * (H * C)) + (s * (H * C) + (h * C + c)) := by ring
  have houter := divmod_mul_add b (S * (H * C))
    (s * (H * C) + (h * C + c)) (Nat.mul_pos hS hHC) hlocal
  have hinner := divmod_mul_add s (H * C) (h * C + c) hHC htail
  rw [valAt_of_lt _ _ hout]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.drop, List.foldl, Nat.one_mul, Nat.ne_of_gt hT, ite_false,
    Nat.mul_div_cancel _ hT, Nat.ne_of_gt hHC,
    Nat.ne_of_gt (Nat.mul_pos hS hHC), Nat.mod_eq_of_lt dst.isLt,
    heq, houter.1, houter.2, hinner.1, hinner.2]
  congr 1
  ring

private theorem gather2_shape (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C]) :
    (allGatherPrimDimN 2 T 0 xs).shape = [B, S, H * T, C] := by
  rw [allGatherPrimDimN_shape 2 T xs _ (head_shape T xs _ hT hlen hxs)]
  simp [List.set, List.getD]

private theorem destination_shape (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H, C]) :
    (AllToAllSourceFaithful.tensor T dst.val 2 1 xs).shape = [B, S, H * T, C] := by
  unfold AllToAllSourceFaithful.tensor
  apply gather2_shape T B S H C _ hT (by rw [List.length_map, hlen])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact chunk1_shape T B S H C dst.val y hT (hxs y hy)

/-- Rank-4 middle exchange: the faithful axis-1 sender split followed by
axis-2 receiver gather equals an axis-1 chunk of the original axis-2 gather.
The sender is selected by the gathered head coordinate, not by sequence. -/
theorem axis2_destination_eq_chunk1
    (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H, C]) :
    AllToAllSourceFaithful.tensor T dst.val 2 1 xs =
      chunkPrimDimN 1 T dst.val (allGatherPrimDimN 2 T 0 xs) := by
  let pieces := xs.map (chunkPrimDimN 1 T dst.val)
  have hplen : pieces.length = T := by rw [List.length_map, hlen]
  have hpieces : ∀ x ∈ pieces, x.shape = [B, S, H, C] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact chunk1_shape T B S H C dst.val y hT (hxs y hy)
  have hphead := head_shape T pieces [B, S, H, C] hT hplen hpieces
  have hxhead := head_shape T xs [B, S * T, H, C] hT hlen hxs
  have hgshape := gather2_shape T B (S * T) H C xs hT hlen hxs
  have hlshape := destination_shape T B S H C xs dst hT hlen hxs
  have hrshape := chunk1_shape T B S (H * T) C dst.val
    (allGatherPrimDimN 2 T 0 xs) hT hgshape
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < B * S * (H * T) * C := by
    rw [hlshape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  obtain ⟨b, s, q, c, hb, hs, hq, hc, hidxEq⟩ :=
    coordinates4 idx B S (H * T) C hS (Nat.mul_pos hH hT) hC hbound
  obtain ⟨r, h, hr, hh, hqEq⟩ := split_index q T H hH
    (by simpa only [Nat.mul_comm] using hq)
  have hhead : r * H + h < H * T := by rw [← hqEq]; exact hq
  have hpre : b * S + s < B * S := flat_lt hb hs
  have hseq : dst.val * S + s < S * T := by
    simpa only [Nat.mul_comm] using flat_lt dst.isLt hs
  have hfullpre : b * (S * T) + (dst.val * S + s) < B * (S * T) :=
    flat_lt hb hseq
  have hrlen : r < xs.length := by rw [hlen]; exact hr
  let sender := xs.get ⟨r, hrlen⟩
  have hsender : sender.shape = [B, S * T, H, C] :=
    hxs sender (List.get_mem xs ⟨r, hrlen⟩)
  have hget : xs.getD r (zeroTensor [B, S * T, H, C]) = sender := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, sender]
  have hpget : pieces.getD r (zeroTensor [B, S, H, C]) =
      chunkPrimDimN 1 T dst.val sender := by
    have hrl : r < pieces.length := by rw [hplen]; exact hr
    simp [List.getD, List.getElem?_eq_getElem hrl, pieces, sender]
  rw [hqEq] at hidxEq
  rw [hidxEq]
  unfold AllToAllSourceFaithful.tensor
  change valAt (allGatherPrimDimN 2 T 0 pieces) _ = _
  rw [allGatherPrimDimN_dim2_4d_valAt pieces T B S H C (b * S + s) r h c
    hT hH hC hpre hr hh hc hphead, hpget]
  rw [chunk1_valAt T B S H C sender dst b s h c hT hS hH hC hsender hb hs hh hc]
  rw [chunk1_valAt T B S (H * T) C (allGatherPrimDimN 2 T 0 xs)
    dst b s (r * H + h) c hT hS (Nat.mul_pos hH hT) hC hgshape hb hs hhead hc]
  rw [allGatherPrimDimN_dim2_4d_valAt xs T B (S * T) H C
    (b * (S * T) + (dst.val * S + s)) r h c
    hT hH hC hfullpre hr hh hc hxhead, hget]

/-- Gathering faithful destinations in destination order on axis 1 reconstructs
 the original ordered sender gather on axis 2. -/
theorem axis2_exchange
    (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H, C]) :
    allGatherPrimDimN 1 T 0
        (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 2 1 xs) =
      allGatherPrimDimN 2 T 0 xs := by
  have hdest :
      (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 2 1 xs) =
        List.ofFn (fun dst : Fin T =>
          chunkPrimDimN 1 T dst.val (allGatherPrimDimN 2 T 0 xs)) := by
    apply congrArg List.ofFn
    funext dst
    exact axis2_destination_eq_chunk1 T B S H C xs dst hT hB hS hH hC hlen hxs
  rw [hdest]
  apply allGatherPrimDimN_chunks_ofFn 1 T (allGatherPrimDimN 2 T 0 xs) hT
  · rw [gather2_shape T B (S * T) H C xs hT hlen hxs]
    change 1 < 4
    decide
  · rw [gather2_shape T B (S * T) H C xs hT hlen hxs]
    simp [List.getD]

/-- Strong algebraic output adapter: only predecessor reconstruction is assumed.
Actual ordered faithful outputs determine local shapes and reconstruction;
DP ownership and source-renderer integration remain separate obligations. -/
theorem axis2_output_facts
    (D u T B S H C : Nat) (global : Tensor) (xs outputs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S * T, H, C])
    (hglobal : global.shape = [B * D, S * T, H * T, C])
    (hpre : chunkPrimDimN 0 D u global = allGatherPrimDimN 2 T 0 xs)
    (houtputs : outputs = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 2 1 xs)) :
    global.shape = [B * D, S * T, H * T, C] ∧
    (∀ x ∈ outputs, x.shape = [B, S, H * T, C]) ∧
    chunkPrimDimN 0 D u global = allGatherPrimDimN 1 T 0 outputs := by
  refine ⟨hglobal, ?_, ?_⟩
  · rw [houtputs]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    exact destination_shape T B S H C xs dst hT hlen hxs
  · rw [houtputs]
    exact hpre.trans (axis2_exchange T B S H C xs hT hB hS hH hC hlen hxs).symm

#print axioms axis2_destination_eq_chunk1
#print axioms axis2_exchange
#print axioms axis2_output_facts

end
end TrainVerify.Denote.SourceRank4MiddleExchange
