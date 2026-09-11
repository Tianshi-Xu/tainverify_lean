import denote.AllToAllSourceFaithful
import denote.KRankAllToAll
import denote.KRankMatmulHeadAxis

namespace TrainVerify.Denote.SourceRank4InnerExchange

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

private theorem chunk2_shape (T B S H C destination : Nat) (x : Tensor)
    (hT : 0 < T) (hx : x.shape = [B, S, H * T, C]) :
    (chunkPrimDimN 2 T destination x).shape = [B, S, H, C] := by
  rw [chunkPrimDimN_shape 2 T destination x _ hx (Nat.ne_of_gt hT)]
  simp [List.set, List.getD, Nat.ne_of_gt hT]

-- Read the actual sender's head chunk; neither sequence nor channel is split.
private theorem chunk2_valAt
    (T B S H C : Nat) (x : Tensor) (dst : Fin T) (b s h c : Nat)
    (hT : 0 < T) (hH : 0 < H) (hC : 0 < C)
    (hx : x.shape = [B, S, H * T, C])
    (hb : b < B) (hs : s < S) (hh : h < H) (hc : c < C) :
    valAt (chunkPrimDimN 2 T dst.val x) (((b * S + s) * H + h) * C + c) =
      valAt x (((b * S + s) * (H * T) + (dst.val * H + h)) * C + c) := by
  have hHC : 0 < H * C := Nat.mul_pos hH hC
  have htail : h * C + c < H * C := flat_lt hh hc
  have hbound : ((b * S + s) * H + h) * C + c < B * S * H * C :=
    flat_lt (flat_lt (flat_lt hb hs) hh) hc
  have hout : ((b * S + s) * H + h) * C + c <
      prodShape (chunkPrimDimN 2 T dst.val x).shape := by
    rw [chunk2_shape T B S H C dst.val x hT hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  have heq : ((b * S + s) * H + h) * C + c =
      (b * S + s) * (H * C) + (h * C + c) := by ring
  have houter := divmod_mul_add (b * S + s) (H * C) (h * C + c) hHC htail
  have hinner := divmod_mul_add h C c hC hc
  rw [valAt_of_lt _ _ hout]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.drop, List.foldl, Nat.one_mul, Nat.ne_of_gt hT, ite_false,
    Nat.mul_div_cancel _ hT, Nat.ne_of_gt hHC, Nat.ne_of_gt hC,
    Nat.mod_eq_of_lt dst.isLt, heq, houter.1, houter.2, hinner.1, hinner.2]
  congr 1
  ring

private theorem gather1_shape (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C]) :
    (allGatherPrimDimN 1 T 0 xs).shape = [B, S * T, H, C] := by
  rw [allGatherPrimDimN_shape 1 T xs _ (head_shape T xs _ hT hlen hxs)]
  simp [List.set, List.getD]

private theorem destination_shape (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T, C]) :
    (AllToAllSourceFaithful.tensor T dst.val 1 2 xs).shape = [B, S * T, H, C] := by
  unfold AllToAllSourceFaithful.tensor
  apply gather1_shape T B S H C _ hT (by rw [List.length_map, hlen])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact chunk2_shape T B S H C dst.val y hT (hxs y hy)

/-- Faithful rank-4 axis-2 sender split followed by axis-1 receiver gather.
The sequence coordinate selects the ordered sender; the destination selects
its head block, and both batch and trailing channel coordinates are retained. -/
theorem axis1_destination_eq_chunk2
    (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T, C]) :
    AllToAllSourceFaithful.tensor T dst.val 1 2 xs =
      chunkPrimDimN 2 T dst.val (allGatherPrimDimN 1 T 0 xs) := by
  let pieces := xs.map (chunkPrimDimN 2 T dst.val)
  have hplen : pieces.length = T := by rw [List.length_map, hlen]
  have hpieces : ∀ x ∈ pieces, x.shape = [B, S, H, C] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact chunk2_shape T B S H C dst.val y hT (hxs y hy)
  have hphead := head_shape T pieces [B, S, H, C] hT hplen hpieces
  have hxhead := head_shape T xs [B, S, H * T, C] hT hlen hxs
  have hgshape := gather1_shape T B S (H * T) C xs hT hlen hxs
  have hlshape := destination_shape T B S H C xs dst hT hlen hxs
  have hrshape := chunk2_shape T B (S * T) H C dst.val
    (allGatherPrimDimN 1 T 0 xs) hT hgshape
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < B * (S * T) * H * C := by
    rw [hlshape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  obtain ⟨b, q, h, c, hb, hq, hh, hc, hidxEq⟩ :=
    coordinates4 idx B (S * T) H C (Nat.mul_pos hS hT) hH hC hbound
  obtain ⟨r, s, hr, hs, hqEq⟩ := split_index q T S hS
    (by simpa only [Nat.mul_comm] using hq)
  have hseq : r * S + s < S * T := by rw [← hqEq]; exact hq
  have hdsth : dst.val * H + h < H * T := by
    simpa only [Nat.mul_comm] using flat_lt dst.isLt hh
  have hrlen : r < xs.length := by rw [hlen]; exact hr
  let sender := xs.get ⟨r, hrlen⟩
  have hsender : sender.shape = [B, S, H * T, C] :=
    hxs sender (List.get_mem xs ⟨r, hrlen⟩)
  have hget : xs.getD r (zeroTensor [B, S, H * T, C]) = sender := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, sender]
  have hpget : pieces.getD r (zeroTensor [B, S, H, C]) =
      chunkPrimDimN 2 T dst.val sender := by
    have hrl : r < pieces.length := by rw [hplen]; exact hr
    simp [List.getD, List.getElem?_eq_getElem hrl, pieces, sender]
  rw [hqEq] at hidxEq
  rw [hidxEq]
  unfold AllToAllSourceFaithful.tensor
  change valAt (allGatherPrimDimN 1 T 0 pieces) _ = _
  rw [allGatherPrimDimN_dim1_4d_valAt pieces T B S H C b r s h c
    hT hS hH hC hb hr hs hh hc hphead, hpget]
  rw [chunk2_valAt T B S H C sender dst b s h c hT hH hC hsender hb hs hh hc]
  rw [chunk2_valAt T B (S * T) H C (allGatherPrimDimN 1 T 0 xs)
    dst b (r * S + s) h c hT hH hC hgshape hb hseq hh hc]
  rw [allGatherPrimDimN_dim1_4d_valAt xs T B S (H * T) C b r s
    (dst.val * H + h) c hT hS (Nat.mul_pos hH hT) hC hb hr hs hdsth hc hxhead,
    hget]

/-- Gathering faithful destinations in destination order on axis 2 reconstructs
 the original ordered sender gather on axis 1. -/
theorem axis1_exchange
    (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T, C]) :
    allGatherPrimDimN 2 T 0
        (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 1 2 xs) =
      allGatherPrimDimN 1 T 0 xs := by
  have hdest :
      (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 1 2 xs) =
        List.ofFn (fun dst : Fin T =>
          chunkPrimDimN 2 T dst.val (allGatherPrimDimN 1 T 0 xs)) := by
    apply congrArg List.ofFn
    funext dst
    exact axis1_destination_eq_chunk2 T B S H C xs dst hT hB hS hH hC hlen hxs
  rw [hdest]
  apply allGatherPrimDimN_chunks_ofFn 2 T (allGatherPrimDimN 1 T 0 xs) hT
  · rw [gather1_shape T B S (H * T) C xs hT hlen hxs]
    change 2 < 4
    decide
  · rw [gather1_shape T B S (H * T) C xs hT hlen hxs]
    simp [List.getD]

/-- Strong output adapter: only predecessor reconstruction is assumed.
Actual ordered faithful outputs determine local shapes and reconstruction;
DP ownership and source-renderer integration remain separate obligations. -/
theorem axis1_output_facts
    (D u T B S H C : Nat) (global : Tensor) (xs outputs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H * T, C])
    (hglobal : global.shape = [B * D, S * T, H * T, C])
    (hpre : chunkPrimDimN 0 D u global = allGatherPrimDimN 1 T 0 xs)
    (houtputs : outputs = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 1 2 xs)) :
    global.shape = [B * D, S * T, H * T, C] ∧
    (∀ x ∈ outputs, x.shape = [B, S * T, H, C]) ∧
    chunkPrimDimN 0 D u global = allGatherPrimDimN 2 T 0 outputs := by
  refine ⟨hglobal, ?_, ?_⟩
  · rw [houtputs]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    exact destination_shape T B S H C xs dst hT hlen hxs
  · rw [houtputs]
    exact hpre.trans (axis1_exchange T B S H C xs hT hB hS hH hC hlen hxs).symm

#print axioms axis1_destination_eq_chunk2
#print axioms axis1_exchange
#print axioms axis1_output_facts

end
end TrainVerify.Denote.SourceRank4InnerExchange
