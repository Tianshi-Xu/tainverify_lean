import denote.AllToAllSourceFaithful
import denote.KRankAllToAll
import denote.KRankMatmulHeadAxis
import denote.KRankMatmulQueryAxis

namespace TrainVerify.Denote.SourceRank4Exchange

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

private theorem chunk3_shape (T B S H C destination : Nat) (x : Tensor)
    (hT : 0 < T) (hx : x.shape = [B, S, H, C * T]) :
    (chunkPrimDimN 3 T destination x).shape = [B, S, H, C] := by
  rw [chunkPrimDimN_shape 3 T destination x _ hx (Nat.ne_of_gt hT)]
  simp [List.set, List.getD, Nat.ne_of_gt hT]

-- Reads the actual sender split, with the destination selecting its channel block.
private theorem chunk3_valAt
    (T B S H C : Nat) (x : Tensor) (dst : Fin T) (b s h c : Nat)
    (hT : 0 < T) (hC : 0 < C)
    (hx : x.shape = [B, S, H, C * T])
    (hb : b < B) (hs : s < S) (hh : h < H) (hc : c < C) :
    valAt (chunkPrimDimN 3 T dst.val x) (((b * S + s) * H + h) * C + c) =
      valAt x (((b * S + s) * H + h) * (C * T) + dst.val * C + c) := by
  have hbound : ((b * S + s) * H + h) * C + c < B * S * H * C :=
    flat_lt (flat_lt (flat_lt hb hs) hh) hc
  have hout : ((b * S + s) * H + h) * C + c <
      prodShape (chunkPrimDimN 3 T dst.val x).shape := by
    rw [chunk3_shape T B S H C dst.val x hT hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  have hcoord := divmod_mul_add ((b * S + s) * H + h) C c hC hc
  rw [valAt_of_lt _ _ hout]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.drop, List.foldl, Nat.one_mul, Nat.mul_one, Nat.ne_of_gt hT,
    Nat.one_ne_zero, ite_false, Nat.mul_div_cancel _ hT, Nat.ne_of_gt hC,
    Nat.mod_eq_of_lt dst.isLt, hcoord.1, hcoord.2,
    Nat.div_one, Nat.mod_one, Nat.add_zero]
  congr 1
  ring

private theorem pieces_shape (T B S H C destination : Nat) (xs : List Tensor)
    (hT : 0 < T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    ∀ x ∈ xs.map (chunkPrimDimN 3 T destination), x.shape = [B, S, H, C] := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact chunk3_shape T B S H C destination y hT (hxs y hy)

private theorem gather1_shape (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C]) :
    (allGatherPrimDimN 1 T 0 xs).shape = [B, S * T, H, C] := by
  rw [allGatherPrimDimN_shape 1 T xs _ (head_shape T xs _ hT hlen hxs)]
  simp [List.set, List.getD]

private theorem gather2_shape (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C]) :
    (allGatherPrimDimN 2 T 0 xs).shape = [B, S, H * T, C] := by
  rw [allGatherPrimDimN_shape 2 T xs _ (head_shape T xs _ hT hlen hxs)]
  simp [List.set, List.getD]

private theorem destination1_shape (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    (AllToAllSourceFaithful.tensor T dst.val 1 3 xs).shape = [B, S * T, H, C] := by
  exact gather1_shape T B S H C _ hT (by rw [List.length_map, hlen])
    (pieces_shape T B S H C dst.val xs hT hxs)

private theorem destination2_shape (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    (AllToAllSourceFaithful.tensor T dst.val 2 3 xs).shape = [B, S, H * T, C] := by
  exact gather2_shape T B S H C _ hT (by rw [List.length_map, hlen])
    (pieces_shape T B S H C dst.val xs hT hxs)

/-- Axis-1 receiver gather commutes with the faithful axis-3 sender split. -/
theorem axis1_destination_eq_chunk3
    (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    AllToAllSourceFaithful.tensor T dst.val 1 3 xs =
      chunkPrimDimN 3 T dst.val (allGatherPrimDimN 1 T 0 xs) := by
  let pieces := xs.map (chunkPrimDimN 3 T dst.val)
  have hplen : pieces.length = T := by rw [List.length_map, hlen]
  have hpieces := pieces_shape T B S H C dst.val xs hT hxs
  have hphead := head_shape T pieces [B, S, H, C] hT hplen hpieces
  have hxhead := head_shape T xs [B, S, H, C * T] hT hlen hxs
  have hgshape := gather1_shape T B S H (C * T) xs hT hlen hxs
  have hlshape := destination1_shape T B S H C xs dst hT hlen hxs
  have hrshape := chunk3_shape T B (S * T) H C dst.val
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
  have hdstc : dst.val * C + c < C * T := by
    simpa only [Nat.mul_comm] using flat_lt dst.isLt hc
  have hrlen : r < xs.length := by rw [hlen]; exact hr
  let sender := xs.get ⟨r, hrlen⟩
  have hsender : sender.shape = [B, S, H, C * T] :=
    hxs sender (List.get_mem xs ⟨r, hrlen⟩)
  have hget : xs.getD r (zeroTensor [B, S, H, C * T]) = sender := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, sender]
  have hpget : pieces.getD r (zeroTensor [B, S, H, C]) =
      chunkPrimDimN 3 T dst.val sender := by
    have hrl : r < pieces.length := by rw [hplen]; exact hr
    simp [List.getD, List.getElem?_eq_getElem hrl, pieces, sender]
  rw [hqEq] at hidxEq
  rw [hidxEq]
  change valAt (allGatherPrimDimN 1 T 0 pieces) _ = _
  rw [allGatherPrimDimN_dim1_4d_valAt pieces T B S H C b r s h c
    hT hS hH hC hb hr hs hh hc hphead, hpget]
  rw [chunk3_valAt T B S H C sender dst b s h c hT hC hsender hb hs hh hc]
  rw [chunk3_valAt T B (S * T) H C (allGatherPrimDimN 1 T 0 xs)
    dst b (r * S + s) h c hT hC hgshape hb hseq hh hc]
  rw [show ((b * (S * T) + (r * S + s)) * H + h) * (C * T) +
      dst.val * C + c =
      ((b * (S * T) + (r * S + s)) * H + h) * (C * T) +
        (dst.val * C + c) by ring]
  rw [allGatherPrimDimN_dim1_4d_valAt xs T B S H (C * T) b r s h
    (dst.val * C + c) hT hS hH (Nat.mul_pos hC hT) hb hr hs hh hdstc hxhead,
    hget]
  congr 1
  ring

/-- Axis-2 receiver gather commutes with the faithful axis-3 sender split. -/
theorem axis2_destination_eq_chunk3
    (T B S H C : Nat) (xs : List Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    AllToAllSourceFaithful.tensor T dst.val 2 3 xs =
      chunkPrimDimN 3 T dst.val (allGatherPrimDimN 2 T 0 xs) := by
  let pieces := xs.map (chunkPrimDimN 3 T dst.val)
  have hplen : pieces.length = T := by rw [List.length_map, hlen]
  have hpieces := pieces_shape T B S H C dst.val xs hT hxs
  have hphead := head_shape T pieces [B, S, H, C] hT hplen hpieces
  have hxhead := head_shape T xs [B, S, H, C * T] hT hlen hxs
  have hgshape := gather2_shape T B S H (C * T) xs hT hlen hxs
  have hlshape := destination2_shape T B S H C xs dst hT hlen hxs
  have hrshape := chunk3_shape T B S (H * T) C dst.val
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
  have hdstc : dst.val * C + c < C * T := by
    simpa only [Nat.mul_comm] using flat_lt dst.isLt hc
  have hrlen : r < xs.length := by rw [hlen]; exact hr
  let sender := xs.get ⟨r, hrlen⟩
  have hsender : sender.shape = [B, S, H, C * T] :=
    hxs sender (List.get_mem xs ⟨r, hrlen⟩)
  have hget : xs.getD r (zeroTensor [B, S, H, C * T]) = sender := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, sender]
  have hpget : pieces.getD r (zeroTensor [B, S, H, C]) =
      chunkPrimDimN 3 T dst.val sender := by
    have hrl : r < pieces.length := by rw [hplen]; exact hr
    simp [List.getD, List.getElem?_eq_getElem hrl, pieces, sender]
  rw [hqEq] at hidxEq
  rw [hidxEq]
  change valAt (allGatherPrimDimN 2 T 0 pieces) _ = _
  rw [allGatherPrimDimN_dim2_4d_valAt pieces T B S H C (b * S + s) r h c
    hT hH hC hpre hr hh hc hphead, hpget]
  rw [chunk3_valAt T B S H C sender dst b s h c hT hC hsender hb hs hh hc]
  rw [chunk3_valAt T B S (H * T) C (allGatherPrimDimN 2 T 0 xs)
    dst b s (r * H + h) c hT hC hgshape hb hs hhead hc]
  rw [show ((b * S + s) * (H * T) + (r * H + h)) * (C * T) +
      dst.val * C + c =
      ((b * S + s) * (H * T) + (r * H + h)) * (C * T) +
        (dst.val * C + c) by ring]
  rw [allGatherPrimDimN_dim2_4d_valAt xs T B S H (C * T) (b * S + s) r h
    (dst.val * C + c) hT hH (Nat.mul_pos hC hT) hpre hr hh hdstc hxhead, hget]
  congr 1
  ring

/-- Ordered faithful axis-1 destinations reconstruct the original axis-1 gather. -/
theorem axis1_exchange
    (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    allGatherPrimDimN 3 T 0
        (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 1 3 xs) =
      allGatherPrimDimN 1 T 0 xs := by
  have hdest :
      (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 1 3 xs) =
        List.ofFn (fun dst : Fin T =>
          chunkPrimDimN 3 T dst.val (allGatherPrimDimN 1 T 0 xs)) := by
    apply congrArg List.ofFn
    funext dst
    exact axis1_destination_eq_chunk3 T B S H C xs dst hT hB hS hH hC hlen hxs
  rw [hdest]
  apply allGatherPrimDimN_chunks_ofFn 3 T (allGatherPrimDimN 1 T 0 xs) hT
  · rw [gather1_shape T B S H (C * T) xs hT hlen hxs]
    change 3 < 4
    decide
  · rw [gather1_shape T B S H (C * T) xs hT hlen hxs]
    simp [List.getD]

/-- Ordered faithful axis-2 destinations reconstruct the original axis-2 gather. -/
theorem axis2_exchange
    (T B S H C : Nat) (xs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T) (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T]) :
    allGatherPrimDimN 3 T 0
        (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 2 3 xs) =
      allGatherPrimDimN 2 T 0 xs := by
  have hdest :
      (List.ofFn fun dst : Fin T => AllToAllSourceFaithful.tensor T dst.val 2 3 xs) =
        List.ofFn (fun dst : Fin T =>
          chunkPrimDimN 3 T dst.val (allGatherPrimDimN 2 T 0 xs)) := by
    apply congrArg List.ofFn
    funext dst
    exact axis2_destination_eq_chunk3 T B S H C xs dst hT hB hS hH hC hlen hxs
  rw [hdest]
  apply allGatherPrimDimN_chunks_ofFn 3 T (allGatherPrimDimN 2 T 0 xs) hT
  · rw [gather2_shape T B S H (C * T) xs hT hlen hxs]
    change 3 < 4
    decide
  · rw [gather2_shape T B S H (C * T) xs hT hlen hxs]
    simp [List.getD]

/-- Strong output adapter: only the predecessor reconstructs by hypothesis;
all output values are fixed by the faithful source exchange. -/
theorem axis1_output_facts
    (D u T B S H C : Nat) (global : Tensor) (xs outputs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T])
    (hglobal : global.shape = [B * D, S * T, H, C * T])
    (hpre : chunkPrimDimN 0 D u global = allGatherPrimDimN 1 T 0 xs)
    (houtputs : outputs = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 1 3 xs)) :
    global.shape = [B * D, S * T, H, C * T] ∧
    (∀ x ∈ outputs, x.shape = [B, S * T, H, C]) ∧
    chunkPrimDimN 0 D u global = allGatherPrimDimN 3 T 0 outputs := by
  refine ⟨hglobal, ?_, ?_⟩
  · rw [houtputs]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    exact destination1_shape T B S H C xs dst hT hlen hxs
  · rw [houtputs]
    exact hpre.trans (axis1_exchange T B S H C xs hT hB hS hH hC hlen hxs).symm

/-- Axis-2 output adapter retaining global shape, actual local shapes, and values. -/
theorem axis2_output_facts
    (D u T B S H C : Nat) (global : Tensor) (xs outputs : List Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hlen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, S, H, C * T])
    (hglobal : global.shape = [B * D, S, H * T, C * T])
    (hpre : chunkPrimDimN 0 D u global = allGatherPrimDimN 2 T 0 xs)
    (houtputs : outputs = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 2 3 xs)) :
    global.shape = [B * D, S, H * T, C * T] ∧
    (∀ x ∈ outputs, x.shape = [B, S, H * T, C]) ∧
    chunkPrimDimN 0 D u global = allGatherPrimDimN 3 T 0 outputs := by
  refine ⟨hglobal, ?_, ?_⟩
  · rw [houtputs]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    exact destination2_shape T B S H C xs dst hT hlen hxs
  · rw [houtputs]
    exact hpre.trans (axis2_exchange T B S H C xs hT hB hS hH hC hlen hxs).symm

#print axioms axis1_destination_eq_chunk3
#print axioms axis2_destination_eq_chunk3
#print axioms axis1_exchange
#print axioms axis2_exchange
#print axioms axis1_output_facts
#print axioms axis2_output_facts

end
end TrainVerify.Denote.SourceRank4Exchange
