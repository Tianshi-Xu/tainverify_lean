import denote.ZigzagKAttention

/-! Actual rank-local rows of the arbitrary-K zigzag relation. The row map is
single-sequence, but the head and channel coordinates are unchanged. This leaf
uses the existing collective value semantics and dim-0 3D gather theorem; it
introduces no source-kernel or compiler claim. -/

namespace TrainVerify.Denote.ZigzagCollective

/-- Closed form of the existing single-sequence row map (also valid at K = 1). -/
theorem zigzagPos_single_eq (K d rank token : Nat)
    (hK : 0 < K) (htoken : token < 2 * d) :
    zigzagPos [0, K * (2 * d)] K rank token =
      if token < d then rank * d + token
      else (2 * K - rank - 1) * d + (token - d) := by
  have hslice : K * (2 * d) / (2 * K) = d := by
    rw [show K * (2 * d) = d * (2 * K) by ring]
    exact Nat.mul_div_cancel d (by omega)
  simp only [zigzagPos, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, zigzagPosAux, sliceSizeAt,
    List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add,
    Nat.sub_zero, hslice, htoken, if_pos]

/-- Every valid local row maps to a valid full-tensor row. -/
theorem zigzagPos_single_lt (K d rank token : Nat)
    (hK : 0 < K) (hd : 0 < d) (hrank : rank < K)
    (htoken : token < 2 * d) :
    zigzagPos [0, K * (2 * d)] K rank token < K * (2 * d) := by
  rw [zigzagPos_single_eq K d rank token hK htoken]
  by_cases hfront : token < d
  · rw [if_pos hfront]
    calc
      rank * d + token < (rank + 1) * d := by nlinarith
      _ ≤ (2 * K) * d := Nat.mul_le_mul_right d (by omega)
      _ = K * (2 * d) := by ring
  · rw [if_neg hfront]
    have hrem : token - d < d := by omega
    have hblock : 2 * K - rank - 1 + 1 ≤ 2 * K := by omega
    calc
      (2 * K - rank - 1) * d + (token - d)
          < (2 * K - rank - 1 + 1) * d := by nlinarith
      _ ≤ (2 * K) * d := Nat.mul_le_mul_right d hblock
      _ = K * (2 * d) := by ring

end TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.RelationCompiler

open ZigzagCollective

private theorem row_index_lt (rows heads dim token head channel : Nat)
    (htoken : token < rows) (hhead : head < heads) (hchannel : channel < dim) :
    (token * heads + head) * dim + channel < prodShape [rows, heads, dim] := by
  have hf : head * dim + channel < heads * dim := by
    calc
      head * dim + channel < (head + 1) * dim := by nlinarith
      _ ≤ heads * dim := Nat.mul_le_mul_right dim hhead
  have hi : token * (heads * dim) + (head * dim + channel) < rows * (heads * dim) := by
    calc
      token * (heads * dim) + (head * dim + channel)
          < (token + 1) * (heads * dim) := by nlinarith
      _ ≤ rows * (heads * dim) := Nat.mul_le_mul_right (heads * dim) htoken
  simp only [prodShape, List.foldl, Nat.one_mul]
  nlinarith [hi]

-- Export both shapes and all three index bounds alongside the actual value.
set_option maxHeartbeats 500000 in
/-- A valid physical row of the actual outputs is the full logical zigzag row,
with exactly the same head/channel. All bounds are on actual tensor shapes. -/
theorem ZigzagKRel.full_row_spec
    {full cu : Tensor} {qs : List Tensor} {K d heads dim : Nat}
    (hq : ZigzagKRel full qs cu [K * (2 * d), heads, dim] [2 * d, heads, dim])
    (hqs : qs.length = K)
    (hdecode : decodeCuSeqlens cu = [0, K * (2 * d)])
    (hK : 1 < K) (hd : 0 < d) (hheads : 0 < heads) (hdim : 0 < dim)
    (rank token head channel : Nat)
    (hrank : rank < K) (htoken : token < 2 * d)
    (hhead : head < heads) (hchannel : channel < dim) :
    (qs.getD rank (zeroTensor [])).shape = [2 * d, heads, dim] ∧
    full.shape = [K * (2 * d), heads, dim] ∧
    zigzagPos (decodeCuSeqlens cu) K rank token < K * (2 * d) ∧
    (token * heads + head) * dim + channel <
      prodShape (qs.getD rank (zeroTensor [])).shape ∧
    (zigzagPos (decodeCuSeqlens cu) K rank token * heads + head) * dim + channel <
      prodShape full.shape ∧
    valAt (qs.getD rank (zeroTensor [])) ((token * heads + head) * dim + channel) =
      valAt full
        ((zigzagPos (decodeCuSeqlens cu) K rank token * heads + head) * dim + channel) := by
  obtain ⟨xs, hs, hlen, _hcu, hout⟩ := hq
  rw [hqs] at hlen hout
  have hshape (r : Nat) (hr : r < K) (fallback : Tensor) :
      (xs.getD r fallback).shape = [2 * d, heads, dim] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hs.shard_shapes _ (List.getElem_mem ..)
  have hdefault (r : Nat) (hr : r < K) :
      xs.getD r (zeroTensor [2 * d, heads, dim]) = xs.getD r (zeroTensor []) := by
    unfold List.getD
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  have hselect : qs.getD rank (zeroTensor []) =
      fw_maybe_shuffle_collective xs (decodeCuSeqlens cu) K rank := by
    rw [hout]
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa only [List.length_range] using hrank)]
    simp only [List.getElem_range, Option.map_some, Option.getD_some]
  have hqshape : (qs.getD rank (zeroTensor [])).shape = [2 * d, heads, dim] := by
    rw [hselect, fw_maybe_shuffle_collective_shape]
    exact hshape rank hrank _
  have hg : zigzagPos (decodeCuSeqlens cu) K rank token < K * (2 * d) := by
    rw [hdecode]
    exact zigzagPos_single_lt K d rank token (by omega) hd hrank htoken
  have hlocal := row_index_lt (2 * d) heads dim token head channel htoken hhead hchannel
  have hglobal := row_index_lt (K * (2 * d)) heads dim
    (zigzagPos (decodeCuSeqlens cu) K rank token) head channel hg hhead hchannel
  refine ⟨hqshape, hs.full_shape, hg, ?_, ?_, ?_⟩
  · rw [hqshape]
    exact hlocal
  · rw [hs.full_shape]
    exact hglobal
  · have hstride : 0 < heads * dim := Nat.mul_pos hheads hdim
    have hf : head * dim + channel < heads * dim := by
      calc
        head * dim + channel < (head + 1) * dim := by nlinarith
        _ ≤ heads * dim := Nat.mul_le_mul_right dim hhead
    have hflat : (token * heads + head) * dim + channel =
        (head * dim + channel) + (heads * dim) * token := by ring
    have hdiv : ((token * heads + head) * dim + channel) / (heads * dim) = token := by
      rw [hflat, Nat.add_mul_div_left _ _ hstride, Nat.div_eq_of_lt hf, Nat.zero_add]
    have hmod : ((token * heads + head) * dim + channel) % (heads * dim) =
        head * dim + channel := by
      rw [hflat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]
    rw [hselect, fw_maybe_shuffle_collective_valAt xs (decodeCuSeqlens cu) K rank
      ((token * heads + head) * dim + channel) (by omega)
      (by rw [hshape rank hrank]; exact hlocal)]
    simp only [hshape rank hrank, List.tail_cons, List.getD_cons_zero,
      prodShape, List.foldl, Nat.one_mul]
    rw [hdiv, hmod]
    let g := zigzagPos (decodeCuSeqlens cu) K rank token
    have hsrc : g / (2 * d) < K := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * d)).mpr
      exact hg
    have hoff : g % (2 * d) < 2 * d := Nat.mod_lt g (by omega)
    have hheadshape : (xs.head?.map (fun t => t.shape)).getD [] = [2 * d, heads, dim] := by
      cases xs with
      | nil => exact False.elim (hs.shards_nonempty rfl)
      | cons x rest =>
        change x.shape = [2 * d, heads, dim]
        exact hs.shard_shapes x (List.mem_cons_self ..)
    have hfull : full = allGatherPrimDimN 0 K 0 xs := by
      have hv := hs.full_value
      rw [hlen] at hv
      exact hv
    have hval := allGatherPrimDimN0_valAt_3D K (2 * d) heads dim xs
      (by omega) (by omega) hheads hdim hheadshape
      (fun r hr => hshape r hr _) (g / (2 * d)) hsrc (g % (2 * d)) hoff
      head hhead channel hchannel
    have hdecomp : g / (2 * d) * (2 * d) + g % (2 * d) = g := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod g (2 * d)
    rw [hdecomp, hdefault _ hsrc, ← hfull] at hval
    change gatherFromRank xs (2 * d) (heads * dim) g (head * dim + channel) =
      valAt full ((g * heads + head) * dim + channel)
    dsimp only [gatherFromRank]
    rw [show g % (2 * d) * (heads * dim) + (head * dim + channel) =
      (g % (2 * d) * heads + head) * dim + channel by ring]
    exact hval.symm

/-- Convenient value-only projection of `full_row_spec`. -/
theorem ZigzagKRel.full_row_value
    {full cu : Tensor} {qs : List Tensor} {K d heads dim : Nat}
    (hq : ZigzagKRel full qs cu [K * (2 * d), heads, dim] [2 * d, heads, dim])
    (hqs : qs.length = K)
    (hdecode : decodeCuSeqlens cu = [0, K * (2 * d)])
    (hK : 1 < K) (hd : 0 < d) (hheads : 0 < heads) (hdim : 0 < dim)
    (rank token head channel : Nat)
    (hrank : rank < K) (htoken : token < 2 * d)
    (hhead : head < heads) (hchannel : channel < dim) :
    valAt (qs.getD rank (zeroTensor [])) ((token * heads + head) * dim + channel) =
      valAt full
        ((zigzagPos (decodeCuSeqlens cu) K rank token * heads + head) * dim + channel) :=
  (hq.full_row_spec hqs hdecode hK hd hheads hdim rank token head channel
    hrank htoken hhead hchannel).2.2.2.2.2

end TrainVerify.Denote.RelationCompiler
