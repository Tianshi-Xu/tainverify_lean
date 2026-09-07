import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section

-- Generic leaf candidates; direct kernel checking is delegated to the parent.
private theorem sequence_transpose_shape (w : Tensor) (o i : Nat)
    (hw : w.shape = [o, i]) : (transpose2d w).shape = [i, o] := by
  simp only [transpose2d, hw, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, Tensor.mkShape]

private theorem sequence_transpose_valAt (w : Tensor) (o i c j : Nat)
    (ho : 0 < o) (hw : w.shape = [o, i]) (hc : c < i) (hj : j < o) :
    valAt (transpose2d w) (c * o + j) = valAt w (j * i + c) := by
  have hidx : c * o + j < i * o := by
    calc
      _ < c * o + o := Nat.add_lt_add_left hj _
      _ = (c + 1) * o := by ring
      _ ≤ i * o := Nat.mul_le_mul_right o hc
  have hio : 0 < o * i := Nat.mul_pos ho (by omega)
  have hdiv : (c * o + j) / o = c := by
    rw [show c * o + j = j + o * c by ring, Nat.add_mul_div_left _ _ ho,
      Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (c * o + j) % o = j := by
    rw [show c * o + j = j + o * c by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hbound : c * o + j < o * i := by
    simpa only [Nat.mul_comm i o] using hidx
  unfold transpose2d
  simp only [hw, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape, prodShape] using hidx)]
  simp only [Tensor.mkShape, if_neg hio.ne', if_neg ho.ne',
    Nat.div_eq_of_lt hbound,
    Nat.mod_eq_of_lt hbound, hdiv, hmod,
    Nat.zero_mul, Nat.zero_add]

/-- Under the exact rank-3 shape contract, dX is linear in g with transposed w.
The activation contributes its shape, never its values. -/
theorem bw_linear_fst_eq_fw_linear_transpose_rank3
    (g x w : Tensor) (b s o i : Nat) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hg : g.shape = [b, s, o]) (hx : x.shape = [b, s, i]) (hw : w.shape = [o, i]) :
    (bw_linear g x w).1 = fw_linear g (transpose2d w) := by
  have hwt := sequence_transpose_shape w o i hw
  have hshape := bw_linear_3d_fst_shape b s o i g x w hg hx hw
  have hshapeR := fw_linear_3d_shape b s o i g (transpose2d w) hg hwt
  apply Tensor.ext (by rw [hshape, hshapeR])
  intro idx hidx
  have hidxR : idx < prodShape (fw_linear g (transpose2d w)).shape := by
    rw [hshapeR, ← hshape]; exact hidx
  unfold bw_linear fw_linear
  simp only [hg, hx, hw, hwt]
  rw [valAt_of_lt _ _ (by simpa only [hshape, Tensor.mkShape] using hidx),
    valAt_of_lt _ _ (by simpa only [hshapeR, Tensor.mkShape] using hidxR)]
  simp only [Tensor.mkShape]
  have hsi : 0 < s * i := Nat.mul_pos hs hi
  simp only [if_neg hsi.ne', if_neg hi.ne']
  apply Finset.sum_congr rfl
  intro j hj
  rw [sequence_transpose_valAt w o i ((idx % (s * i)) % i) j ho hw
    (Nat.mod_lt _ hi) (Finset.mem_range.mp hj)]

/-- Sequence sharding of dX, arbitrary positive rank count and dimensions.
Ordered pairs of gradient/activation shards share exactly one weight. -/
theorem bw_linear_dx_sequence_allGather_rank3
    (K b s o i : Nat) (gs xs : List Tensor) (x w : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, s, o])
    (hxs : ∀ a ∈ xs, a.shape = [b, s, i])
    (hx : x.shape = [b, s * K, i]) (hw : w.shape = [o, i]) :
    (bw_linear (allGatherPrimDimN 1 K 0 gs) x w).1 =
      allGatherPrimDimN 1 K 0 (List.zipWith (fun g a => (bw_linear g a w).1) gs xs) := by
  have hhead : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, o] := by
    cases gs with
    | nil => simp at hglen; omega
    | cons g rest => exact hgs g (List.mem_cons_self ..)
  have hg : (allGatherPrimDimN 1 K 0 gs).shape = [b, s * K, o] := by
    rw [allGatherPrimDimN_shape 1 K gs [b, s, o] hhead]
    simp [List.set, List.getD]
  rw [bw_linear_fst_eq_fw_linear_transpose_rank3 _ x w b (s * K) o i
    (Nat.mul_pos hs hK) ho hi hg hx hw]
  rw [fw_linear_3d_allGatherPrimDimN_dim1_comm K b s o i gs (transpose2d w)
    hK hb hs ho hi hglen hgs (sequence_transpose_shape w o i hw)]
  congr 1
  have hlen : gs.length = xs.length := hglen.trans hxlen.symm
  clear hglen hxlen hg hhead hx
  induction gs generalizing xs with
  | nil => cases xs <;> simp_all
  | cons g rest ih =>
    cases xs with
    | nil => simp at hlen
    | cons a tail =>
      simp only [List.map, List.zipWith]
      congr 1
      · exact (bw_linear_fst_eq_fw_linear_transpose_rank3 g a w b s o i hs ho hi
          (hgs g (List.mem_cons_self ..)) (hxs a (List.mem_cons_self ..)) hw).symm
      · exact ih tail (fun t ht => hgs t (List.mem_cons_of_mem _ ht))
          (fun t ht => hxs t (List.mem_cons_of_mem _ ht)) (by simpa using hlen)

end
end TrainVerify.Denote
