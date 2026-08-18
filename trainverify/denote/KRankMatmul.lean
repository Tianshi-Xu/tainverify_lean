import denote.RelationCompiler

namespace TrainVerify.Denote

open scoped BigOperators

set_option maxHeartbeats 500000

/-- A canonical read through a last-axis gather of rank-4 shards. -/
theorem allGatherPrimDimN_dim3_4d_valAt
    (ys : List Tensor) (K b h n ms pre r j : Nat)
    (hK : 0 < K) (hms : 0 < ms)
    (hpre : pre < b * h * n) (hr : r < K) (hj : j < ms)
    (hhead : (ys.head?.map (fun t => t.shape)).getD [] = [b, h, n, ms]) :
    valAt (allGatherPrimDimN 3 K 0 ys) (pre * (ms * K) + (r * ms + j)) =
      valAt (ys.getD r (zeroTensor [b, h, n, ms])) (pre * ms + j) := by
  have hmsK : 0 < ms * K := Nat.mul_pos hms hK
  have hlocal : r * ms + j < ms * K := by
    have hstep : r * ms + j < (r + 1) * ms := by
      rw [Nat.add_mul]
      omega
    have hr1 : r + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right ms hr1
    rw [Nat.mul_comm K ms] at hmul
    exact lt_of_lt_of_le hstep hmul
  have hidx : pre * (ms * K) + (r * ms + j) < (b * h * n) * (ms * K) := by
    have hstep : pre * (ms * K) + (r * ms + j) < (pre + 1) * (ms * K) := by
      rw [Nat.add_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (ms * K) hpre)
  have hgshape : (allGatherPrimDimN 3 K 0 ys).shape = [b, h, n, ms * K] := by
    rw [allGatherPrimDimN_shape 3 K ys [b, h, n, ms] hhead]
    simp [List.set, List.getD]
  have hprod : pre * (ms * K) + (r * ms + j) <
      prodShape (allGatherPrimDimN 3 K 0 ys).shape := by
    rw [hgshape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.mul_one, Nat.one_ne_zero, if_false,
    if_neg (Nat.ne_of_gt hmsK), if_neg (Nat.ne_of_gt hms)]
  have hpreDiv : (pre * (ms * K) + (r * ms + j)) / (ms * K) = pre := by
    rw [show pre * (ms * K) + (r * ms + j) =
        (r * ms + j) + (ms * K) * pre by ring,
      Nat.add_mul_div_left _ _ hmsK, Nat.div_eq_of_lt hlocal, Nat.zero_add]
  have hrem : (pre * (ms * K) + (r * ms + j)) % (ms * K) = r * ms + j := by
    rw [show pre * (ms * K) + (r * ms + j) =
        (r * ms + j) + (ms * K) * pre by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlocal]
  have hrank : (r * ms + j) / ms = r := by
    rw [show r * ms + j = j + ms * r by ring,
      Nat.add_mul_div_left _ _ hms, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hjlocal : (r * ms + j) % ms = j := by
    rw [show r * ms + j = j + ms * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [hpreDiv, hrem]
  simp only [Nat.div_one, Nat.mod_one, Nat.add_zero]
  rw [hrank, hjlocal]

/-- Rank-4 batched matmul has the symbolic output shape `[b,h,q,m]`. -/
theorem fw_matmul_rank4_shape
    (x y : Tensor) (b h q k m : Nat)
    (hx : x.shape = [b, h, q, k]) (hy : y.shape = [b, h, k, m]) :
    (fw_matmul x y).shape = [b, h, q, m] := by
  unfold fw_matmul batchedMatmul
  rw [hx, hy]
  rfl

/-- Canonical rank-4 batched-matmul value formula. -/
theorem fw_matmul_rank4_valAt
    (x y : Tensor) (b h q k m outer i j : Nat)
    (hm : 0 < m) (houter : outer < b * h) (hi : i < q) (hj : j < m)
    (hx : x.shape = [b, h, q, k]) (hy : y.shape = [b, h, k, m]) :
    valAt (fw_matmul x y) ((outer * q + i) * m + j) =
      ∑ l ∈ Finset.range k,
        valAt x ((outer * q + i) * k + l) *
        valAt y ((outer * k + l) * m + j) := by
  have hrow : outer * q + i < (b * h) * q := by
    have hstep : outer * q + i < (outer + 1) * q := by
      calc
        outer * q + i < outer * q + q := Nat.add_lt_add_left hi _
        _ = (outer + 1) * q := by ring
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right q houter)
  have hidx : (outer * q + i) * m + j < (b * h * q) * m := by
    have hstep : (outer * q + i) * m + j < (outer * q + i + 1) * m := by
      calc
        (outer * q + i) * m + j < (outer * q + i) * m + m :=
          Nat.add_lt_add_left hj _
        _ = (outer * q + i + 1) * m := by ring
    have hrow1 : outer * q + i + 1 ≤ (b * h) * q := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right m hrow1)
  rw [show fw_matmul x y = batchedMatmul x y from rfl]
  unfold batchedMatmul
  simp only [hx, hy, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  rw [valAt_of_lt]
  · simp only [Tensor.mkShape]
    have hm0 : m ≠ 0 := Nat.ne_of_gt hm
    have hq0 : q ≠ 0 := by omega
    have hinner : q * m ≠ 0 := Nat.mul_ne_zero hq0 hm0
    simp only [hinner, hm0, if_false]
    have houterDiv : ((outer * q + i) * m + j) / (q * m) = outer := by
      have hlow : i * m + j < q * m := by
        have hstep : i * m + j < (i + 1) * m := by rw [Nat.add_mul]; omega
        exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right m hi)
      rw [show (outer * q + i) * m + j = (i * m + j) + (q * m) * outer by ring,
        Nat.add_mul_div_left _ _ (Nat.mul_pos (by omega) hm), Nat.div_eq_of_lt hlow,
        Nat.zero_add]
    have houterRem : ((outer * q + i) * m + j) % (q * m) = i * m + j := by
      have hlow : i * m + j < q * m := by
        have hstep : i * m + j < (i + 1) * m := by rw [Nat.add_mul]; omega
        exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right m hi)
      rw [show (outer * q + i) * m + j = (i * m + j) + (q * m) * outer by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
    have hiDiv : (i * m + j) / m = i := by
      rw [show i * m + j = j + m * i by ring,
        Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hjRem : (i * m + j) % m = j := by
      rw [show i * m + j = j + m * i by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [houterDiv, houterRem, hiDiv, hjRem]
    apply Finset.sum_congr rfl
    intro l hl
    congr 2 <;> ring
  · simpa [Tensor.mkShape, prodShape, Nat.mul_assoc] using hidx

/-- For any positive ordered rank count `K`, gathering the output columns of
rank-4 right operands commutes with `fw_matmul`. -/
theorem fw_matmul_allGatherPrimDimN_dim3_K_rank4
    (x : Tensor) (ys : List Tensor) (K b h q k ms : Nat)
    (hK : 0 < K) (hq : 0 < q) (hms : 0 < ms)
    (hlen : ys.length = K)
    (hx : x.shape = [b, h, q, k])
    (hy : ∀ y ∈ ys, y.shape = [b, h, k, ms]) :
    fw_matmul x (allGatherPrimDimN 3 K 0 ys) =
      allGatherPrimDimN 3 K 0 (ys.map (fw_matmul x)) := by
  have hne : ys ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨y0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hy0 : y0.shape = [b, h, k, ms] := hy y0 (by simp)
  have hhead : (((y0 :: rest).head?.map (fun t => t.shape)).getD []) = [b, h, k, ms] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hy0
  have hYshape : (allGatherPrimDimN 3 K 0 (y0 :: rest)).shape = [b, h, k, ms * K] := by
    rw [allGatherPrimDimN_shape 3 K _ [b, h, k, ms] hhead]
    simp [List.set, List.getD]
  have hmapHead : ((((y0 :: rest).map (fw_matmul x)).head?.map
      (fun t => t.shape)).getD []) = [b, h, q, ms] := by
    simp only [List.map, List.head?, Option.map, Option.getD]
    exact fw_matmul_rank4_shape x y0 b h q k ms hx hy0
  have hLshape : (fw_matmul x (allGatherPrimDimN 3 K 0 (y0 :: rest))).shape =
      [b, h, q, ms * K] := fw_matmul_rank4_shape _ _ b h q k (ms * K) hx hYshape
  have hRshape : (allGatherPrimDimN 3 K 0 ((y0 :: rest).map (fw_matmul x))).shape =
      [b, h, q, ms * K] := by
    rw [allGatherPrimDimN_shape 3 K _ [b, h, q, ms] hmapHead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hbound : idx < (b * h * q) * (ms * K) := by
      simpa [prodShape, Nat.mul_assoc] using hidx
    have hmK : 0 < ms * K := Nat.mul_pos hms hK
    set col := idx % (ms * K) with hcolDef
    set row := idx / (ms * K) with hrowDef
    set outer := row / q with houterDef
    set i := row % q with hiDef
    set r := col / ms with hrDef
    set j := col % ms with hjDef
    have hcol : col < ms * K := by rw [hcolDef]; exact Nat.mod_lt _ hmK
    have hrow : row < b * h * q := by
      rw [hrowDef, Nat.div_lt_iff_lt_mul hmK]
      exact hbound
    have houter : outer < b * h := by
      rw [houterDef, Nat.div_lt_iff_lt_mul hq]
      exact hrow
    have hi : i < q := by rw [hiDef]; exact Nat.mod_lt _ hq
    have hr : r < K := by
      rw [hrDef, Nat.div_lt_iff_lt_mul hms]
      simpa [Nat.mul_comm] using hcol
    have hj : j < ms := by rw [hjDef]; exact Nat.mod_lt _ hms
    have hrowEq : outer * q + i = row := by
      simpa [houterDef, hiDef, Nat.mul_comm] using Nat.div_add_mod row q
    have hcolEq : r * ms + j = col := by
      simpa [hrDef, hjDef, Nat.mul_comm] using Nat.div_add_mod col ms
    have hidxEq : idx = (outer * q + i) * (ms * K) + (r * ms + j) := by
      calc
        idx = row * (ms * K) + col := by
          simpa [row, col, Nat.mul_comm] using (Nat.div_add_mod idx (ms * K)).symm
        _ = _ := by rw [hrowEq, hcolEq]
    have hrlen : r < (y0 :: rest).length := by omega
    have hyr : ((y0 :: rest)[r]).shape = [b, h, k, ms] :=
      hy _ (List.getElem_mem hrlen)
    have hmapGetD : ((y0 :: rest).map (fw_matmul x)).getD r
        (zeroTensor [b, h, q, ms]) = fw_matmul x ((y0 :: rest)[r]) := by
      rw [List.getD]
      rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hrlen)]
      simp only [Option.getD_some, List.getElem_map]
    rw [hidxEq]
    rw [fw_matmul_rank4_valAt x (allGatherPrimDimN 3 K 0 (y0 :: rest))
      b h q k (ms * K) outer i (r * ms + j) hmK houter hi
        (by rw [hcolEq]; exact hcol) hx hYshape]
    rw [allGatherPrimDimN_dim3_4d_valAt ((y0 :: rest).map (fw_matmul x))
      K b h q ms (outer * q + i) r j hK hms
        (by rw [hrowEq]; exact hrow) hr hj hmapHead]
    rw [hmapGetD]
    rw [fw_matmul_rank4_valAt x ((y0 :: rest)[r])
      b h q k ms outer i j hms houter hi hj hx hyr]
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l < k := Finset.mem_range.mp hl
    rw [allGatherPrimDimN_dim3_4d_valAt (y0 :: rest)
      K b h k ms (outer * k + l) r j hK hms]
    · rw [List.getD, List.getElem?_eq_getElem hrlen, Option.getD_some]
    · have houtk : outer * k + l < (b * h) * k := by
        have hstep : outer * k + l < (outer + 1) * k := by rw [Nat.add_mul]; omega
        exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right k houter)
      simpa [Nat.mul_assoc] using houtk
    · exact hr
    · exact hj
    · exact hhead

end TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

/-- `ShardedRel` transport for rank-4 output-axis matmul. -/
theorem ShardedRel.fw_matmul_output_axis_rank4
    {x y : Tensor} {ys : List Tensor} {K b h q k ms : Nat}
    (hrel : ShardedRel y ys 3 [b, h, k, ms * K] [b, h, k, ms])
    (hK : 0 < K) (hq : 0 < q) (hms : 0 < ms)
    (hlen : ys.length = K)
    (hx : x.shape = [b, h, q, k]) :
    ShardedRel (fw_matmul x y) (ys.map (fw_matmul x)) 3
      [b, h, q, ms * K] [b, h, q, ms] := by
  have hy : ∀ z ∈ ys, z.shape = [b, h, k, ms] := hrel.shard_shapes
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := ?_
    gather_dim_lt := by simp
    shard_shapes := ?_
    shape_contract := ?_
  }
  · rw [hrel.full_value, List.length_map, hlen]
    exact TrainVerify.Denote.fw_matmul_allGatherPrimDimN_dim3_K_rank4
      x ys K b h q k ms hK hq hms hlen hx hy
  · exact TrainVerify.Denote.fw_matmul_rank4_shape x y b h q k (ms * K) hx hrel.full_shape
  · intro hnil
    have hmLen : (ys.map (fw_matmul x)).length = 0 := by rw [hnil]; rfl
    rw [List.length_map, hlen] at hmLen
    omega
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact TrainVerify.Denote.fw_matmul_rank4_shape x w b h q k ms hx (hy w hw)
  · simp [List.set, List.getD, hlen]

end TrainVerify.Denote.RelationCompiler

#print axioms TrainVerify.Denote.fw_matmul_allGatherPrimDimN_dim3_K_rank4
#print axioms TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_output_axis_rank4
