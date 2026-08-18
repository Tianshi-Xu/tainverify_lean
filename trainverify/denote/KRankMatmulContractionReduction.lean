import denote.KRankMatmul

namespace TrainVerify.Denote

open scoped BigOperators

set_option maxHeartbeats 500000

/-- A canonical read through a dim-2 gather of rank-4 shards. -/
theorem allGatherPrimDimN_dim2_4d_valAt
    (ys : List Tensor) (K b h k m outer r l j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hm : 0 < m)
    (houter : outer < b * h) (hr : r < K) (hl : l < k) (hj : j < m)
    (hhead : (ys.head?.map (fun t => t.shape)).getD [] = [b, h, k, m]) :
    valAt (allGatherPrimDimN 2 K 0 ys)
        ((outer * (k * K) + (r * k + l)) * m + j) =
      valAt (ys.getD r (zeroTensor [b, h, k, m]))
        ((outer * k + l) * m + j) := by
  have hkK : 0 < k * K := Nat.mul_pos hk hK
  have hlocal : r * k + l < k * K := by
    have hstep : r * k + l < (r + 1) * k := by
      rw [Nat.add_mul]
      omega
    have hr1 : r + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right k hr1
    rw [Nat.mul_comm K k] at hmul
    exact lt_of_lt_of_le hstep hmul
  have hpre : outer * (k * K) + (r * k + l) < (b * h) * (k * K) := by
    have hstep : outer * (k * K) + (r * k + l) < (outer + 1) * (k * K) := by
      rw [Nat.add_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (k * K) houter)
  have hidx : (outer * (k * K) + (r * k + l)) * m + j <
      ((b * h) * (k * K)) * m := by
    have hstep : (outer * (k * K) + (r * k + l)) * m + j <
        (outer * (k * K) + (r * k + l) + 1) * m := by
      calc
        _ < (outer * (k * K) + (r * k + l)) * m + m :=
          Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hrow1 : outer * (k * K) + (r * k + l) + 1 ≤
        (b * h) * (k * K) := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right m hrow1)
  have hgshape : (allGatherPrimDimN 2 K 0 ys).shape = [b, h, k * K, m] := by
    rw [allGatherPrimDimN_shape 2 K ys [b, h, k, m] hhead]
    simp [List.set, List.getD]
  have hprod : (outer * (k * K) + (r * k + l)) * m + j <
      prodShape (allGatherPrimDimN 2 K 0 ys).shape := by
    rw [hgshape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.one_mul]
  have hkm : 0 < (k * K) * m := Nat.mul_pos hkK hm
  have hlocalm : (r * k + l) * m + j < (k * K) * m := by
    have hstep : (r * k + l) * m + j < (r * k + l + 1) * m := by
      calc
        _ < (r * k + l) * m + m := Nat.add_lt_add_left hj _
        _ = _ := by ring
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right m (by omega))
  have hpreDiv : ((outer * (k * K) + (r * k + l)) * m + j) /
      ((k * K) * m) = outer := by
    rw [show (outer * (k * K) + (r * k + l)) * m + j =
        ((r * k + l) * m + j) + ((k * K) * m) * outer by ring,
      Nat.add_mul_div_left _ _ hkm, Nat.div_eq_of_lt hlocalm, Nat.zero_add]
  have hpreRem : ((outer * (k * K) + (r * k + l)) * m + j) %
      ((k * K) * m) = (r * k + l) * m + j := by
    rw [show (outer * (k * K) + (r * k + l)) * m + j =
        ((r * k + l) * m + j) + ((k * K) * m) * outer by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlocalm]
  have hjFullDiv : ((r * k + l) * m + j) / m = r * k + l := by
    rw [show (r * k + l) * m + j = j + m * (r * k + l) by ring,
      Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hjRem : ((r * k + l) * m + j) % m = j := by
    rw [show (r * k + l) * m + j = j + m * (r * k + l) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hrank : (r * k + l) / k = r := by
    rw [show r * k + l = l + k * r by ring,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hl, Nat.zero_add]
  have hlocalRem : (r * k + l) % k = l := by
    rw [show r * k + l = l + k * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  simp only [if_neg (Nat.ne_of_gt hkm), if_neg (Nat.ne_of_gt hm),
    if_neg (Nat.ne_of_gt hk)]
  rw [hpreDiv, hpreRem, hjFullDiv, hjRem, hrank, hlocalRem]
  congr 1 <;> ring

/-- Dynamic-rank contraction-axis decomposition for symbolic rank-4 matmul. -/
theorem fw_matmul_allGather_contraction_eq_allReduce_zipWith_rank4
    (xs ys : List Tensor) (K b h q k m : Nat)
    (hK : 0 < K) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hxslen : xs.length = K) (hyslen : ys.length = K)
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, k])
    (hys : ∀ y ∈ ys, y.shape = [b, h, k, m]) :
    fw_matmul (allGatherPrimDimN 3 K 0 xs) (allGatherPrimDimN 2 K 0 ys) =
      allReducePrim K 0 (List.zipWith fw_matmul xs ys) := by
  classical
  have hxsne : xs ≠ [] := by
    intro he
    rw [he] at hxslen
    simp only [List.length_nil] at hxslen
    omega
  have hysne : ys ≠ [] := by
    intro he
    rw [he] at hyslen
    simp only [List.length_nil] at hyslen
    omega
  obtain ⟨x0, xrest, rfl⟩ := List.exists_cons_of_ne_nil hxsne
  obtain ⟨y0, yrest, rfl⟩ := List.exists_cons_of_ne_nil hysne
  have hx0 : x0.shape = [b, h, q, k] := hxs x0 (by simp)
  have hy0 : y0.shape = [b, h, k, m] := hys y0 (by simp)
  have hxhead : (((x0 :: xrest).head?.map (fun t => t.shape)).getD []) =
      [b, h, q, k] := by simp only [List.head?, Option.map, Option.getD]; exact hx0
  have hyhead : (((y0 :: yrest).head?.map (fun t => t.shape)).getD []) =
      [b, h, k, m] := by simp only [List.head?, Option.map, Option.getD]; exact hy0
  have hXshape : (allGatherPrimDimN 3 K 0 (x0 :: xrest)).shape =
      [b, h, q, k * K] := by
    rw [allGatherPrimDimN_shape 3 K _ [b, h, q, k] hxhead]
    simp [List.set, List.getD]
  have hYshape : (allGatherPrimDimN 2 K 0 (y0 :: yrest)).shape =
      [b, h, k * K, m] := by
    rw [allGatherPrimDimN_shape 2 K _ [b, h, k, m] hyhead]
    simp [List.set, List.getD]
  have hLshape : (fw_matmul (allGatherPrimDimN 3 K 0 (x0 :: xrest))
      (allGatherPrimDimN 2 K 0 (y0 :: yrest))).shape = [b, h, q, m] :=
    fw_matmul_rank4_shape _ _ b h q (k * K) m hXshape hYshape
  have hP0shape : (fw_matmul x0 y0).shape = [b, h, q, m] :=
    fw_matmul_rank4_shape x0 y0 b h q k m hx0 hy0
  have hRhead : (List.zipWith fw_matmul (x0 :: xrest) (y0 :: yrest)).head? =
      some (fw_matmul x0 y0) := rfl
  have hRshape : (allReducePrim K 0
      (List.zipWith fw_matmul (x0 :: xrest) (y0 :: yrest))).shape = [b, h, q, m] := by
    rw [allReducePrim_shape K 0 _ _ hRhead]
    exact hP0shape
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hbound : idx < (b * h * q) * m := by
      simpa [prodShape, Nat.mul_assoc] using hidx
    set j := idx % m with hjDef
    set row := idx / m with hrowDef
    set i := row % q with hiDef
    set outer := row / q with houterDef
    have hj : j < m := by rw [hjDef]; exact Nat.mod_lt _ hm
    have hrow : row < b * h * q := by
      rw [hrowDef, Nat.div_lt_iff_lt_mul hm]
      exact hbound
    have hi : i < q := by rw [hiDef]; exact Nat.mod_lt _ hq
    have houter : outer < b * h := by
      rw [houterDef, Nat.div_lt_iff_lt_mul hq]
      exact hrow
    have hrowEq : outer * q + i = row := by
      simpa [houterDef, hiDef, Nat.mul_comm] using Nat.div_add_mod row q
    have hidxEq : idx = (outer * q + i) * m + j := by
      calc
        idx = row * m + j := by
          simpa [hrowDef, hjDef, Nat.mul_comm] using (Nat.div_add_mod idx m).symm
        _ = _ := by rw [hrowEq]
    rw [hidxEq]
    rw [fw_matmul_rank4_valAt _ _ b h q (k * K) m outer i j hm houter hi hj
      hXshape hYshape]
    rw [show k * K = K * k by ring]
    rw [Finset.sum_range_mul_eq_sum_sum]
    rw [Nat.mul_comm K k]
    have hlocal : ∀ r, r < K → ∀ l, l < k →
        valAt (allGatherPrimDimN 3 K 0 (x0 :: xrest))
            ((outer * q + i) * (k * K) + (r * k + l)) *
          valAt (allGatherPrimDimN 2 K 0 (y0 :: yrest))
            ((outer * (k * K) + (r * k + l)) * m + j) =
        valAt ((x0 :: xrest).getD r (zeroTensor [b, h, q, k]))
            ((outer * q + i) * k + l) *
          valAt ((y0 :: yrest).getD r (zeroTensor [b, h, k, m]))
            ((outer * k + l) * m + j) := by
      intro r hr l hl
      rw [allGatherPrimDimN_dim3_4d_valAt (x0 :: xrest) K b h q k
        (outer * q + i) r l hK hk (by rw [hrowEq]; simpa [Nat.mul_assoc] using hrow) hr hl hxhead]
      rw [allGatherPrimDimN_dim2_4d_valAt (y0 :: yrest) K b h k m outer r l j
        hK hk hm houter hr hl hj hyhead]
    have hsplit : (∑ r ∈ Finset.range K, ∑ l ∈ Finset.range k,
        valAt (allGatherPrimDimN 3 K 0 (x0 :: xrest))
            ((outer * q + i) * (k * K) + (r * k + l)) *
          valAt (allGatherPrimDimN 2 K 0 (y0 :: yrest))
            ((outer * (k * K) + (r * k + l)) * m + j)) =
        ∑ r ∈ Finset.range K, ∑ l ∈ Finset.range k,
          valAt ((x0 :: xrest).getD r (zeroTensor [b, h, q, k]))
              ((outer * q + i) * k + l) *
            valAt ((y0 :: yrest).getD r (zeroTensor [b, h, k, m]))
              ((outer * k + l) * m + j) := by
      apply Finset.sum_congr rfl
      intro r hrmem
      apply Finset.sum_congr rfl
      intro l hlmem
      exact hlocal r (Finset.mem_range.mp hrmem) l (Finset.mem_range.mp hlmem)
    rw [hsplit]
    rw [allReducePrim_valAt K 0 _ ((outer * q + i) * m + j)
      (fw_matmul x0 y0) hRhead (by
        rw [hP0shape]
        rw [← hidxEq]
        exact hidx)]
    rw [List.foldl_add_eq_sum]
    rw [← List.ofFn_getElem_eq_map]
    rw [Fin.sum_ofFn]
    have hziplen : (List.zipWith fw_matmul (x0 :: xrest) (y0 :: yrest)).length = K := by
      rw [List.length_zipWith, hxslen, hyslen, min_self]
    rw [← hziplen]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    have hr : (r : Nat) < K := by omega
    have hrx : r < (x0 :: xrest).length := by omega
    have hry : r < (y0 :: yrest).length := by omega
    rw [List.getElem_zipWith]
    rw [fw_matmul_rank4_valAt (x0 :: xrest)[(r : Nat)] (y0 :: yrest)[(r : Nat)]
      b h q k m outer i j hm houter hi hj
      (hxs _ (List.getElem_mem hrx)) (hys _ (List.getElem_mem hry))]
    apply Finset.sum_congr rfl
    intro l hlmem
    rw [List.getD, List.getElem?_eq_getElem hrx, Option.getD_some,
      List.getD, List.getElem?_eq_getElem hry, Option.getD_some]

end TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

/-- Contraction-axis sharding of both rank-4 operands produces the ordered
rank-wise local matmul contributions consumed by `allReducePrim`. -/
theorem ShardedRel.fw_matmul_contraction_axis_rank4
    {x y : Tensor} {xs ys : List Tensor} {K b h q k m : Nat}
    (hxrel : ShardedRel x xs 3 [b, h, q, k * K] [b, h, q, k])
    (hyrel : ShardedRel y ys 2 [b, h, k * K, m] [b, h, k, m])
    (hK : 0 < K) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hxslen : xs.length = K) (hyslen : ys.length = K) :
    ReductionRel (fw_matmul x y) (List.zipWith fw_matmul xs ys) [b, h, q, m] := by
  have hvalue : fw_matmul x y =
      allReducePrim (List.zipWith fw_matmul xs ys).length 0
        (List.zipWith fw_matmul xs ys) := by
    rw [hxrel.full_value, hyrel.full_value, hxslen, hyslen]
    have hziplen : (List.zipWith fw_matmul xs ys).length = K := by
      rw [List.length_zipWith, hxslen, hyslen, min_self]
    rw [hziplen]
    exact fw_matmul_allGather_contraction_eq_allReduce_zipWith_rank4
      xs ys K b h q k m hK hq hk hm hxslen hyslen
      hxrel.shard_shapes hyrel.shard_shapes
  have hfullshape : (fw_matmul x y).shape = [b, h, q, m] :=
    fw_matmul_rank4_shape x y b h q (k * K) m
      hxrel.full_shape hyrel.full_shape
  refine {
    full_value := hvalue
    full_shape := hfullshape
    contributions_nonempty := ?_
    contribution_shapes := ?_
    reduced_shape := ?_
  }
  · intro hnil
    rcases List.zipWith_eq_nil_iff.mp hnil with hxs | hys
    · rw [hxs] at hxslen
      simp only [List.length_nil] at hxslen
      omega
    · rw [hys] at hyslen
      simp only [List.length_nil] at hyslen
      omega
  · intro contribution hmem
    rcases List.mem_iff_getElem.mp hmem with ⟨r, hrzip, hcontribution⟩
    have hrx : r < xs.length := by
      rw [List.length_zipWith, hxslen, hyslen, min_self] at hrzip
      omega
    have hry : r < ys.length := by
      rw [List.length_zipWith, hxslen, hyslen, min_self] at hrzip
      omega
    rw [← hcontribution, List.getElem_zipWith]
    exact fw_matmul_rank4_shape xs[r] ys[r] b h q k m
      (hxrel.shard_shapes xs[r] (List.getElem_mem hrx))
      (hyrel.shard_shapes ys[r] (List.getElem_mem hry))
  · rw [← hvalue]
    exact hfullshape

end TrainVerify.Denote.RelationCompiler

#print axioms TrainVerify.Denote.fw_matmul_allGather_contraction_eq_allReduce_zipWith_rank4
#print axioms TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_contraction_axis_rank4
