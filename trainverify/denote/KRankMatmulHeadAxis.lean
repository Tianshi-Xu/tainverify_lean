import denote.KRankMatmul

namespace TrainVerify.Denote

open scoped BigOperators

set_option maxHeartbeats 500000

/-- A canonical read through a dimension-1 gather of rank-4 shards.  The
ordered rank `r` and local head `p` become the full head `r * h + p`. -/
theorem allGatherPrimDimN_dim1_4d_valAt
    (zs : List Tensor) (K b h n d batch r p i j : Nat)
    (hK : 0 < K) (hh : 0 < h) (hn : 0 < n) (hd : 0 < d)
    (hbatch : batch < b) (hr : r < K) (hp : p < h)
    (hi : i < n) (hj : j < d)
    (hhead : (zs.head?.map (fun t => t.shape)).getD [] = [b, h, n, d]) :
    valAt (allGatherPrimDimN 1 K 0 zs)
        (((batch * (h * K) + (r * h + p)) * n + i) * d + j) =
      valAt (zs.getD r (zeroTensor [b, h, n, d]))
        (((batch * h + p) * n + i) * d + j) := by
  have hhK : 0 < h * K := Nat.mul_pos hh hK
  have hnd : 0 < n * d := Nat.mul_pos hn hd
  have hfullStride : 0 < h * K * (n * d) := Nat.mul_pos hhK hnd
  have hlocalStride : 0 < h * (n * d) := Nat.mul_pos hh hnd
  have hrp : r * h + p < h * K := by
    have hstep : r * h + p < (r + 1) * h := by
      calc
        r * h + p < r * h + h := Nat.add_lt_add_left hp _
        _ = (r + 1) * h := by ring
    have hle : (r + 1) * h ≤ K * h := Nat.mul_le_mul_right h hr
    calc
      r * h + p < (r + 1) * h := hstep
      _ ≤ K * h := hle
      _ = h * K := by ring
  have hid : i * d + j < n * d := by
    calc
      i * d + j < i * d + d := Nat.add_lt_add_left hj _
      _ = (i + 1) * d := by ring
      _ ≤ n * d := Nat.mul_le_mul_right d hi
  have hlow : (r * h + p) * (n * d) + (i * d + j) < h * K * (n * d) := by
    calc
      (r * h + p) * (n * d) + (i * d + j)
          < (r * h + p) * (n * d) + n * d := Nat.add_lt_add_left hid _
      _ = (r * h + p + 1) * (n * d) := by ring
      _ ≤ (h * K) * (n * d) := Nat.mul_le_mul_right (n * d) hrp
  have hidxEq :
      ((batch * (h * K) + (r * h + p)) * n + i) * d + j =
        ((r * h + p) * (n * d) + (i * d + j)) +
          (h * K * (n * d)) * batch := by ring
  have hidx : ((batch * (h * K) + (r * h + p)) * n + i) * d + j <
      b * (h * K) * n * d := by
    rw [hidxEq]
    calc
      ((r * h + p) * (n * d) + (i * d + j)) +
          (h * K * (n * d)) * batch
          < (h * K * (n * d)) + (h * K * (n * d)) * batch :=
            Nat.add_lt_add_right hlow _
      _ = (batch + 1) * (h * K * (n * d)) := by ring
      _ ≤ b * (h * K * (n * d)) := Nat.mul_le_mul_right _ hbatch
      _ = b * (h * K) * n * d := by ring
  have hgshape : (allGatherPrimDimN 1 K 0 zs).shape = [b, h * K, n, d] := by
    rw [allGatherPrimDimN_shape 1 K zs [b, h, n, d] hhead]
    simp [List.set, List.getD]
  have hprod : ((batch * (h * K) + (r * h + p)) * n + i) * d + j <
      prodShape (allGatherPrimDimN 1 K 0 zs).shape := by
    rw [hgshape]
    simpa [prodShape] using hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.one_mul, if_neg (Nat.ne_of_gt hh), if_neg (Nat.ne_of_gt hnd),
    if_neg (Nat.ne_of_gt hfullStride)]
  have hpre :
      (((batch * (h * K) + (r * h + p)) * n + i) * d + j) /
          (h * K * (n * d)) = batch := by
    rw [hidxEq, Nat.add_mul_div_left _ _ hfullStride,
      Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hrem :
      (((batch * (h * K) + (r * h + p)) * n + i) * d + j) %
          (h * K * (n * d)) = (r * h + p) * (n * d) + (i * d + j) := by
    rw [hidxEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hheadDiv :
      ((r * h + p) * (n * d) + (i * d + j)) / (n * d) = r * h + p := by
    rw [show (r * h + p) * (n * d) + (i * d + j) =
        (i * d + j) + (n * d) * (r * h + p) by ring,
      Nat.add_mul_div_left _ _ hnd, Nat.div_eq_of_lt hid, Nat.zero_add]
  have htailRem :
      ((r * h + p) * (n * d) + (i * d + j)) % (n * d) = i * d + j := by
    rw [show (r * h + p) * (n * d) + (i * d + j) =
        (i * d + j) + (n * d) * (r * h + p) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hid]
  have hrank : (r * h + p) / h = r := by
    rw [show r * h + p = p + h * r by ring,
      Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hlocalHead : (r * h + p) % h = p := by
    rw [show r * h + p = p + h * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  rw [hpre, hrem, hheadDiv, htailRem, hrank, hlocalHead]
  congr 1
  ring

/-- Aligned head-axis rank-4 matmul commutes with an ordered dynamic-`K`
dimension-1 gather on both operands. -/
theorem fw_matmul_allGatherPrimDimN_dim1_aligned_K_rank4
    (xs ys : List Tensor) (K b h q k m : Nat)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hxsLen : xs.length = K) (hysLen : ys.length = K)
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, k])
    (hys : ∀ y ∈ ys, y.shape = [b, h, k, m]) :
    fw_matmul (allGatherPrimDimN 1 K 0 xs) (allGatherPrimDimN 1 K 0 ys) =
      allGatherPrimDimN 1 K 0 (List.zipWith fw_matmul xs ys) := by
  have hxsNe : xs ≠ [] := by
    intro he
    rw [he] at hxsLen
    simp only [List.length_nil] at hxsLen
    omega
  have hysNe : ys ≠ [] := by
    intro he
    rw [he] at hysLen
    simp only [List.length_nil] at hysLen
    omega
  have hheadX : (xs.head?.map (fun t => t.shape)).getD [] = [b, h, q, k] := by
    obtain ⟨x0, xr, rfl⟩ := List.exists_cons_of_ne_nil hxsNe
    simp only [List.head?, Option.map, Option.getD]
    exact hxs x0 (by simp)
  have hheadY : (ys.head?.map (fun t => t.shape)).getD [] = [b, h, k, m] := by
    obtain ⟨y0, yr, rfl⟩ := List.exists_cons_of_ne_nil hysNe
    simp only [List.head?, Option.map, Option.getD]
    exact hys y0 (by simp)
  have hzipLen : (List.zipWith fw_matmul xs ys).length = K := by
    rw [List.length_zipWith, hxsLen, hysLen, Nat.min_self]
  have hzipPos : 0 < (List.zipWith fw_matmul xs ys).length := by omega
  have hxsPos : 0 < xs.length := by omega
  have hysPos : 0 < ys.length := by omega
  have hheadZip :
      ((List.zipWith fw_matmul xs ys).head?.map (fun t => t.shape)).getD [] =
        [b, h, q, m] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hzipPos]
    simp only [Option.map_some, Option.getD_some]
    have hz0 : (List.zipWith fw_matmul xs ys)[0]'hzipPos =
        fw_matmul (xs[0]'hxsPos) (ys[0]'hysPos) := List.getElem_zipWith
    rw [hz0]
    exact fw_matmul_rank4_shape _ _ b h q k m
      (hxs _ (List.getElem_mem hxsPos)) (hys _ (List.getElem_mem hysPos))
  have hXshape : (allGatherPrimDimN 1 K 0 xs).shape = [b, h * K, q, k] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, h, q, k] hheadX]
    simp [List.set, List.getD]
  have hYshape : (allGatherPrimDimN 1 K 0 ys).shape = [b, h * K, k, m] := by
    rw [allGatherPrimDimN_shape 1 K ys [b, h, k, m] hheadY]
    simp [List.set, List.getD]
  have hLshape :
      (fw_matmul (allGatherPrimDimN 1 K 0 xs) (allGatherPrimDimN 1 K 0 ys)).shape =
        [b, h * K, q, m] :=
    fw_matmul_rank4_shape _ _ b (h * K) q k m hXshape hYshape
  have hRshape :
      (allGatherPrimDimN 1 K 0 (List.zipWith fw_matmul xs ys)).shape =
        [b, h * K, q, m] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, h, q, m] hheadZip]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hbound : idx < b * (h * K) * q * m := by
      simpa [prodShape] using hidx
    have hhK : 0 < h * K := Nat.mul_pos hh hK
    have hqm : 0 < q * m := Nat.mul_pos hq hm
    have hstride : 0 < h * K * (q * m) := Nat.mul_pos hhK hqm
    set batch := idx / (h * K * (q * m)) with hbatchDef
    set rem := idx % (h * K * (q * m)) with hremDef
    set fullHead := rem / (q * m) with hfullHeadDef
    set tail := rem % (q * m) with htailDef
    set r := fullHead / h with hrDef
    set p := fullHead % h with hpDef
    set i := tail / m with hiDef
    set j := tail % m with hjDef
    have hbatch : batch < b := by
      rw [hbatchDef, Nat.div_lt_iff_lt_mul hstride]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbound
    have hrem : rem < h * K * (q * m) := by
      rw [hremDef]
      exact Nat.mod_lt _ hstride
    have hfullHead : fullHead < h * K := by
      rw [hfullHeadDef, Nat.div_lt_iff_lt_mul hqm]
      exact hrem
    have hr : r < K := by
      rw [hrDef, Nat.div_lt_iff_lt_mul hh]
      simpa [Nat.mul_comm] using hfullHead
    have hp : p < h := by rw [hpDef]; exact Nat.mod_lt _ hh
    have htail : tail < q * m := by rw [htailDef]; exact Nat.mod_lt _ hqm
    have hi : i < q := by
      rw [hiDef, Nat.div_lt_iff_lt_mul hm]
      exact htail
    have hj : j < m := by rw [hjDef]; exact Nat.mod_lt _ hm
    have hheadEq : r * h + p = fullHead := by
      simpa [hrDef, hpDef, Nat.mul_comm] using Nat.div_add_mod fullHead h
    have htailEq : i * m + j = tail := by
      simpa [hiDef, hjDef, Nat.mul_comm] using Nat.div_add_mod tail m
    have hremEq : fullHead * (q * m) + tail = rem := by
      simpa [hfullHeadDef, htailDef, Nat.mul_comm] using Nat.div_add_mod rem (q * m)
    have hidxEq :
        idx = ((batch * (h * K) + (r * h + p)) * q + i) * m + j := by
      calc
        idx = batch * (h * K * (q * m)) + rem := by
          simpa [batch, rem, Nat.mul_comm] using
            (Nat.div_add_mod idx (h * K * (q * m))).symm
        _ = batch * (h * K * (q * m)) + (fullHead * (q * m) + tail) := by
          rw [hremEq]
        _ = batch * (h * K * (q * m)) +
            ((r * h + p) * (q * m) + (i * m + j)) := by
          rw [hheadEq, htailEq]
        _ = ((batch * (h * K) + (r * h + p)) * q + i) * m + j := by ring
    have houterFull : batch * (h * K) + (r * h + p) < b * (h * K) := by
      have hlocal : r * h + p < h * K := by rw [hheadEq]; exact hfullHead
      calc
        batch * (h * K) + (r * h + p) < batch * (h * K) + h * K :=
          Nat.add_lt_add_left hlocal _
        _ = (batch + 1) * (h * K) := by ring
        _ ≤ b * (h * K) := Nat.mul_le_mul_right _ hbatch
    have hrx : r < xs.length := by omega
    have hry : r < ys.length := by omega
    have hrz : r < (List.zipWith fw_matmul xs ys).length := by omega
    have hxShape : (xs[r]).shape = [b, h, q, k] :=
      hxs _ (List.getElem_mem hrx)
    have hyShape : (ys[r]).shape = [b, h, k, m] :=
      hys _ (List.getElem_mem hry)
    have hzipGetD : (List.zipWith fw_matmul xs ys).getD r
        (zeroTensor [b, h, q, m]) = fw_matmul (xs[r]) (ys[r]) := by
      rw [List.getD, List.getElem?_eq_getElem hrz, Option.getD_some]
      exact List.getElem_zipWith
    have hxGetD : xs.getD r (zeroTensor [b, h, q, k]) = xs[r] := by
      rw [List.getD, List.getElem?_eq_getElem hrx, Option.getD_some]
    have hyGetD : ys.getD r (zeroTensor [b, h, k, m]) = ys[r] := by
      rw [List.getD, List.getElem?_eq_getElem hry, Option.getD_some]
    rw [hidxEq]
    rw [fw_matmul_rank4_valAt
      (allGatherPrimDimN 1 K 0 xs) (allGatherPrimDimN 1 K 0 ys)
      b (h * K) q k m (batch * (h * K) + (r * h + p)) i j
      hm houterFull hi hj hXshape hYshape]
    rw [allGatherPrimDimN_dim1_4d_valAt
      (List.zipWith fw_matmul xs ys) K b h q m batch r p i j
      hK hh hq hm hbatch hr hp hi hj hheadZip]
    rw [hzipGetD]
    rw [fw_matmul_rank4_valAt (xs[r]) (ys[r]) b h q k m
      (batch * h + p) i j hm (by
        calc
          batch * h + p < batch * h + h := Nat.add_lt_add_left hp _
          _ = (batch + 1) * h := by ring
          _ ≤ b * h := Nat.mul_le_mul_right h hbatch) hi hj hxShape hyShape]
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l < k := Finset.mem_range.mp hl
    rw [allGatherPrimDimN_dim1_4d_valAt xs K b h q k batch r p i l
      hK hh hq hk hbatch hr hp hi hlk hheadX, hxGetD]
    rw [allGatherPrimDimN_dim1_4d_valAt ys K b h k m batch r p l j
      hK hh hk hm hbatch hr hp hlk hj hheadY, hyGetD]

end TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

/-- `ShardedRel` transport for aligned head-axis rank-4 matmul.  Both ordered
shard lists have the same nonempty dynamic rank count `K`, so `zipWith`
preserves rank-wise pairing. -/
theorem ShardedRel.fw_matmul_head_axis_rank4
    {x y : Tensor} {xs ys : List Tensor} {K b h q k m : Nat}
    (hxrel : ShardedRel x xs 1 [b, h * K, q, k] [b, h, q, k])
    (hyrel : ShardedRel y ys 1 [b, h * K, k, m] [b, h, k, m])
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hxsLen : xs.length = K) (hysLen : ys.length = K) :
    ShardedRel (fw_matmul x y) (List.zipWith fw_matmul xs ys) 1
      [b, h * K, q, m] [b, h, q, m] := by
  have hzipLen : (List.zipWith fw_matmul xs ys).length = K := by
    rw [List.length_zipWith, hxsLen, hysLen, Nat.min_self]
  have hzipShapes : ∀ z ∈ List.zipWith fw_matmul xs ys,
      z.shape = [b, h, q, m] := by
    intro z hz
    obtain ⟨r, hrz, rfl⟩ := List.mem_iff_getElem.mp hz
    have hrx : r < xs.length := by
      rw [List.length_zipWith] at hrz
      omega
    have hry : r < ys.length := by
      rw [List.length_zipWith] at hrz
      omega
    rw [List.getElem_zipWith]
    exact TrainVerify.Denote.fw_matmul_rank4_shape _ _ b h q k m
      (hxrel.shard_shapes _ (List.getElem_mem hrx))
      (hyrel.shard_shapes _ (List.getElem_mem hry))
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := ?_
    gather_dim_lt := by simp
    shard_shapes := ?_
    shape_contract := ?_
  }
  · rw [hxrel.full_value, hyrel.full_value, hxsLen, hysLen, hzipLen]
    exact TrainVerify.Denote.fw_matmul_allGatherPrimDimN_dim1_aligned_K_rank4
      xs ys K b h q k m hK hh hq hk hm hxsLen hysLen
      hxrel.shard_shapes hyrel.shard_shapes
  · exact TrainVerify.Denote.fw_matmul_rank4_shape x y b (h * K) q k m
      hxrel.full_shape hyrel.full_shape
  · intro hnil
    have hz : (List.zipWith fw_matmul xs ys).length = 0 := by rw [hnil]; rfl
    rw [hzipLen] at hz
    omega
  · intro z hz
    exact hzipShapes z hz
  · simp [List.set, List.getD, hzipLen]

end TrainVerify.Denote.RelationCompiler

#print axioms TrainVerify.Denote.fw_matmul_allGatherPrimDimN_dim1_aligned_K_rank4
#print axioms TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_head_axis_rank4
