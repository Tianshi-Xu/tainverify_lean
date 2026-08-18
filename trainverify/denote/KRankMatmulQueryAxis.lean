import denote.KRankMatmul

namespace TrainVerify.Denote

open scoped BigOperators

set_option maxHeartbeats 500000

/-- A canonical read through a query-axis gather of symbolic rank-4 shards. -/
theorem allGatherPrimDimN_dim2_4d_valAt
    (xs : List Tensor) (K b h q k outer r i l : Nat)
    (hK : 0 < K) (hq : 0 < q) (hk : 0 < k)
    (houter : outer < b * h) (hr : r < K) (hi : i < q) (hl : l < k)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, h, q, k]) :
    valAt (allGatherPrimDimN 2 K 0 xs)
        ((outer * (q * K) + (r * q + i)) * k + l) =
      valAt (xs.getD r (zeroTensor [b, h, q, k]))
        ((outer * q + i) * k + l) := by
  have hqK : 0 < q * K := Nat.mul_pos hq hK
  have hqKk : 0 < q * K * k := Nat.mul_pos hqK hk
  have hlocal : r * q + i < q * K := by
    have hstep : r * q + i < (r + 1) * q := by
      rw [Nat.add_mul]
      omega
    have hr1 : r + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right q hr1
    rw [Nat.mul_comm K q] at hmul
    exact lt_of_lt_of_le hstep hmul
  have hrow : outer * (q * K) + (r * q + i) < (b * h) * (q * K) := by
    have hstep : outer * (q * K) + (r * q + i) < (outer + 1) * (q * K) := by
      rw [Nat.add_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (q * K) houter)
  have hidx : (outer * (q * K) + (r * q + i)) * k + l <
      ((b * h) * (q * K)) * k := by
    have hstep : (outer * (q * K) + (r * q + i)) * k + l <
        (outer * (q * K) + (r * q + i) + 1) * k := by
      calc
        _ < (outer * (q * K) + (r * q + i)) * k + k :=
          Nat.add_lt_add_left hl _
        _ = _ := by ring
    exact lt_of_lt_of_le hstep
      (Nat.mul_le_mul_right k (Nat.succ_le_of_lt hrow))
  have hgshape : (allGatherPrimDimN 2 K 0 xs).shape = [b, h, q * K, k] := by
    rw [allGatherPrimDimN_shape 2 K xs [b, h, q, k] hhead]
    simp [List.set, List.getD]
  have hprod : (outer * (q * K) + (r * q + i)) * k + l <
      prodShape (allGatherPrimDimN 2 K 0 xs).shape := by
    rw [hgshape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.one_mul,
    if_neg (Nat.ne_of_gt hqKk), if_neg (Nat.ne_of_gt hq),
    if_neg (Nat.ne_of_gt hk)]
  have hpreDiv :
      (((outer * (q * K) + (r * q + i)) * k + l) / ((q * K) * k)) = outer := by
    have hlow : (r * q + i) * k + l < (q * K) * k := by
      have hs : (r * q + i) * k + l < (r * q + i + 1) * k := by
        calc
          _ < (r * q + i) * k + k := Nat.add_lt_add_left hl _
          _ = _ := by ring
      exact lt_of_lt_of_le hs
        (Nat.mul_le_mul_right k (Nat.succ_le_of_lt hlocal))
    rw [show (outer * (q * K) + (r * q + i)) * k + l =
        ((r * q + i) * k + l) + ((q * K) * k) * outer by ring,
      Nat.add_mul_div_left _ _ (Nat.mul_pos hqK hk), Nat.div_eq_of_lt hlow,
      Nat.zero_add]
  have hrem :
      (((outer * (q * K) + (r * q + i)) * k + l) % ((q * K) * k)) =
        (r * q + i) * k + l := by
    have hlow : (r * q + i) * k + l < (q * K) * k := by
      have hs : (r * q + i) * k + l < (r * q + i + 1) * k := by
        calc
          _ < (r * q + i) * k + k := Nat.add_lt_add_left hl _
          _ = _ := by ring
      exact lt_of_lt_of_le hs
        (Nat.mul_le_mul_right k (Nat.succ_le_of_lt hlocal))
    rw [show (outer * (q * K) + (r * q + i)) * k + l =
        ((r * q + i) * k + l) + ((q * K) * k) * outer by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hdivK : ((r * q + i) * k + l) / k = r * q + i := by
    rw [show (r * q + i) * k + l = l + k * (r * q + i) by ring,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hl, Nat.zero_add]
  have hdivQ : (r * q + i) / q = r := by
    rw [show r * q + i = i + q * r by ring,
      Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmodQ : (r * q + i) % q = i := by
    rw [show r * q + i = i + q * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have hlRem : ((r * q + i) * k + l) % k = l := by
    rw [show (r * q + i) * k + l = l + k * (r * q + i) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  rw [hpreDiv, hrem, hdivK, hdivQ, hmodQ, hlRem]
  ring_nf

/-- Gathering an arbitrary positive number of rank-4 query shards commutes
with batched matmul against one shared right operand. -/
theorem fw_matmul_allGatherPrimDimN_dim2_K_rank4
    (xs : List Tensor) (y : Tensor) (K b h q k m : Nat)
    (hK : 0 < K) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hlen : xs.length = K)
    (hx : ∀ x ∈ xs, x.shape = [b, h, q, k])
    (hy : y.shape = [b, h, k, m]) :
    fw_matmul (allGatherPrimDimN 2 K 0 xs) y =
      allGatherPrimDimN 2 K 0 (xs.map (fun shard => fw_matmul shard y)) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx0 : x0.shape = [b, h, q, k] := hx x0 (by simp)
  have hhead : (((x0 :: rest).head?.map (fun t => t.shape)).getD []) =
      [b, h, q, k] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hx0
  have hXshape : (allGatherPrimDimN 2 K 0 (x0 :: rest)).shape =
      [b, h, q * K, k] := by
    rw [allGatherPrimDimN_shape 2 K _ [b, h, q, k] hhead]
    simp [List.set, List.getD]
  have hmapHead : ((((x0 :: rest).map (fun shard => fw_matmul shard y)).head?.map
      (fun t => t.shape)).getD []) = [b, h, q, m] := by
    simp only [List.map, List.head?, Option.map, Option.getD]
    exact fw_matmul_rank4_shape x0 y b h q k m hx0 hy
  have hLshape : (fw_matmul (allGatherPrimDimN 2 K 0 (x0 :: rest)) y).shape =
      [b, h, q * K, m] := fw_matmul_rank4_shape _ _ b h (q * K) k m hXshape hy
  have hRshape :
      (allGatherPrimDimN 2 K 0 ((x0 :: rest).map (fun shard => fw_matmul shard y))).shape =
        [b, h, q * K, m] := by
    rw [allGatherPrimDimN_shape 2 K _ [b, h, q, m] hmapHead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hbound : idx < (b * h * (q * K)) * m := by
      simpa [prodShape, Nat.mul_assoc] using hidx
    have hqK : 0 < q * K := Nat.mul_pos hq hK
    set col := idx % m with hcolDef
    set row := idx / m with hrowDef
    set outer := row / (q * K) with houterDef
    set query := row % (q * K) with hqueryDef
    set r := query / q with hrDef
    set i := query % q with hiDef
    have hcol : col < m := by rw [hcolDef]; exact Nat.mod_lt _ hm
    have hrow : row < b * h * (q * K) := by
      rw [hrowDef, Nat.div_lt_iff_lt_mul hm]
      exact hbound
    have houter : outer < b * h := by
      rw [houterDef, Nat.div_lt_iff_lt_mul hqK]
      exact hrow
    have hquery : query < q * K := by rw [hqueryDef]; exact Nat.mod_lt _ hqK
    have hr : r < K := by
      rw [hrDef, Nat.div_lt_iff_lt_mul hq]
      simpa [Nat.mul_comm] using hquery
    have hi : i < q := by rw [hiDef]; exact Nat.mod_lt _ hq
    have hrowEq : outer * (q * K) + query = row := by
      simpa [houterDef, hqueryDef, Nat.mul_comm] using Nat.div_add_mod row (q * K)
    have hqueryEq : r * q + i = query := by
      simpa [hrDef, hiDef, Nat.mul_comm] using Nat.div_add_mod query q
    have hidxEq : idx = (outer * (q * K) + (r * q + i)) * m + col := by
      calc
        idx = row * m + col := by
          simpa [row, col, Nat.mul_comm] using (Nat.div_add_mod idx m).symm
        _ = _ := by rw [← hrowEq, ← hqueryEq]
    have hrlen : r < (x0 :: rest).length := by omega
    have hxr : ((x0 :: rest)[r]).shape = [b, h, q, k] :=
      hx _ (List.getElem_mem hrlen)
    have hmapGetD :
        ((x0 :: rest).map (fun shard => fw_matmul shard y)).getD r
          (zeroTensor [b, h, q, m]) = fw_matmul ((x0 :: rest)[r]) y := by
      rw [List.getD]
      rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hrlen)]
      simp only [Option.getD_some, List.getElem_map]
    rw [hidxEq]
    rw [fw_matmul_rank4_valAt (allGatherPrimDimN 2 K 0 (x0 :: rest)) y
      b h (q * K) k m outer (r * q + i) col hm houter
        (by rw [hqueryEq]; exact hquery) hcol hXshape hy]
    rw [allGatherPrimDimN_dim2_4d_valAt
      ((x0 :: rest).map (fun shard => fw_matmul shard y)) K b h q m outer r i col
      hK hq hm houter hr hi hcol hmapHead]
    rw [hmapGetD]
    rw [fw_matmul_rank4_valAt ((x0 :: rest)[r]) y
      b h q k m outer i col hm houter hi hcol hxr hy]
    apply Finset.sum_congr rfl
    intro l hlmem
    have hl : l < k := Finset.mem_range.mp hlmem
    rw [allGatherPrimDimN_dim2_4d_valAt (x0 :: rest)
      K b h q k outer r i l hK hq hk houter hr hi hl hhead]
    rw [List.getD, List.getElem?_eq_getElem hrlen, Option.getD_some]

end TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

/-- Query-axis matmul transport. `hjoined` is the actual SM/PM shared-value
authority for the right operand; shape agreement alone is intentionally
insufficient. -/
theorem ShardedRel.fw_matmul_query_axis_rank4
    {x y sharedY : Tensor} {xs : List Tensor} {K b h q k m : Nat}
    (hrel : ShardedRel x xs 2 [b, h, q * K, k] [b, h, q, k])
    (hjoined : y = sharedY ∧ y.shape = [b, h, k, m] ∧
      sharedY.shape = [b, h, k, m])
    (hK : 0 < K) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hlen : xs.length = K) :
    ShardedRel (fw_matmul x y)
      (xs.map (fun shard => fw_matmul shard sharedY)) 2
      [b, h, q * K, m] [b, h, q, m] := by
  rcases hjoined with ⟨hyValue, hy, hsharedY⟩
  subst sharedY
  have hx : ∀ z ∈ xs, z.shape = [b, h, q, k] := hrel.shard_shapes
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := ?_
    gather_dim_lt := by simp
    shard_shapes := ?_
    shape_contract := ?_
  }
  · rw [hrel.full_value, List.length_map, hlen]
    exact TrainVerify.Denote.fw_matmul_allGatherPrimDimN_dim2_K_rank4
      xs y K b h q k m hK hq hk hm hlen hx hy
  · exact TrainVerify.Denote.fw_matmul_rank4_shape x y b h (q * K) k m
      hrel.full_shape hy
  · intro hnil
    have hmLen : (xs.map (fun shard => fw_matmul shard y)).length = 0 := by
      rw [hnil]
      rfl
    rw [List.length_map, hlen] at hmLen
    omega
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact TrainVerify.Denote.fw_matmul_rank4_shape w y b h q k m (hx w hw) hy
  · simp [List.set, List.getD, hlen]

end TrainVerify.Denote.RelationCompiler

#print axioms TrainVerify.Denote.fw_matmul_allGatherPrimDimN_dim2_K_rank4
#print axioms TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4
