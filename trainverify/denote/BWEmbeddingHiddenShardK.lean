import denote.KRankLinearGather

namespace TrainVerify.Denote

noncomputable section

open scoped BigOperators

private theorem bw_embedding_hidden_valAt_rank2
    (g ids w : Tensor) (v d row col : Nat)
    (hd : 0 < d) (hw : w.shape = [v, d])
    (hrow : row < v) (hcol : col < d) :
    valAt (bw_embedding g ids w) (row * d + col) =
      ∑ p ∈ Finset.range (prodShape ids.shape),
        if scalarToNat (valAt ids p) = row then valAt g (p * d + col) else 0 := by
  have hidx : row * d + col < v * d := by
    calc
      row * d + col < (row + 1) * d := by rw [Nat.add_mul]; omega
      _ ≤ v * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hrow)
  have hlast : lastD w.shape = d := by rw [hw]; rfl
  have hdiv : (row * d + col) / d = row := by
    rw [show row * d + col = col + d * row by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod : (row * d + col) % d = col := by
    rw [show row * d + col = col + d * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  rw [bw_embedding_valAt g ids w (row * d + col)
    (by rw [hw]; simpa only [prodShape, List.foldl, Nat.one_mul] using hidx)]
  simp only [hlast, hdiv, hmod]

-- 同一份 IDs 在各 rank 上原值复用；仅隐藏特征轴分片。
-- 梯度的所有 batch/sequence 位置求和与固定隐藏特征的 rank 选择交换。
-- 不要求 ID 值域、路由条件或任何预先给定的输出等式。
set_option maxHeartbeats 500000 in
theorem bw_embedding_hidden_allGather_rank3
    (K b s v d : Nat) (gs ws : List Tensor) (ids : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hv : 0 < v) (hd : 0 < d)
    (hgslen : gs.length = K) (hwslen : ws.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, s, d])
    (hws : ∀ w ∈ ws, w.shape = [v, d])
    (hids : ids.shape = [b, s]) :
    bw_embedding (allGatherPrimDimN 2 K 0 gs) ids (allGatherPrimDimN 1 K 0 ws) =
      allGatherPrimDimN 1 K 0 (List.zipWith (fun g w => bw_embedding g ids w) gs ws) := by
  classical
  have hheadg : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, d] := by
    cases gs with
    | nil => simp only [List.length_nil] at hgslen; omega
    | cons g rest => simpa using hgs g (by simp)
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [v, d] := by
    cases ws with
    | nil => simp only [List.length_nil] at hwslen; omega
    | cons w rest => simpa using hws w (by simp)
  have hwsget (r : Nat) (hr : r < K) :
      (ws.getD r (zeroTensor [v, d])).shape = [v, d] := by
    have hwr : r < ws.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwr]
    exact hws ws[r] (List.getElem_mem _)
  have hWshape : (allGatherPrimDimN 1 K 0 ws).shape = [v, d * K] := by
    rw [allGatherPrimDimN_shape 1 K ws [v, d] hheadw]
    simp only [List.set, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
  let pieces := List.zipWith (fun g w => bw_embedding g ids w) gs ws
  have hplen : pieces.length = K := by
    simp only [pieces, List.length_zipWith, hgslen, hwslen, min_self]
  have hpget (r : Nat) (hr : r < K) :
      pieces.getD r (zeroTensor [v, d]) =
        bw_embedding (gs.getD r (zeroTensor [b, s, d])) ids
          (ws.getD r (zeroTensor [v, d])) := by
    have hgr : r < gs.length := by omega
    have hwr : r < ws.length := by omega
    have hpr : r < pieces.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr]
    simp [pieces, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgr,
      List.getElem?_eq_getElem hwr]
  have hpshape (r : Nat) (hr : r < K) :
      (pieces.getD r (zeroTensor [v, d])).shape = [v, d] := by
    rw [hpget r hr, bw_embedding_shape, hwsget r hr]
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [v, d] := by
    have ht := hpshape 0 hK
    cases he : pieces with
    | nil => rw [he] at hplen; simp only [List.length_nil] at hplen; omega
    | cons t ts => simpa [he] using ht
  have hRshape : (allGatherPrimDimN 1 K 0 pieces).shape = [v, d * K] := by
    rw [allGatherPrimDimN_shape 1 K pieces [v, d] hpiecehead]
    simp only [List.set, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
  have hLshape :
      (bw_embedding (allGatherPrimDimN 2 K 0 gs) ids
        (allGatherPrimDimN 1 K 0 ws)).shape = [v, d * K] := by
    rw [bw_embedding_shape, hWshape]
  change bw_embedding (allGatherPrimDimN 2 K 0 gs) ids
    (allGatherPrimDimN 1 K 0 ws) = allGatherPrimDimN 1 K 0 pieces
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hbound : idx < v * (d * K) := by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hfullpos : 0 < d * K := Nat.mul_pos hd hK
  let row := idx / (d * K)
  let rem := idx % (d * K)
  let r := rem / d
  let col := rem % d
  have hrow : row < v := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hbound)
  have hrem : rem < d * K := Nat.mod_lt idx hfullpos
  have hr : r < K := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hrem)
  have hcol : col < d := Nat.mod_lt rem hd
  have hri : r * d + col = rem := by
    simpa only [r, col, Nat.mul_comm] using Nat.div_add_mod rem d
  have hfullcol : r * d + col < d * K := by rw [hri]; exact hrem
  have heq : idx = row * (d * K) + (r * d + col) := by
    rw [hri]
    simpa only [row, rem, Nat.mul_comm] using (Nat.div_add_mod idx (d * K)).symm
  rw [heq, allGatherPrimDimN1_valAt_g240 K v d pieces hK hv hd
    hpiecehead hpshape row hrow r hr col hcol, hpget r hr]
  rw [bw_embedding_hidden_valAt_rank2 _ ids _ v (d * K) row (r * d + col)
      hfullpos hWshape hrow hfullcol,
    bw_embedding_hidden_valAt_rank2 _ ids _ v d row col hd (hwsget r hr) hrow hcol]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p < b * s := by
    have hpos := Finset.mem_range.mp hp
    rw [hids] at hpos
    simpa only [prodShape, List.foldl, Nat.one_mul] using hpos
  rw [allGatherPrimDimN_dim2_3d_valAt gs K b s d p r col hK hd hp' hr hcol hheadg]

end

end TrainVerify.Denote
