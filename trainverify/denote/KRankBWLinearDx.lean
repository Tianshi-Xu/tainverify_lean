import denote.Denote

namespace TrainVerify.Denote

noncomputable section

private theorem foldl_zipWith_eq_sum_range
    (xs ys : List Tensor) (f : Tensor → Tensor → Scalar) (dx dy : Tensor)
    (hlen : ys.length = xs.length) :
    (List.zipWith f xs ys).foldl (fun acc x => acc + x) 0 =
      ∑ r ∈ Finset.range xs.length, f (xs.getD r dx) (ys.getD r dy) := by
  rw [← List.sum_eq_foldl]
  let zs := List.zipWith f xs ys
  have hzlen : zs.length = xs.length := by simp [zs, List.length_zipWith, hlen]
  rw [← hzlen, Finset.sum_range]
  change zs.sum = ∑ i : Fin zs.length, f (xs.getD (↑i) dx) (ys.getD (↑i) dy)
  have hzsum : (∑ i : Fin zs.length, zs[i]) = zs.sum := by
    simpa using Fin.sum_univ_fun_getElem zs id
  rw [← hzsum]
  apply Finset.sum_congr rfl
  intro n _hn
  have hnx : n.val < xs.length := by rw [← hzlen]; exact n.isLt
  have hny : n.val < ys.length := by rw [hlen]; exact hnx
  simp [zs, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hnx, List.getElem?_eq_getElem hny]

private theorem allGatherPrimDimN_2_valAt_1_8_32
    (xs : List Tensor) (K P r j : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32])
    (hK : 0 < K) (hP : P < 8) (hr : r < K) (hj : j < 32) :
    valAt (allGatherPrimDimN 2 K 0 xs) (P * (32 * K) + r * 32 + j) =
      valAt (xs.getD r (zeroTensor [1, 8, 32])) (P * 32 + j) := by
  have hshape : (allGatherPrimDimN 2 K 0 xs).shape = [1, 8, 32 * K] := by
    rw [allGatherPrimDimN_shape 2 K xs [1, 8, 32] hhead]
    simp [List.set, List.getD]
  have mpos : 0 < 32 * K := by omega
  have qlt : r * 32 + j < 32 * K := by omega
  have hbound : P * (32 * K) + (r * 32 + j) < 8 * (32 * K) := by
    calc
      P * (32 * K) + (r * 32 + j) < P * (32 * K) + (32 * K) := Nat.add_lt_add_left qlt _
      _ = (P + 1) * (32 * K) := by ring
      _ ≤ 8 * (32 * K) := Nat.mul_le_mul_right (32 * K) (Nat.succ_le_of_lt hP)
  rw [valAt_of_lt _ _ (by
    rw [hshape]
    simpa [prodShape, Nat.mul_assoc, Nat.add_assoc] using hbound)]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl,
    show ([1,8,32].getD 2 0 : Nat) = 32 from rfl]
  have hrem : (P * (32 * K) + r * 32 + j) % (32 * K) = r * 32 + j := by
    calc
      _ = ((32 * K) * P + (r * 32 + j)) % (32 * K) := by congr 1 <;> ring
      _ = (r * 32 + j) % (32 * K) := Nat.mul_add_mod _ _ _
      _ = r * 32 + j := Nat.mod_eq_of_lt qlt
  have d1 : (P * (32 * K) + r * 32 + j) / (32 * K) = P := by
    calc
      _ = ((32 * K) * P + (r * 32 + j)) / (32 * K) := by congr 1 <;> ring
      _ = P + (r * 32 + j) / (32 * K) := Nat.mul_add_div mpos P _
      _ = P := by rw [Nat.div_eq_of_lt qlt]; omega
  have d2 : ((P * (32 * K) + r * 32 + j) % (32 * K)) / 32 = r := by rw [hrem]; omega
  have d3 : ((P * (32 * K) + r * 32 + j) % (32 * K)) % 32 = j := by rw [hrem]; omega
  have d4 : ((P * (32 * K) + r * 32 + j) % (32 * K)) % 1 = 0 := by omega
  simp only [mpos.ne', show (32:Nat) ≠ 0 by omega,
    Nat.one_ne_zero, if_false, Nat.mul_one, Nat.div_one, d1, d2, d3, d4,
    Nat.add_zero]

private theorem allGatherPrimDimN_0_valAt_32_32
    (xs : List Tensor) (K r j col : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [32, 32])
    (hK : 0 < K) (hr : r < K) (hj : j < 32) (hcol : col < 32) :
    valAt (allGatherPrimDimN 0 K 0 xs) ((r * 32 + j) * 32 + col) =
      valAt (xs.getD r (zeroTensor [32, 32])) (j * 32 + col) := by
  have hshape : (allGatherPrimDimN 0 K 0 xs).shape = [32 * K, 32] := by
    rw [allGatherPrimDimN_shape 0 K xs [32, 32] hhead]
    simp [List.set, List.getD]
  have mpos : 0 < 32 * K * 32 := by omega
  have qrowlt : r * 32 + j < 32 * K := by omega
  have qlt : (r * 32 + j) * 32 + col < 32 * K * 32 := by
    calc
      (r * 32 + j) * 32 + col < (r * 32 + j) * 32 + 32 := Nat.add_lt_add_left hcol _
      _ = (r * 32 + j + 1) * 32 := by ring
      _ ≤ (32 * K) * 32 := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt qrowlt)
  rw [valAt_of_lt _ _ (by rw [hshape]; simpa [prodShape, Nat.mul_assoc] using qlt)]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl,
    show ([32,32].getD 0 0 : Nat) = 32 from rfl]
  have d1 : ((r * 32 + j) * 32 + col) / (32 * K * 32) = 0 := Nat.div_eq_of_lt qlt
  have hrem : ((r * 32 + j) * 32 + col) % (32 * K * 32) =
      (r * 32 + j) * 32 + col := Nat.mod_eq_of_lt qlt
  have d2 : (((r * 32 + j) * 32 + col) % (32 * K * 32)) / 32 / 32 = r := by
    rw [hrem]
    omega
  have d3 : (((r * 32 + j) * 32 + col) % (32 * K * 32)) / 32 % 32 = j := by
    rw [hrem]
    omega
  have d4 : (((r * 32 + j) * 32 + col) % (32 * K * 32)) % 32 = col := by
    rw [hrem]
    omega
  simp only [mpos.ne', show (32:Nat) ≠ 0 by omega, if_false, d1, d2, d3, d4,
    Nat.zero_mul, Nat.zero_add]


-- The dX component of rank-3 `BW_linear` commutes with an arbitrary nonempty
-- ordered tensor-parallel row split whose gradient and weight shards both have
-- width 32. The rank count is the exact common list length.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem bw_linear_dx_allGatherPrimDimN_dim2_rank3
    (gs ws : List Tensor) (x : Tensor)
    (hne : gs ≠ []) (hlen : ws.length = gs.length)
    (hgshapes : ∀ g ∈ gs, g.shape = [1, 8, 32])
    (hwshapes : ∀ w ∈ ws, w.shape = [32, 32])
    (hx : x.shape = [1, 8, 32]) :
    (bw_linear (allGatherPrimDimN 2 gs.length 0 gs) x
      (allGatherPrimDimN 0 ws.length 0 ws)).1 =
      allReducePrim gs.length 0
        (List.zipWith (fun g w => (bw_linear g x w).1) gs ws) := by
  have hK : 0 < gs.length := by
    cases gs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hheadg : (gs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    cases gs with
    | nil => exact (hne rfl).elim
    | cons g rest => simpa using hgshapes g (by simp)
  have hwsne : ws ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    cases gs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp at hlen
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    cases ws with
    | nil => exact (hwsne rfl).elim
    | cons w rest => simpa using hwshapes w (by simp)
  have hGshape : (allGatherPrimDimN 2 gs.length 0 gs).shape = [1, 8, 32 * gs.length] := by
    rw [allGatherPrimDimN_shape 2 gs.length gs [1, 8, 32] hheadg]
    simp [List.set, List.getD]
  have hWshape : (allGatherPrimDimN 0 ws.length 0 ws).shape = [32 * gs.length, 32] := by
    rw [allGatherPrimDimN_shape 0 ws.length ws [32, 32] hheadw]
    simp [List.set, List.getD, hlen]
  have hLshape : (bw_linear (allGatherPrimDimN 2 gs.length 0 gs) x
      (allGatherPrimDimN 0 ws.length 0 ws)).1.shape = [1, 8, 32] :=
    bw_linear_3d_fst_shape 1 8 (32 * gs.length) 32 _ _ _ hGshape hx hWshape
  let pieces := List.zipWith (fun g w => (bw_linear g x w).1) gs ws
  have hpiecesne : pieces ≠ [] := by
    cases gs with
    | nil => exact (hne rfl).elim
    | cons g rest =>
      cases ws with
      | nil => simp at hlen
      | cons w wrest => simp [pieces]
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    cases gs with
    | nil => exact (hne rfl).elim
    | cons g rest =>
      cases ws with
      | nil => simp at hlen
      | cons w wrest =>
        simp [pieces, bw_linear_3d_fst_shape 1 8 32 32 g x w
          (hgshapes g (by simp)) hx (hwshapes w (by simp))]
  have hRshape : (allReducePrim gs.length 0 pieces).shape = [1, 8, 32] := by
    unfold allReducePrim
    simp only [hpiecehead, Tensor.mkShape]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
  let P := idx / 32
  let col := idx % 32
  have hP : P < 8 := by simp [P]; omega
  have hcol : col < 32 := by
    unfold col
    exact Nat.mod_lt idx (by omega)
  have hidxeq : idx = P * 32 + col := by simp [P, col]; omega
  rw [hidxeq]
  rw [bw_linear_fst_valAt_1_8_32_g134 _ _ _ (32 * gs.length)
    hGshape hx hWshape P hP col hcol]
  have hsplit := Finset.sum_range_mul_eq_sum_sum gs.length 32
    (fun j => valAt (allGatherPrimDimN 2 gs.length 0 gs) (P * (gs.length * 32) + j) *
      valAt (allGatherPrimDimN 0 ws.length 0 ws) (j * 32 + col))
  rw [show 32 * gs.length = gs.length * 32 by omega, hsplit]
  have hinner : ∀ r, r < gs.length →
      (∑ j ∈ Finset.range 32,
        valAt (allGatherPrimDimN 2 gs.length 0 gs)
          (P * (gs.length * 32) + (r * 32 + j)) *
        valAt (allGatherPrimDimN 0 ws.length 0 ws)
          ((r * 32 + j) * 32 + col)) =
      valAt (bw_linear (gs.getD r (zeroTensor [1, 8, 32])) x
        (ws.getD r (zeroTensor [32, 32]))).1 (P * 32 + col) := by
    intro r hr
    have hwr : r < ws.length := by rw [hlen]; exact hr
    have hgs : (gs.getD r (zeroTensor [1, 8, 32])).shape = [1, 8, 32] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
      exact hgshapes gs[r] (List.getElem_mem _)
    have hws : (ws.getD r (zeroTensor [32, 32])).shape = [32, 32] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwr]
      exact hwshapes ws[r] (List.getElem_mem _)
    rw [bw_linear_fst_valAt_1_8_32_g134 _ _ _ 32 hgs hx hws P hP col hcol]
    apply Finset.sum_congr rfl
    intro j hj
    have hj32 := Finset.mem_range.mp hj
    rw [show P * (gs.length * 32) + (r * 32 + j) =
      P * (32 * gs.length) + r * 32 + j by ring]
    rw [allGatherPrimDimN_2_valAt_1_8_32 gs gs.length P r j hheadg hK hP hr hj32]
    rw [allGatherPrimDimN_0_valAt_32_32 ws ws.length r j col hheadw
      (by rw [hlen]; exact hK) hwr hj32 hcol]
  have hRval : valAt (allReducePrim gs.length 0 pieces) (P * 32 + col) =
      ∑ r ∈ Finset.range gs.length,
        valAt (bw_linear (gs.getD r (zeroTensor [1, 8, 32])) x
          (ws.getD r (zeroTensor [32, 32]))).1 (P * 32 + col) := by
    have hpbound : P * 32 + col < prodShape (allReducePrim gs.length 0 pieces).shape := by
      rw [hRshape]
      simp only [prodShape, List.foldl]
      rw [← hidxeq]
      exact hidx256
    rw [valAt_of_lt _ _ hpbound]
    unfold allReducePrim
    simp only [Tensor.mkShape]
    rw [← List.foldl_map, List.map_zipWith]
    exact foldl_zipWith_eq_sum_range gs ws
      (fun g w => valAt (bw_linear g x w).1 (P * 32 + col))
      (zeroTensor [1, 8, 32]) (zeroTensor [32, 32]) hlen
  rw [hRval]
  apply Finset.sum_congr rfl
  intro r hr
  exact hinner r (Finset.mem_range.mp hr)

end

end TrainVerify.Denote
