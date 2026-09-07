import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section

set_option maxHeartbeats 500000 in
/-- Ordered output-feature shards of the gradient reconstruct the rows of dW.
The activation is shared; weight values do not enter dW, but their shapes select
its rank-3 linear semantics. No relation between shard values is assumed. -/
theorem bw_linear_dw_row_allGather_rank3
    (K b s o i : Nat) (gs ws : List Tensor) (x : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hgslen : gs.length = K) (hwslen : ws.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, s, o])
    (hws : ∀ w ∈ ws, w.shape = [o, i])
    (hx : x.shape = [b, s, i]) :
    (bw_linear (allGatherPrimDimN 2 K 0 gs) x
      (allGatherPrimDimN 0 K 0 ws)).2 =
      allGatherPrimDimN 0 K 0
        (List.zipWith (fun g w => (bw_linear g x w).2) gs ws) := by
  have hheadg : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, o] := by
    cases hlist : gs with
    | nil => simp [hlist] at hgslen; omega
    | cons g rest =>
      simp only [hlist, List.head?, Option.map, Option.getD]
      exact hgs g (hlist ▸ List.mem_cons_self ..)
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    cases hlist : ws with
    | nil => simp [hlist] at hwslen; omega
    | cons w rest =>
      simp only [hlist, List.head?, Option.map, Option.getD]
      exact hws w (hlist ▸ List.mem_cons_self ..)
  have hgget (r : Nat) (hr : r < K) :
      (gs.getD r (zeroTensor [b, s, o])).shape = [b, s, o] := by
    have hgr : r < gs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgr]
    exact hgs gs[r] (List.getElem_mem _)
  have hwget (r : Nat) (hr : r < K) :
      (ws.getD r (zeroTensor [o, i])).shape = [o, i] := by
    have hwr : r < ws.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwr]
    exact hws ws[r] (List.getElem_mem _)
  have hGshape : (allGatherPrimDimN 2 K 0 gs).shape = [b, s, o * K] := by
    rw [allGatherPrimDimN_shape 2 K gs [b, s, o] hheadg]
    simp [List.set, List.getD]
  have hWshape : (allGatherPrimDimN 0 K 0 ws).shape = [o * K, i] := by
    rw [allGatherPrimDimN_shape 0 K ws [o, i] hheadw]
    simp [List.set, List.getD]
  have hLshape : (bw_linear (allGatherPrimDimN 2 K 0 gs) x
      (allGatherPrimDimN 0 K 0 ws)).2.shape = [o * K, i] :=
    bw_linear_3d_snd_shape b s (o * K) i _ x _ hGshape hx hWshape
  let pieces := List.zipWith (fun g w => (bw_linear g x w).2) gs ws
  have hplen : pieces.length = K := by
    simp [pieces, List.length_zipWith, hgslen, hwslen]
  have hpget (r : Nat) (hr : r < K) :
      pieces.getD r (zeroTensor [o, i]) =
        (bw_linear (gs.getD r (zeroTensor [b, s, o])) x
          (ws.getD r (zeroTensor [o, i]))).2 := by
    have hgr : r < gs.length := by omega
    have hwr : r < ws.length := by omega
    have hpr : r < pieces.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr]
    simp [pieces, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgr,
      List.getElem?_eq_getElem hwr]
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    cases gs with
    | nil => simp at hgslen; omega
    | cons g rest =>
      cases ws with
      | nil => simp at hwslen; omega
      | cons w wrest =>
        simp [pieces, bw_linear_3d_snd_shape b s o i g x w
          (hgs g (by simp)) hx (hws w (by simp))]
  have hRshape : (allGatherPrimDimN 0 K 0 pieces).shape = [o * K, i] := by
    rw [allGatherPrimDimN_shape 0 K pieces [o, i] hpiecehead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hbound : idx < (o * K) * i := by simpa [prodShape] using hidx
  let row := idx / i
  let col := idx % i
  let r := row / o
  let localRow := row % o
  have hrow : row < o * K :=
    Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hbound)
  have hcol : col < i := Nat.mod_lt idx hi
  have hr : r < K := Nat.div_lt_of_lt_mul hrow
  have hlocalRow : localRow < o := Nat.mod_lt row ho
  have hrowEq : r * o + localRow = row := by
    simpa only [r, localRow, Nat.mul_comm] using Nat.div_add_mod row o
  have hidxEq : idx = (r * o + localRow) * i + col := by
    rw [hrowEq]
    simpa only [row, col, Nat.mul_comm] using (Nat.div_add_mod idx i).symm
  have hfullRow : r * o + localRow < o * K := by
    rw [hrowEq]
    exact hrow
  rw [hidxEq, bw_linear_dw_valAt3d _ x _ b s (o * K) i hGshape hx hWshape
    (r * o + localRow) hfullRow col hcol]
  rw [allGatherPrimDimN_dim0_2d_valAt pieces K o i r localRow col
    hK ho hi hr hlocalRow hcol hpiecehead, hpget r hr]
  rw [bw_linear_dw_valAt3d _ x _ b s o i (hgget r hr) hx (hwget r hr)
    localRow hlocalRow col hcol]
  apply Finset.sum_congr rfl
  intro pre hpre
  rw [allGatherPrimDimN_dim2_3d_valAt gs K b s o pre r localRow
    hK ho (Finset.mem_range.mp hpre) hr hlocalRow hheadg]

end
end TrainVerify.Denote
