import denote.RelationCompiler

open TrainVerify.Denote
namespace TrainVerify.Denote

set_option maxHeartbeats 500000 in
theorem valAt_fw_view_eq_of_prod
    (target : Shape) (x : Tensor) (idx : Nat)
    (hprod : prodShape target = prodShape x.shape) :
    valAt (fw_view target x) idx = valAt x idx := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  split <;> split <;> simp_all

set_option maxHeartbeats 500000 in
theorem fw_view_fw_rms_norm_flatten3d
    (x w : Tensor) (rows middle hidden : Nat)
    (hrows : 0 < rows) (hmiddle : 0 < middle) (hhidden : 0 < hidden)
    (hx : x.shape = [rows, middle, hidden]) :
    fw_view [rows * middle, hidden] (fw_rms_norm x w) =
      fw_rms_norm (fw_view [rows * middle, hidden] x) w := by
  have hprod : prodShape [rows * middle, hidden] = prodShape x.shape := by
    rw [hx]
    simp [prodShape]
  have hrmsShape : (fw_rms_norm x w).shape = x.shape := by
    unfold fw_rms_norm
    rw [hx]
    simp [Tensor.mkShape]
  have hprodRms : prodShape [rows * middle, hidden] =
      prodShape (fw_rms_norm x w).shape := by rw [hrmsShape]; exact hprod
  have hrms : ∀ row, rmsMeanSqAt (fw_view [rows * middle, hidden] x) row hidden =
      rmsMeanSqAt x row hidden := by
    intro row
    unfold rmsMeanSqAt
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [valAt_fw_view_eq_of_prod _ _ _ hprod]
  have hviewShape : (fw_view [rows * middle, hidden] x).shape =
      [rows * middle, hidden] := rfl
  apply Tensor.ext
  · simp [fw_view, fw_rms_norm, hx, Tensor.mkShape]
  · intro idx hidx
    rw [valAt_fw_view_eq_of_prod _ _ _ hprodRms]
    unfold fw_rms_norm
    rw [hx, hviewShape]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, Tensor.mkShape]
    simp only [valAt_fw_view_eq_of_prod _ _ _ hprod, hrms]
    simp [valAt, prodShape, Nat.mul_assoc]

set_option maxHeartbeats 500000 in
theorem fw_rms_norm_allGather0_commute_2_core_3d
    (a b w : Tensor) (shard middle hidden : Nat)
    (hshard : 0 < shard) (hmiddle : 0 < middle) (hhidden : 0 < hidden)
    (ha : a.shape = [shard, middle, hidden])
    (hb : b.shape = [shard, middle, hidden]) :
    fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w =
      allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [shard, middle, hidden] := by simp [ha]
  have hGshape : (allGatherPrimDimN 0 2 0 [a, b]).shape =
      [shard * 2, middle, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, middle, hidden] hhead]
    simp [List.set, List.getD]
  have hrmsShape : ∀ x : Tensor, x.shape = [shard, middle, hidden] →
      (fw_rms_norm x w).shape = [shard, middle, hidden] := by
    intro x hx
    unfold fw_rms_norm
    rw [hx]
    simp [Tensor.mkShape]
  have hra := hrmsShape a ha
  have hrb := hrmsShape b hb
  have hheadR : (([fw_rms_norm a w, fw_rms_norm b w] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [shard, middle, hidden] := by simp [hra]
  have hRshape : (allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w]).shape =
      [shard * 2, middle, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, middle, hidden] hheadR]
    simp [List.set, List.getD]
  have hLshape : (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w).shape =
      [shard * 2, middle, hidden] := by
    unfold fw_rms_norm
    rw [hGshape]
    simp [Tensor.mkShape]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hbound : idx < shard * 2 * middle * hidden := by
      simpa [prodShape, Nat.mul_assoc] using hidx
    set row := idx / hidden with hrow
    set col := idx % hidden with hcol
    have hcolLt : col < hidden := by rw [hcol]; exact Nat.mod_lt _ hhidden
    have hrowLt : row < shard * 2 * middle := by
      rw [hrow]
      exact Nat.div_lt_iff_lt_mul hhidden |>.mpr (by simpa [Nat.mul_assoc] using hbound)
    set block := shard * middle with hblock
    have hblockPos : 0 < block := by dsimp [block]; positivity
    set rank := row / block with hrank
    set loc := row % block with hloc
    have hrankLt : rank < 2 := by
      rw [hrank]
      apply (Nat.div_lt_iff_lt_mul hblockPos).mpr
      simpa [hblock, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hrowLt
    have hlocLt : loc < block := by rw [hloc]; exact Nat.mod_lt _ hblockPos
    set i := loc / middle with hi
    set j := loc % middle with hj
    have hiLt : i < shard := by
      rw [hi]
      rw [hblock] at hlocLt
      exact (Nat.div_lt_iff_lt_mul hmiddle).mpr (by simpa [Nat.mul_comm] using hlocLt)
    have hjLt : j < middle := by rw [hj]; exact Nat.mod_lt _ hmiddle
    have hrowEq : row = (rank * shard + i) * middle + j := by
      have h1 : row = block * (row / block) + row % block := (Nat.div_add_mod row block).symm
      have h2 : loc = middle * (loc / middle) + loc % middle :=
        (Nat.div_add_mod loc middle).symm
      rw [h1, ← hrank, ← hloc, h2, ← hi, ← hj, hblock]
      ring
    have hidxEq : idx = ((rank * shard + i) * middle + j) * hidden + col := by
      calc
        idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
        _ = hidden * row + col := by rw [← hrow, ← hcol]
        _ = ((rank * shard + i) * middle + j) * hidden + col := by rw [hrowEq]; ring
    have hab : ∀ r (_ : r < 2),
        ([a, b].getD r (zeroTensor [shard, middle, hidden])).shape =
          [shard, middle, hidden] := by
      intro r hr
      have : r = 0 ∨ r = 1 := by omega
      rcases this with rfl | rfl <;> simp [List.getD, ha, hb]
    have hrab : ∀ r (_ : r < 2),
        ([fw_rms_norm a w, fw_rms_norm b w].getD r
          (zeroTensor [shard, middle, hidden])).shape = [shard, middle, hidden] := by
      intro r hr
      have : r = 0 ∨ r = 1 := by omega
      rcases this with rfl | rfl <;> simp [List.getD, hra, hrb]
    have hmean : rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b])
        ((rank * shard + i) * middle + j) hidden =
        rmsMeanSqAt ([a, b].getD rank (zeroTensor [shard, middle, hidden]))
          (i * middle + j) hidden := by
      unfold rmsMeanSqAt
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [allGatherPrimDimN0_valAt_3D 2 shard middle hidden [a, b]
        (by omega) hshard hmiddle hhidden hhead hab rank hrankLt i hiLt j hjLt k hk]
    rw [hidxEq]
    have hLval : valAt (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w)
        (((rank * shard + i) * middle + j) * hidden + col) =
        (valAt (allGatherPrimDimN 0 2 0 [a, b])
          (((rank * shard + i) * middle + j) * hidden + col) *
          (1 / sqrtFn (rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b])
            ((rank * shard + i) * middle + j) hidden + rmsNormEps))) *
          valAt w col := by
      unfold fw_rms_norm
      rw [show (allGatherPrimDimN 0 2 0 [a, b]).shape.reverse =
          hidden :: [middle, shard * 2] by rw [hGshape]; rfl]
      simp only [Tensor.mkShape, valAt]
      have hidxGather : ((rank * shard + i) * middle + j) * hidden + col <
          prodShape (allGatherPrimDimN 0 2 0 [a, b]).shape := by
        rw [← hidxEq]
        simpa [hGshape] using hidx
      have hdivIdx : (((rank * shard + i) * middle + j) * hidden + col) / hidden =
          ((rank * shard + i) * middle + j) := by
        rw [show ((rank * shard + i) * middle + j) * hidden + col =
          col + hidden * ((rank * shard + i) * middle + j) by ring,
          Nat.add_mul_div_left _ _ hhidden, Nat.div_eq_of_lt hcolLt, Nat.zero_add]
      have hmodIdx : (((rank * shard + i) * middle + j) * hidden + col) % hidden = col := by
        rw [show ((rank * shard + i) * middle + j) * hidden + col =
          col + hidden * ((rank * shard + i) * middle + j) by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcolLt]
      simp [hidxGather, hdivIdx, hmodIdx, Nat.mod_eq_of_lt hcolLt]
    rw [hLval, hmean]
    rw [allGatherPrimDimN0_valAt_3D 2 shard middle hidden [a, b]
      (by omega) hshard hmiddle hhidden hhead hab rank hrankLt i hiLt j hjLt col hcolLt]
    rw [allGatherPrimDimN0_valAt_3D 2 shard middle hidden
      [fw_rms_norm a w, fw_rms_norm b w] (by omega) hshard hmiddle hhidden
      hheadR hrab rank hrankLt i hiLt j hjLt col hcolLt]
    have hget : [fw_rms_norm a w, fw_rms_norm b w].getD rank
        (zeroTensor [shard, middle, hidden]) =
        fw_rms_norm ([a, b].getD rank (zeroTensor [shard, middle, hidden])) w := by
      interval_cases rank <;> simp [List.getD]
    rw [hget]
    set x := [a, b].getD rank (zeroTensor [shard, middle, hidden]) with hx
    have hxShape : x.shape = [shard, middle, hidden] := hab rank hrankLt
    unfold fw_rms_norm
    rw [show x.shape.reverse = hidden :: [middle, shard] by rw [hxShape]; rfl]
    simp only [Tensor.mkShape, valAt]
    have hlocBound : (i * middle + j) * hidden + col <
        prodShape x.shape := by
      rw [hxShape]
      simp only [prodShape, List.foldl]
      calc
        (i * middle + j) * hidden + col =
            i * (middle * hidden) + (j * hidden + col) := by ring
        _ < i * (middle * hidden) + middle * hidden := by
          have : j * hidden + col < middle * hidden := by
            calc
              j * hidden + col < j * hidden + hidden := by omega
              _ = (j + 1) * hidden := by ring
              _ ≤ middle * hidden := Nat.mul_le_mul_right _ (by omega)
          omega
        _ = (i + 1) * (middle * hidden) := by ring
        _ ≤ shard * (middle * hidden) := Nat.mul_le_mul_right _ (by omega)
        _ = 1 * shard * middle * hidden := by ring
    have hdivLocal : ((i * middle + j) * hidden + col) / hidden = i * middle + j := by
      rw [show (i * middle + j) * hidden + col = col + hidden * (i * middle + j) by ring,
        Nat.add_mul_div_left _ _ hhidden, Nat.div_eq_of_lt hcolLt, Nat.zero_add]
    have hmodLocal : ((i * middle + j) * hidden + col) % hidden = col := by
      rw [show (i * middle + j) * hidden + col = col + hidden * (i * middle + j) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcolLt]
    simp [hlocBound, hdivLocal, hmodLocal, Nat.mod_eq_of_lt hcolLt]

end TrainVerify.Denote
