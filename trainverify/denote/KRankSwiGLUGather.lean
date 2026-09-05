import denote.KRankLinearReduction
import denote.KRankLinearGather
import denote.InnerChunkCEShard

open TrainVerify.Denote

namespace TrainVerify.Denote

set_option maxRecDepth 100000

set_option maxHeartbeats 500000 in
theorem allGatherPrimDimN_dim1_two_valAt_2d
    (x0 x1 : Tensor) (rows shard idx : Nat)
    (hrows : 0 < rows) (hshard : 0 < shard)
    (hx0 : x0.shape = [rows, shard]) (hx1 : x1.shape = [rows, shard])
    (hidx : idx < rows * (shard * 2)) :
    valAt (allGatherPrimDimN 1 2 0 [x0, x1]) idx =
      valAt ([x0, x1].getD ((idx % (shard * 2)) / shard)
        (zeroTensor [rows, shard]))
        (idx / (shard * 2) * shard + (idx % (shard * 2)) % shard) := by
  have hhead : (([x0, x1].head?.map (fun t => t.shape)).getD []) =
      [rows, shard] := by simp [hx0]
  have hshape : (allGatherPrimDimN 1 2 0 [x0, x1]).shape =
      [rows, shard * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, shard] hhead]
    simp [List.set, List.getD]
  have hp : idx < prodShape (allGatherPrimDimN 1 2 0 [x0, x1]).shape := by
    rw [hshape]
    simpa [prodShape] using hidx
  rw [valAt_of_lt _ _ hp]
  have hfull : shard * 2 ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hshard) (by decide)
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceAdd, Nat.mul_one, Nat.div_one, Nat.mod_one,
    hfull, Nat.ne_of_gt hshard, if_false]
  simp

set_option maxHeartbeats 500000 in
theorem chunkPrimDimN_dim1_two_valAt_2d
    (x : Tensor) (rows cols rank idx : Nat)
    (hcols : 0 < cols) (hrank : rank < 2)
    (hx : x.shape = [rows, cols * 2])
    (hidx : idx < rows * cols) :
    valAt (chunkPrimDimN 1 2 rank x) idx =
      valAt x (idx / cols * (cols * 2) + rank * cols + idx % cols) := by
  have hchunkShape : (chunkPrimDimN 1 2 rank x).shape = [rows, cols] := by
    rw [chunkPrimDimN_shape 1 2 rank x [rows, cols * 2] hx (by decide)]
    simp [List.set, List.getD]
  have hp : idx < prodShape (chunkPrimDimN 1 2 rank x).shape := by
    rw [hchunkShape]
    simpa [prodShape] using hidx
  rw [valAt_of_lt _ _ hp]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceAdd, Nat.mul_one, Nat.div_one, Nat.mod_one,
    show (2 : Nat) ≠ 0 by decide, Nat.one_ne_zero, if_false]
  have hcols2 : cols * 2 / 2 = cols := by omega
  rw [hcols2]
  have hrmod : rank % 2 = rank := Nat.mod_eq_of_lt hrank
  rw [hrmod]
  simp [Nat.ne_of_gt hcols]
  rw [Nat.add_assoc]

set_option maxHeartbeats 500000 in
theorem chunkPrimDimN_dim1_two_allGather_2d
    (x0 x1 : Tensor) (rows cols rank : Nat)
    (hrows : 0 < rows) (hcols : 0 < cols) (hrank : rank < 2)
    (hx0 : x0.shape = [rows, cols]) (hx1 : x1.shape = [rows, cols]) :
    chunkPrimDimN 1 2 rank (allGatherPrimDimN 1 2 0 [x0, x1]) =
      [x0, x1].getD rank (zeroTensor [rows, cols]) := by
  have hhead : (([x0, x1].head?.map (fun t => t.shape)).getD []) =
      [rows, cols] := by simp [hx0]
  have hgshape : (allGatherPrimDimN 1 2 0 [x0, x1]).shape =
      [rows, cols * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, cols] hhead]
    simp [List.set, List.getD]
  have houtShape : (chunkPrimDimN 1 2 rank
      (allGatherPrimDimN 1 2 0 [x0, x1])).shape = [rows, cols] := by
    rw [chunkPrimDimN_shape 1 2 rank _ [rows, cols * 2] hgshape (by decide)]
    simp [List.set, List.getD]
  have hrhsShape : ([x0, x1].getD rank (zeroTensor [rows, cols])).shape =
      [rows, cols] := by
    rcases Nat.eq_zero_or_pos rank with hz | hp
    · rw [hz]; simp [List.getD, hx0]
    · have hr1 : rank = 1 := Nat.le_antisymm (Nat.le_of_lt_succ (by simpa using hrank)) hp
      rw [hr1]; simp [List.getD, hx1]
  apply Tensor.ext
  · rw [houtShape, hrhsShape]
  · intro idx hidx
    rw [houtShape] at hidx
    have hbound : idx < rows * cols := by simpa [prodShape] using hidx
    rw [chunkPrimDimN_dim1_two_valAt_2d _ rows cols rank idx
      hcols hrank hgshape hbound]
    rw [allGatherPrimDimN_dim1_two_valAt_2d x0 x1 rows cols
      (idx / cols * (cols * 2) + rank * cols + idx % cols)
      hrows hcols hx0 hx1 (by
        have hrow : idx / cols < rows :=
          Nat.div_lt_iff_lt_mul hcols |>.mpr hbound
        have hcol : idx % cols < cols := Nat.mod_lt _ hcols
        nlinarith)]
    have hrowDiv : (idx / cols * (cols * 2) + rank * cols + idx % cols) /
        (cols * 2) = idx / cols := by
      have hinner : rank * cols + idx % cols < cols * 2 := by
        have hcol := Nat.mod_lt idx hcols
        nlinarith
      rw [show idx / cols * (cols * 2) + rank * cols + idx % cols =
        (rank * cols + idx % cols) + (cols * 2) * (idx / cols) by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hinner,
        Nat.zero_add]
    have hmodFull : (idx / cols * (cols * 2) + rank * cols + idx % cols) %
        (cols * 2) = rank * cols + idx % cols := by
      have hinner : rank * cols + idx % cols < cols * 2 := by
        have hcol := Nat.mod_lt idx hcols
        nlinarith
      rw [show idx / cols * (cols * 2) + rank * cols + idx % cols =
        (rank * cols + idx % cols) + (cols * 2) * (idx / cols) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hinner]
    have hrankDiv : (rank * cols + idx % cols) / cols = rank := by
      rw [show rank * cols + idx % cols = idx % cols + cols * rank by ring,
        Nat.add_mul_div_left _ _ hcols, Nat.div_eq_of_lt (Nat.mod_lt _ hcols),
        Nat.zero_add]
    have hcolMod : (rank * cols + idx % cols) % cols = idx % cols := by
      rw [show rank * cols + idx % cols = idx % cols + cols * rank by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ hcols)]
    rw [hrowDiv, hmodFull, hrankDiv, hcolMod]
    have hlocal : idx / cols * cols + idx % cols = idx := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod idx cols)
    rw [hlocal]

set_option maxHeartbeats 500000 in
theorem fw_linear_dim1_two_allReduce_2d
    (x0 x1 w0 w1 : Tensor) (rows feature output : Nat)
    (hrows : 0 < rows) (hfeature : 0 < feature) (houtput : 0 < output)
    (hx0 : x0.shape = [rows, feature]) (hx1 : x1.shape = [rows, feature])
    (hw0 : w0.shape = [output, feature]) (hw1 : w1.shape = [output, feature]) :
    fw_linear (allGatherPrimDimN 1 2 0 [x0, x1])
      (allGatherPrimDimN 1 2 0 [w0, w1]) =
    allReducePrim 2 0 [fw_linear x0 w0, fw_linear x1 w1] := by
  have hxHead : (([x0, x1].head?.map (fun t => t.shape)).getD []) =
      [rows, feature] := by simp [hx0]
  have hwHead : (([w0, w1].head?.map (fun t => t.shape)).getD []) =
      [output, feature] := by simp [hw0]
  have hxShape : (allGatherPrimDimN 1 2 0 [x0, x1]).shape =
      [rows, 2 * feature] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, feature] hxHead]
    simp [List.set, List.getD, Nat.mul_comm]
  have hwGather := allGatherPrimDimN_1_eq_allGatherPrim_2d
    2 [w0, w1] output feature hwHead hfeature (by decide)
  have hmain := fw_linear_allGather_eq_allReduce_fw_linear_chunk
    2 rows (2 * feature) output feature
    (allGatherPrimDimN 1 2 0 [x0, x1]) [w0, w1]
    hxShape rfl (by simp)
    (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hw0
      · exact hw1)
    (by decide) hfeature
  have hchunk0 := chunkPrim_allGatherPrimDimN_cancel_2d
    2 0 rows feature [x0, x1] (by simp)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hx0
      · exact hx1)
    (by decide) hfeature (by decide)
  have hchunk1 := chunkPrim_allGatherPrimDimN_cancel_2d
    2 1 rows feature [x0, x1] (by simp)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hx0
      · exact hx1)
    (by decide) hfeature (by decide)
  rw [hwGather]
  rw [hmain]
  change allReducePrim 2 0
    [fw_linear (chunkPrim 2 0 (allGatherPrimDimN 1 2 0 [x0, x1])) w0,
     fw_linear (chunkPrim 2 1 (allGatherPrimDimN 1 2 0 [x0, x1])) w1] =
    allReducePrim 2 0 [fw_linear x0 w0, fw_linear x1 w1]
  rw [hchunk0, hchunk1]
  rfl

set_option maxHeartbeats 500000 in
theorem fw_swiglu_allGatherDim1_two_2d
    (g0 g1 u0 u1 : Tensor) (rows shard : Nat)
    (hrows : 0 < rows) (hshard : 0 < shard)
    (hg0 : g0.shape = [rows, shard]) (hg1 : g1.shape = [rows, shard])
    (hu0 : u0.shape = [rows, shard]) (hu1 : u1.shape = [rows, shard]) :
    fw_swiglu (allGatherPrimDimN 1 2 0 [g0, g1])
      (allGatherPrimDimN 1 2 0 [u0, u1]) =
    allGatherPrimDimN 1 2 0 [fw_swiglu g0 u0, fw_swiglu g1 u1] := by
  have hheadG : (([g0, g1].head?.map (fun t => t.shape)).getD []) =
      [rows, shard] := by simp [hg0]
  have hheadU : (([u0, u1].head?.map (fun t => t.shape)).getD []) =
      [rows, shard] := by simp [hu0]
  have hgShape : (allGatherPrimDimN 1 2 0 [g0, g1]).shape =
      [rows, shard * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, shard] hheadG]
    simp [List.set, List.getD]
  have huShape : (allGatherPrimDimN 1 2 0 [u0, u1]).shape =
      [rows, shard * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, shard] hheadU]
    simp [List.set, List.getD]
  have hlocal0 : (fw_swiglu g0 u0).shape = [rows, shard] := by
    unfold fw_swiglu Tensor.mkShape
    exact hu0
  have hlocal1 : (fw_swiglu g1 u1).shape = [rows, shard] := by
    unfold fw_swiglu Tensor.mkShape
    exact hu1
  have hheadOut : (([fw_swiglu g0 u0, fw_swiglu g1 u1].head?.map
      (fun t => t.shape)).getD []) = [rows, shard] := by simp [hlocal0]
  have houtShape : (allGatherPrimDimN 1 2 0
      [fw_swiglu g0 u0, fw_swiglu g1 u1]).shape = [rows, shard * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, shard] hheadOut]
    simp [List.set, List.getD]
  apply Tensor.ext
  · change (allGatherPrimDimN 1 2 0 [u0, u1]).shape =
      (allGatherPrimDimN 1 2 0 [fw_swiglu g0 u0, fw_swiglu g1 u1]).shape
    rw [huShape, houtShape]
  · intro idx hidx
    have hLshape : (fw_swiglu (allGatherPrimDimN 1 2 0 [g0, g1])
        (allGatherPrimDimN 1 2 0 [u0, u1])).shape = [rows, shard * 2] := by
      unfold fw_swiglu Tensor.mkShape
      exact huShape
    have hbound : idx < rows * (shard * 2) := by
      rw [hLshape] at hidx
      simpa [prodShape] using hidx
    have hrank : (idx % (shard * 2)) / shard < 2 := by
      apply (Nat.div_lt_iff_lt_mul hshard).mpr
      have hm := Nat.mod_lt idx (by omega : 0 < shard * 2)
      simpa [Nat.mul_comm] using hm
    have hlocal : idx / (shard * 2) * shard +
        idx % (shard * 2) % shard < rows * shard := by
      have hrow : idx / (shard * 2) < rows :=
        Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by simpa [Nat.mul_assoc] using hbound)
      have hcol : idx % (shard * 2) % shard < shard := Nat.mod_lt _ hshard
      calc
        idx / (shard * 2) * shard + idx % (shard * 2) % shard <
            idx / (shard * 2) * shard + shard := Nat.add_lt_add_left hcol _
        _ = (idx / (shard * 2) + 1) * shard := by simp [Nat.add_mul]
        _ ≤ rows * shard := Nat.mul_le_mul_right shard (Nat.succ_le_iff.mpr hrow)
    have hswigVal : valAt (fw_swiglu
        (allGatherPrimDimN 1 2 0 [g0, g1])
        (allGatherPrimDimN 1 2 0 [u0, u1])) idx =
        siluScalar (valAt (allGatherPrimDimN 1 2 0 [g0, g1]) idx) *
          valAt (allGatherPrimDimN 1 2 0 [u0, u1]) idx := by
      have hp : idx < prodShape (allGatherPrimDimN 1 2 0 [u0, u1]).shape := by
        rw [huShape]
        simpa [prodShape] using hbound
      unfold fw_swiglu
      rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hp)]
      rfl
    rw [hswigVal]
    rw [allGatherPrimDimN_dim1_two_valAt_2d g0 g1 rows shard idx
      hrows hshard hg0 hg1 hbound]
    rw [allGatherPrimDimN_dim1_two_valAt_2d u0 u1 rows shard idx
      hrows hshard hu0 hu1 hbound]
    rw [allGatherPrimDimN_dim1_two_valAt_2d
      (fw_swiglu g0 u0) (fw_swiglu g1 u1) rows shard idx
      hrows hshard hlocal0 hlocal1 hbound]
    have hrankCases : (idx % (shard * 2)) / shard = 0 ∨
        (idx % (shard * 2)) / shard = 1 := by
      rcases Nat.eq_zero_or_pos ((idx % (shard * 2)) / shard) with hz | hp
      · exact Or.inl hz
      · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ (by simpa using hrank)) hp)
    have hsimple : idx / (shard * 2) * shard + idx % shard < rows * shard := by
      have hrow : idx / (shard * 2) < rows :=
        Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by simpa [Nat.mul_assoc] using hbound)
      have hcol : idx % shard < shard := Nat.mod_lt _ hshard
      calc
        idx / (shard * 2) * shard + idx % shard <
            idx / (shard * 2) * shard + shard := Nat.add_lt_add_left hcol _
        _ = (idx / (shard * 2) + 1) * shard := by simp [Nat.add_mul]
        _ ≤ rows * shard := Nat.mul_le_mul_right shard (Nat.succ_le_iff.mpr hrow)
    have hpSimple : idx / (shard * 2) * shard + idx % shard <
        prodShape [rows, shard] := by simpa [prodShape] using hsimple
    rcases hrankCases with hr | hr <;> rw [hr] <;>
      simp [List.getD, List.getElem?_cons_zero, Option.getD_some,
        fw_swiglu, Tensor.mkShape, valAt, hg0, hg1, hu0, hu1, hpSimple]

set_option maxHeartbeats 500000 in
theorem fw_linear_2d_weight_allGather_dim0_two
    (x w0 w1 : Tensor) (rows input output : Nat)
    (hrows : 0 < rows) (hinput : 0 < input) (houtput : 0 < output)
    (hx : x.shape = [rows, input])
    (hw0 : w0.shape = [output, input])
    (hw1 : w1.shape = [output, input]) :
    fw_linear x (allGatherPrimDimN 0 2 0 [w0, w1]) =
      allGatherPrimDimN 1 2 0 [fw_linear x w0, fw_linear x w1] := by
  have hheadW : (([w0, w1].head?.map (fun t => t.shape)).getD []) =
      [output, input] := by simp [hw0]
  have hWshape : (allGatherPrimDimN 0 2 0 [w0, w1]).shape =
      [output * 2, input] := by
    rw [allGatherPrimDimN_shape 0 2 _ [output, input] hheadW]
    simp [List.set, List.getD]
  have hlin0 : (fw_linear x w0).shape = [rows, output] := by
    rw [fw_linear_is_matmul rows input output x w0 hx hw0]
    rfl
  have hlin1 : (fw_linear x w1).shape = [rows, output] := by
    rw [fw_linear_is_matmul rows input output x w1 hx hw1]
    rfl
  have hheadOut : (([fw_linear x w0, fw_linear x w1].head?.map
      (fun t => t.shape)).getD []) = [rows, output] := by simp [hlin0]
  have hRshape : (allGatherPrimDimN 1 2 0
      [fw_linear x w0, fw_linear x w1]).shape = [rows, output * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [rows, output] hheadOut]
    simp [List.set, List.getD]
  have hLshape : (fw_linear x (allGatherPrimDimN 0 2 0 [w0, w1])).shape =
      [rows, output * 2] := by
    rw [fw_linear_is_matmul rows input (output * 2) x _ hx hWshape]
    rfl
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hbound : idx < rows * (output * 2) := by
      simpa [prodShape] using hidx
    set row := idx / (output * 2) with hrowDef
    set col := idx % (output * 2) with hcolDef
    set rank := col / output with hrankDef
    set localCol := col % output with hlocalDef
    have hrow : row < rows := by
      rw [hrowDef, Nat.div_lt_iff_lt_mul (by omega)]
      exact hbound
    have hcol : col < output * 2 := by
      rw [hcolDef]
      exact Nat.mod_lt _ (by omega)
    have hrank : rank < 2 := by
      rw [hrankDef, Nat.div_lt_iff_lt_mul houtput]
      simpa [Nat.mul_comm] using hcol
    have hlocal : localCol < output := by
      rw [hlocalDef]
      exact Nat.mod_lt _ houtput
    have hcolEq : rank * output + localCol = col := by
      simpa [hrankDef, hlocalDef, Nat.mul_comm] using Nat.div_add_mod col output
    have hinner : rank * output + localCol < output * 2 := by
      rw [hcolEq]
      exact hcol
    have hdivFull : (row * (output * 2) + (rank * output + localCol)) /
        (output * 2) = row := by
      rw [show row * (output * 2) + (rank * output + localCol) =
        (rank * output + localCol) + (output * 2) * row by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hinner,
        Nat.zero_add]
    have hmodFull : (row * (output * 2) + (rank * output + localCol)) %
        (output * 2) = rank * output + localCol := by
      rw [show row * (output * 2) + (rank * output + localCol) =
        (rank * output + localCol) + (output * 2) * row by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hinner]
    have hdivOutput : (rank * output + localCol) / output = rank := by
      rw [show rank * output + localCol = localCol + output * rank by ring,
        Nat.add_mul_div_left _ _ houtput, Nat.div_eq_of_lt hlocal,
        Nat.zero_add]
    have hmodOutput : (rank * output + localCol) % output = localCol := by
      rw [show rank * output + localCol = localCol + output * rank by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlocal]
    have hidxEq : idx = row * (output * 2) + (rank * output + localCol) := by
      calc
        idx = row * (output * 2) + col := by
          simpa [row, col, Nat.mul_comm] using
            (Nat.div_add_mod idx (output * 2)).symm
        _ = _ := by rw [hcolEq]
    have hrankCases : rank = 0 ∨ rank = 1 := by
      rcases Nat.eq_zero_or_pos rank with hz | hp
      · exact Or.inl hz
      · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ (by simpa using hrank)) hp)
    rw [hidxEq]
    rw [fw_linear_2d_valAt rows input (output * 2) x
      (allGatherPrimDimN 0 2 0 [w0, w1]) hx hWshape row hrow
      (rank * output + localCol) (by rw [hcolEq]; exact hcol)]
    rw [allGatherPrimDimN_dim1_two_valAt_2d
      (fw_linear x w0) (fw_linear x w1) rows output
      (row * (output * 2) + (rank * output + localCol))
      hrows houtput hlin0 hlin1 (by
        rw [← hidxEq]
        exact hbound)]
    rw [hmodFull, hdivFull, hdivOutput, hmodOutput]
    rcases hrankCases with hr0 | hr1
    · rw [hr0]
      simp only [Nat.zero_mul, Nat.zero_add]
      simp only [List.getD_cons_zero]
      rw [fw_linear_2d_valAt rows input output x w0 hx hw0 row hrow localCol hlocal]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < input := Finset.mem_range.mp hj
      have hwval := allGatherPrimDimN_dim0_2d_valAt [w0, w1] 2 output input
        0 localCol j (by decide) houtput hinput (by decide) hlocal hj' hheadW
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero] at hwval
      rw [hwval]
    · rw [hr1]
      simp only [Nat.one_mul]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.reduceSub]
      rw [fw_linear_2d_valAt rows input output x w1 hx hw1 row hrow localCol hlocal]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < input := Finset.mem_range.mp hj
      have hwval := allGatherPrimDimN_dim0_2d_valAt [w0, w1] 2 output input
        1 localCol j (by decide) houtput hinput (by decide) hlocal hj' hheadW
      simp only [Nat.one_mul, List.getD_cons_succ, List.getD_cons_zero] at hwval
      rw [hwval]

end TrainVerify.Denote
