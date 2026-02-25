/- Goal: 12 (tensor id: 110)
   SM: FW_matmul(104, 109) → 110
   PM: AllToAllPrimWithDims(256-259, idim=3, odim=0) → 348-351,
       FW_matmul per rank → 352-355
   Fix: AllToAllPrim nodes need params := [3, 0] for correct redistribution.
-/
import denote.attn.GeneratedData
import denote.attn.Common

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.Common

namespace TrainVerify.Denote.GeneratedGoals

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

def sm_goal_12 : GraphDecl := by
  refine { numRanks := 1, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.FW_matmul", ins := [104, 109], outs := [110] },
  ]

def pm_goal_12 : GraphDecl := by
  refine { numRanks := 4, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.AllToAllPrim", ins := [256, 257, 258, 259], outs := [348], params := [3, 0] },
    { rank := 1, op := "OpName.AllToAllPrim", ins := [256, 257, 258, 259], outs := [349], params := [3, 0] },
    { rank := 2, op := "OpName.AllToAllPrim", ins := [256, 257, 258, 259], outs := [350], params := [3, 0] },
    { rank := 3, op := "OpName.AllToAllPrim", ins := [256, 257, 258, 259], outs := [351], params := [3, 0] },
    { rank := 0, op := "OpName.FW_matmul", ins := [348, 328], outs := [352] },
    { rank := 1, op := "OpName.FW_matmul", ins := [349, 329], outs := [353] },
    { rank := 2, op := "OpName.FW_matmul", ins := [350, 330], outs := [354] },
    { rank := 3, op := "OpName.FW_matmul", ins := [351, 331], outs := [355] },
  ]

def sm_goal_12InitShapes : List (Tid × Shape) := [
  (104, [16, 8, 64, 16]),
  (109, [16, 8, 16, 64]),
]

def sm_goal_12InitEnv : ShapeEnv := shapeEnvOfList sm_goal_12InitShapes

def pm_goal_12InitShapes : List (Tid × Shape) := [
  (256, [16, 8, 64, 4]),
  (257, [16, 8, 64, 4]),
  (258, [16, 8, 64, 4]),
  (259, [16, 8, 64, 4]),
  (328, [4, 8, 16, 64]),
  (329, [4, 8, 16, 64]),
  (330, [4, 8, 16, 64]),
  (331, [4, 8, 16, 64]),
]

def pm_goal_12InitEnv : ShapeEnv := shapeEnvOfList pm_goal_12InitShapes

def goal_12_cut_initGoals : List LineageGoal := initGoals ++ goal_12_prereqs

def goal_12_stmt_cut : Prop :=
  CoarseLineageHoldsWithInit sm_goal_12 pm_goal_12 goal_12 sm_goal_12InitEnv pm_goal_12InitEnv goal_12_cut_initGoals

private theorem batchedMatmul_4d_shape (x y : Tensor) (d0 d1 n k m : Nat)
    (hx : x.shape = [d0, d1, n, k]) (hy : y.shape = [d0, d1, k, m]) :
    (batchedMatmul x y).shape = [d0, d1, n, m] := by
  unfold batchedMatmul; rw [hx, hy]; simp [Tensor.mkShape]

/-! ## Helper A: valAt of allGatherPrimDimN 0 4 for shard shape [4,8,64,64] -/
-- allGatherPrimDimN valAt for [4,8,64,64] requires simp on complex gather expression
set_option maxHeartbeats 1600000 in
private lemma valAt_allGather_out
    (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 8, 64, 64])
    (hidx : idx < 524288) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 524288 / 32768 / 4) (zeroTensor [4, 8, 64, 64]))
      ((idx / 32768 % 4) * 32768 + idx % 32768) := by
  have h4x4 : (4 : Nat) * 4 = 16 := by norm_num
  have h4x32768 : (4 : Nat) * 32768 = 131072 := by norm_num
  have h16x32768 : (16 : Nat) * 32768 = 524288 := by norm_num
  have h_ps_out : prodShape [16, 8, 64, 64] = 524288 := by simp [prodShape]
  have hmm : idx % 524288 = idx := Nat.mod_eq_of_lt hidx
  have hdv : idx / 524288 = 0 := Nat.div_eq_of_lt hidx
  unfold allGatherPrimDimN
  rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps_out,
    List.set, List.getD, List.drop, List.foldl, List.length,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    h4x4, h4x32768, h16x32768, hmm, hdv, dif_pos hidx]

/-! ## Helper B: valAt of allGatherPrimDimN 0 4 for shard shape [4,8,16,64] -/
-- allGatherPrimDimN valAt for [4,8,16,64] requires simp on gather expression
set_option maxHeartbeats 1600000 in
private lemma valAt_allGather_Y
    (xs : List Tensor) (g : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 8, 16, 64])
    (hg : g < 131072) :
    valAt (allGatherPrimDimN 0 4 0 xs) g =
    valAt (xs.getD (g % 131072 / 8192 / 4) (zeroTensor [4, 8, 16, 64]))
      ((g / 8192 % 4) * 8192 + g % 8192) := by
  have h4x4 : (4 : Nat) * 4 = 16 := by norm_num
  have h4x8192 : (4 : Nat) * 8192 = 32768 := by norm_num
  have h16x8192 : (16 : Nat) * 8192 = 131072 := by norm_num
  have h_ps_out : prodShape [16, 8, 16, 64] = 131072 := by simp [prodShape]
  have hmm : g % 131072 = g := Nat.mod_eq_of_lt hg
  have hdv : g / 131072 = 0 := Nat.div_eq_of_lt hg
  unfold allGatherPrimDimN
  rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps_out,
    List.set, List.getD, List.drop, List.foldl, List.length,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    h4x4, h4x8192, h16x8192, hmm, hdv, dif_pos hg]

/-! ## Helper C: valAt of chunkPrimDimN 0 4 for shape [16,8,64,16] -/
-- chunkPrimDimN valAt requires unfolding and simp on index arithmetic
set_option maxHeartbeats 1600000 in
private lemma valAt_chunk_dim0_X (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 8, 64, 16])
    (hr : r < 4) (hidx : idx < 32768) :
    valAt (chunkPrimDimN 0 4 r x) idx = valAt x (r * 32768 + idx) := by
  have hps : prodShape x.shape = 131072 := by simp [hshape, prodShape]
  have hfi_bound : r * 32768 + idx < 131072 := by omega
  have hps2 : prodShape [4, 8, 64, 16] = 32768 := by simp [prodShape]
  have hchunk_shape : (chunkPrimDimN 0 4 r x).shape = [4, 8, 64, 16] := by
    simp [chunkPrimDimN, Tensor.mkShape, hshape]
  have hps_chunk : prodShape (chunkPrimDimN 0 4 r x).shape = 32768 := by
    rw [hchunk_shape]; exact hps2
  rw [valAt_of_lt _ _ (by rw [hps_chunk]; exact hidx)]
  rw [valAt_of_lt _ _ (by rw [hps]; exact hfi_bound)]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hshape, List.set, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none,
    List.take, List.drop, List.foldl, List.length,
    Nat.sub_zero]
  have : (16 : Nat) / 4 = 4 := by norm_num
  have : (4 : Nat) * (8 * 64 * 16) = 32768 := by norm_num
  have : (16 : Nat) * (8 * 64 * 16) = 131072 := by norm_num
  have : (8 : Nat) * 64 * 16 = 8192 := by norm_num
  have hne_4 : (4 : Nat) ≠ 0 := by omega
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_32768 : (32768 : Nat) ≠ 0 := by omega
  have hne_131072 : (131072 : Nat) ≠ 0 := by omega
  have h_4x8192 : (4 : Nat) * 8192 = 32768 := by norm_num
  simp only [*, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    Nat.zero_mul, Nat.mul_zero,
    dif_pos hfi_bound, if_neg, if_pos, ite_false, ite_true]
  have h0 : idx / 32768 = 0 := Nat.div_eq_of_lt hidx
  have hm : idx % 32768 = idx := Nat.mod_eq_of_lt hidx
  simp only [h0, hm, Nat.zero_mul, Nat.zero_add, Nat.mul_zero]
  rw [show r % 4 = r from Nat.mod_eq_of_lt hr]
  have heq : (r * 4 + idx / 8192) * 8192 + idx % 8192 = r * 32768 + idx := by omega
  rw [heq, valAt_of_lt _ _ (by rw [hps]; exact hfi_bound)]

/-! ## Helper D: valAt of batchedMatmul -/
-- batchedMatmul valAt requires unfolding match + List.reverse + simp
set_option maxHeartbeats 8000000 in
private lemma valAt_batchedMatmul_16 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [16, 8, 64, 16]) (hy : y.shape = [16, 8, 16, 64])
    (hidx : idx < 524288) :
    valAt (batchedMatmul x y) idx =
    ∑ l ∈ Finset.range 16,
      valAt x (idx / 4096 * 1024 + idx % 4096 / 64 * 16 + l) *
      valAt y (idx / 4096 * 1024 + l * 64 + idx % 64) := by
  cases x with | mk sx vx =>
  cases y with | mk sy vy =>
  simp only at hx hy
  subst hx; subst hy
  unfold batchedMatmul
  dsimp only [List.reverse, List.reverseAux, List.append]
  simp [valAt, Tensor.mkShape, prodShape, dif_pos hidx]

-- batchedMatmul valAt for chunk shapes [4,8,64,16] × [4,8,16,64]
set_option maxHeartbeats 8000000 in
private lemma valAt_batchedMatmul_4 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [4, 8, 64, 16]) (hy : y.shape = [4, 8, 16, 64])
    (hidx : idx < 131072) :
    valAt (batchedMatmul x y) idx =
    ∑ l ∈ Finset.range 16,
      valAt x (idx / 4096 * 1024 + idx % 4096 / 64 * 16 + l) *
      valAt y (idx / 4096 * 1024 + l * 64 + idx % 64) := by
  cases x with | mk sx vx =>
  cases y with | mk sy vy =>
  simp only at hx hy
  subst hx; subst hy
  unfold batchedMatmul
  dsimp only [List.reverse, List.reverseAux, List.append]
  simp [valAt, Tensor.mkShape, prodShape, dif_pos hidx]

/-! ## Main distribution: batchedMatmul distributes over dim-0 gather

For X of shape [16,8,64,16] and B0..B3 of shape [4,8,16,64]:
  batchedMatmul X (allGather₀ [B0,B1,B2,B3]) = allGather₀ [bM(chunk₀X, B0), ..., bM(chunk₃X, B3)]

This holds because dim 0 is a batch dimension for batchedMatmul: each batch
slice is computed independently, so splitting both inputs along dim 0 gives
independent subproblems.
-/

-- distribution proof requires Tensor.ext over 524288 indices with 4-way case split
set_option maxHeartbeats 8000000 in
private theorem batchedMatmul_gatherDim0_dist
    (X B0 B1 B2 B3 : Tensor)
    (hX : X.shape = [16, 8, 64, 16])
    (hB0 : B0.shape = [4, 8, 16, 64])
    (hB1 : B1.shape = [4, 8, 16, 64])
    (hB2 : B2.shape = [4, 8, 16, 64])
    (hB3 : B3.shape = [4, 8, 16, 64]) :
    batchedMatmul X (allGatherPrimDimN 0 4 0 [B0, B1, B2, B3]) =
    allGatherPrimDimN 0 4 0 [
      batchedMatmul (chunkPrimDimN 0 4 0 X) B0,
      batchedMatmul (chunkPrimDimN 0 4 1 X) B1,
      batchedMatmul (chunkPrimDimN 0 4 2 X) B2,
      batchedMatmul (chunkPrimDimN 0 4 3 X) B3] := by
  -- Shape setup
  have hheadB : (([B0, B1, B2, B3].head?.map (·.shape)).getD []) = [4, 8, 16, 64] := by
    simp [hB0]
  have hY_shape : (allGatherPrimDimN 0 4 0 [B0, B1, B2, B3]).shape = [16, 8, 16, 64] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hheadB]; simp [List.set, List.getD]
  have hLHS_shape : (batchedMatmul X (allGatherPrimDimN 0 4 0 [B0, B1, B2, B3])).shape =
      [16, 8, 64, 64] :=
    batchedMatmul_4d_shape _ _ 16 8 64 16 64 hX hY_shape
  have hcX : ∀ r, (chunkPrimDimN 0 4 r X).shape = [4, 8, 64, 16] := by
    intro r; simp [chunkPrimDimN, Tensor.mkShape, hX]
  have hbm0 : (batchedMatmul (chunkPrimDimN 0 4 0 X) B0).shape = [4, 8, 64, 64] :=
    batchedMatmul_4d_shape _ _ 4 8 64 16 64 (hcX 0) hB0
  have hheadBM : (([batchedMatmul (chunkPrimDimN 0 4 0 X) B0,
      batchedMatmul (chunkPrimDimN 0 4 1 X) B1,
      batchedMatmul (chunkPrimDimN 0 4 2 X) B2,
      batchedMatmul (chunkPrimDimN 0 4 3 X) B3].head?.map (·.shape)).getD []) =
      [4, 8, 64, 64] := by
    simp [hbm0]
  have hRHS_shape : (allGatherPrimDimN 0 4 0 [
      batchedMatmul (chunkPrimDimN 0 4 0 X) B0,
      batchedMatmul (chunkPrimDimN 0 4 1 X) B1,
      batchedMatmul (chunkPrimDimN 0 4 2 X) B2,
      batchedMatmul (chunkPrimDimN 0 4 3 X) B3]).shape = [16, 8, 64, 64] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hheadBM]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 524288 := by simpa [prodShape] using hidx
  -- LHS: unfold batchedMatmul
  rw [valAt_batchedMatmul_16 X _ idx hX hY_shape hidx']
  -- RHS: unfold allGather for output shape [4,8,64,64]
  rw [valAt_allGather_out _ idx hheadBM hidx']
   -- Simplify piece selector: idx % 524288 / 32768 / 4 = idx / 32768 / 4
  have hmm : idx % 524288 = idx := Nat.mod_eq_of_lt hidx'
  rw [hmm]
  -- Case split on piece = idx / 32768 / 4
  have hlocalIdx_lt : (idx / 32768 % 4) * 32768 + idx % 32768 < 131072 := by omega
  have hr_cases : idx / 32768 / 4 = 0 ∨ idx / 32768 / 4 = 1 ∨ idx / 32768 / 4 = 2 ∨ idx / 32768 / 4 = 3 := by omega
  rcases hr_cases with hr | hr | hr | hr <;> {
    simp only [hr, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none]
    -- RHS: unfold batchedMatmul of chunk and B_r
    rw [valAt_batchedMatmul_4 _ _
      ((idx / 32768 % 4) * 32768 + idx % 32768)
      (hcX _)
      (by first | exact hB0 | exact hB1 | exact hB2 | exact hB3)
      hlocalIdx_lt]
    -- Both sides are Σ l: show term-by-term equality
    apply Finset.sum_congr rfl
    intro l hl
    have hl16 : l < 16 := Finset.mem_range.mp hl
    -- X factor: rewrite chunk to valAt X (...)
    have hchunk_idx_bound : (idx / 32768 % 4 * 32768 + idx % 32768) / 4096 * 1024 +
      (idx / 32768 % 4 * 32768 + idx % 32768) % 4096 / 64 * 16 + l < 32768 := by omega
    rw [valAt_chunk_dim0_X X _ _ hX (by omega) hchunk_idx_bound]
    -- Y factor: rewrite allGather to valAt B_r (...)
    rw [valAt_allGather_Y [B0, B1, B2, B3] _ hheadB (by omega)]
    have hYmm : (idx / 4096 * 1024 + l * 64 + idx % 64) % 131072 = idx / 4096 * 1024 + l * 64 + idx % 64 := by
      apply Nat.mod_eq_of_lt; omega
    rw [hYmm]
    have hYpiece : (idx / 4096 * 1024 + l * 64 + idx % 64) / 8192 / 4 = idx / 32768 / 4 := by omega
    rw [hYpiece, hr]
    simp only [List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none]
    -- Both sides: valAt X (a) * valAt B_r (b)
    -- Show the indices match using congrArg (avoids congr recursion on dif)
    exact congrArg₂ HMul.hMul (congrArg (valAt X) (by omega)) (congrArg (valAt _) (by omega))
  }

/-! ## Main theorem -/

-- main theorem unfolds SM/PM graphs and applies distribution lemma
set_option maxHeartbeats 1600000 in
theorem prove_goal_12_cut : goal_12_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Extract prerequisites using initGoalHolds_sharded4
  have hInit104 : InitGoalHolds pm_goal_12.numRanks intermediateGoal_104 initSM initPM :=
    hInitGoals intermediateGoal_104 (by simp [goal_12_cut_initGoals, goal_12_prereqs, initGoals])
  have hInit109 : InitGoalHolds pm_goal_12.numRanks intermediateGoal_109 initSM initPM :=
    hInitGoals intermediateGoal_109 (by simp [goal_12_cut_initGoals, goal_12_prereqs, initGoals])
  have h104 := initGoalHolds_sharded4 4 intermediateGoal_104 104 256 257 258 259
    [16, 8, 64, 16] [16, 8, 64, 4] initSM initPM hInit104 rfl rfl rfl rfl
  obtain ⟨h104_sm_shape, h256_shape, h257_shape, h258_shape, h259_shape, h104_rec⟩ := h104
  have h109 := initGoalHolds_sharded4 4 intermediateGoal_109 109 328 329 330 331
    [16, 8, 16, 64] [4, 8, 16, 64] initSM initPM hInit109 rfl rfl rfl rfl
  obtain ⟨h109_sm_shape, h328_shape, h329_shape, h330_shape, h331_shape, h109_rec⟩ := h109
  -- Reconstructions → allGatherPrimDimN
  have h104_ag : initSM 104 = allGatherPrimDimN 3 4 0
      [initPM 256, initPM 257, initPM 258, initPM 259] := by
    rw [h104_rec]; apply reconstructWithDim_cons_cons_nonscalar
    rw [h256_shape]; decide
  have h109_ag : initSM 109 = allGatherPrimDimN 0 4 0
      [initPM 328, initPM 329, initPM 330, initPM 331] := by
    rw [h109_rec]; apply reconstructWithDim_cons_cons_nonscalar
    rw [h328_shape]; decide
  -- SM computation
  have hsm : (denoteGraph sm_goal_12 initSM) 110 = batchedMatmul (initSM 104) (initSM 109) := by
    simp only [sm_goal_12, denoteGraph, List.foldl, applyNode, evalOp, storeSet, fw_matmul,
               List.map, List.find?, List.zip, List.zipWith]
    split <;> simp_all
  -- PM computation: unfold the graph for each output
  have hpm352 : (denoteGraph pm_goal_12 initPM) 352 =
      batchedMatmul (allToAllPrimWithDims 4 0 [initPM 256, initPM 257, initPM 258, initPM 259] 3 0) (initPM 328) := by
    simp [pm_goal_12, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrimWithDims, fw_matmul]
  have hpm353 : (denoteGraph pm_goal_12 initPM) 353 =
      batchedMatmul (allToAllPrimWithDims 4 1 [initPM 256, initPM 257, initPM 258, initPM 259] 3 0) (initPM 329) := by
    simp [pm_goal_12, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrimWithDims, fw_matmul]
  have hpm354 : (denoteGraph pm_goal_12 initPM) 354 =
      batchedMatmul (allToAllPrimWithDims 4 2 [initPM 256, initPM 257, initPM 258, initPM 259] 3 0) (initPM 330) := by
    simp [pm_goal_12, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrimWithDims, fw_matmul]
  have hpm355 : (denoteGraph pm_goal_12 initPM) 355 =
      batchedMatmul (allToAllPrimWithDims 4 3 [initPM 256, initPM 257, initPM 258, initPM 259] 3 0) (initPM 331) := by
    simp [pm_goal_12, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrimWithDims, fw_matmul]
  -- Relate allToAllPrimWithDims to chunkPrimDimN of full tensor
  have hata_eq : ∀ r, allToAllPrimWithDims 4 r
      [initPM 256, initPM 257, initPM 258, initPM 259] 3 0 =
      chunkPrimDimN 0 4 r (initSM 104) := by
    intro r; rw [h104_ag]; rfl
  rw [hata_eq 0] at hpm352; rw [hata_eq 1] at hpm353
  rw [hata_eq 2] at hpm354; rw [hata_eq 3] at hpm355
  -- Unfold the goal
  dsimp only [goal_12_stmt_cut, CoarseLineageHoldsWithInit, goal_12] at *
  simp only [List.map, Piece.tid]
  rw [hsm, hpm352, hpm353, hpm354, hpm355]
  -- The reconstruction for the output
  have hcX : ∀ r, (chunkPrimDimN 0 4 r (initSM 104)).shape = [4, 8, 64, 16] := by
    intro r; simp [chunkPrimDimN, Tensor.mkShape, h104_sm_shape]
  have hpiece0_shape : (batchedMatmul (chunkPrimDimN 0 4 0 (initSM 104)) (initPM 328)).shape =
      [4, 8, 64, 64] :=
    batchedMatmul_4d_shape _ _ 4 8 64 16 64 (hcX 0) h328_shape
  have hrecon : reconstructWithDim 0 4 0
      [batchedMatmul (chunkPrimDimN 0 4 0 (initSM 104)) (initPM 328),
       batchedMatmul (chunkPrimDimN 0 4 1 (initSM 104)) (initPM 329),
       batchedMatmul (chunkPrimDimN 0 4 2 (initSM 104)) (initPM 330),
       batchedMatmul (chunkPrimDimN 0 4 3 (initSM 104)) (initPM 331)] =
    allGatherPrimDimN 0 4 0
      [batchedMatmul (chunkPrimDimN 0 4 0 (initSM 104)) (initPM 328),
       batchedMatmul (chunkPrimDimN 0 4 1 (initSM 104)) (initPM 329),
       batchedMatmul (chunkPrimDimN 0 4 2 (initSM 104)) (initPM 330),
       batchedMatmul (chunkPrimDimN 0 4 3 (initSM 104)) (initPM 331)] := by
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hpiece0_shape]; decide
  simp only [show pm_goal_12.numRanks = 4 from rfl]
  rw [hrecon]
  refine ⟨?_, ?_, ?_⟩
  · -- SM output shape = [16, 8, 64, 64]
    exact batchedMatmul_4d_shape _ _ 16 8 64 16 64 h104_sm_shape h109_sm_shape
  · -- PM output shapes
    simp only [batchedMatmul_4d_shape _ _ 4 8 64 16 64 (hcX 0) h328_shape,
      batchedMatmul_4d_shape _ _ 4 8 64 16 64 (hcX 1) h329_shape,
      batchedMatmul_4d_shape _ _ 4 8 64 16 64 (hcX 2) h330_shape,
      batchedMatmul_4d_shape _ _ 4 8 64 16 64 (hcX 3) h331_shape]
  · -- Value equality: SM result = allGather of PM results
    rw [h109_ag]
    exact batchedMatmul_gatherDim0_dist (initSM 104)
      (initPM 328) (initPM 329) (initPM 330) (initPM 331)
      h104_sm_shape h328_shape h329_shape h330_shape h331_shape

end TrainVerify.Denote.GeneratedGoals
