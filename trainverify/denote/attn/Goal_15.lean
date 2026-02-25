/- Goal: 15 (tensor id: 113)
   SM: FW_matmul(112, 108) → 113
   PM: AllToAll(304-307, params [3,1])→424-427, AllToAllPrim(400-403)→420-423,
       FW_matmul per rank → 428-431
   goal_15: per-rank matmul outputs 428-431, gatherDim=1
   Key: batchedMatmul distributes over batch dim 1
-/
import denote.attn.Common

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.Common

namespace TrainVerify.Denote.GeneratedGoals

-- ===== Graph declarations =====

def sm_goal_15 : GraphDecl := by
  refine { numRanks := 1, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.FW_matmul", ins := [112, 108], outs := [113] },
  ]

set_option linter.style.longLine false in
def pm_goal_15 : GraphDecl := by
  refine { numRanks := 4, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.AllToAllPrim", ins := [304, 305, 306, 307], outs := [424], params := [3, 1] },
    { rank := 0, op := "OpName.AllToAllPrim", ins := [400, 401, 402, 403], outs := [420] },
    { rank := 1, op := "OpName.AllToAllPrim", ins := [304, 305, 306, 307], outs := [425], params := [3, 1] },
    { rank := 1, op := "OpName.AllToAllPrim", ins := [400, 401, 402, 403], outs := [421] },
    { rank := 2, op := "OpName.AllToAllPrim", ins := [304, 305, 306, 307], outs := [426], params := [3, 1] },
    { rank := 2, op := "OpName.AllToAllPrim", ins := [400, 401, 402, 403], outs := [422] },
    { rank := 3, op := "OpName.AllToAllPrim", ins := [304, 305, 306, 307], outs := [427], params := [3, 1] },
    { rank := 3, op := "OpName.AllToAllPrim", ins := [400, 401, 402, 403], outs := [423] },
    { rank := 0, op := "OpName.FW_matmul", ins := [420, 424], outs := [428] },
    { rank := 1, op := "OpName.FW_matmul", ins := [421, 425], outs := [429] },
    { rank := 2, op := "OpName.FW_matmul", ins := [422, 426], outs := [430] },
    { rank := 3, op := "OpName.FW_matmul", ins := [423, 427], outs := [431] },
  ]

def sm_goal_15InitShapes : List (Tid × Shape) := [
  (108, [16, 8, 64, 16]),
  (112, [16, 8, 64, 64]),
]

def sm_goal_15InitEnv : ShapeEnv := shapeEnvOfList sm_goal_15InitShapes

def pm_goal_15InitShapes : List (Tid × Shape) := [
  (304, [16, 8, 64, 4]),
  (305, [16, 8, 64, 4]),
  (306, [16, 8, 64, 4]),
  (307, [16, 8, 64, 4]),
  (400, [16, 2, 64, 64]),
  (401, [16, 2, 64, 64]),
  (402, [16, 2, 64, 64]),
  (403, [16, 2, 64, 64]),
]

def pm_goal_15InitEnv : ShapeEnv := shapeEnvOfList pm_goal_15InitShapes

def goal_15_cut_initGoals : List LineageGoal := initGoals ++ goal_15_prereqs

def goal_15_stmt_cut : Prop :=
  CoarseLineageHoldsWithInit sm_goal_15 pm_goal_15 goal_15
    sm_goal_15InitEnv pm_goal_15InitEnv goal_15_cut_initGoals

-- ===== Helper lemmas =====

-- batchedMatmul shape for 4D tensors
private theorem batchedMatmul_4d_shape (x y : Tensor) (d0 d1 n k m : Nat)
    (hx : x.shape = [d0, d1, n, k]) (hy : y.shape = [d0, d1, k, m]) :
    (batchedMatmul x y).shape = [d0, d1, n, m] := by
  unfold batchedMatmul
  rw [hx, hy]
  simp [Tensor.mkShape]

-- allToAllPrim for 4D: just returns xs[rank] (non-2D fallback)
private theorem allToAllPrim_4d_eq (numParts rank : Nat) (xs : List Tensor) (xr : Tensor)
    (hget : xs[rank]? = some xr) (a b c d : Nat) (hsh : xr.shape = [a, b, c, d]) :
    allToAllPrim numParts rank xs = xr := by
  simp [allToAllPrim, hget, hsh]

-- valAt of allGatherPrimDimN 1 4 with piece shape [16, 2, 64, 64]
set_option linter.style.longLine false in
private theorem valAt_gather1_16_2_64_64
    (xs : List Tensor)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 2, 64, 64])
    (idx : Nat) (hidx : idx < 524288) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
    valAt (xs.getD (idx % 32768 / 4096 / 2) (zeroTensor [16, 2, 64, 64]))
      (idx / 32768 * 8192 + idx % 32768 / 4096 % 2 * 4096 + idx % 4096) := by
  have h_ps : prodShape [16, 8, 64, 64] = 524288 := by decide
  have h2x4 : (2 : Nat) * 4 = 8 := by norm_num
  have h2x4096 : (2 : Nat) * 4096 = 8192 := by norm_num
  have h8x4096 : (8 : Nat) * 4096 = 32768 := by norm_num
  have h64x64x1 : (64 : Nat) * (64 * 1) = 4096 := by norm_num
  have h1x64 : (1 : Nat) * 64 = 64 := by norm_num
  unfold allGatherPrimDimN
  rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps, h2x4, h2x4096, h8x4096, h64x64x1, h1x64,
    List.getD, List.drop, List.foldl, List.length, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, dif_pos hidx]
-- valAt of allGatherPrimDimN 1 4 with piece shape [16, 2, 64, 16]
set_option linter.style.longLine false in
private theorem valAt_gather1_16_2_64_16
    (xs : List Tensor)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 2, 64, 16])
    (idx : Nat) (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
    valAt (xs.getD (idx % 8192 / 1024 / 2) (zeroTensor [16, 2, 64, 16]))
      (idx / 8192 * 2048 + idx % 8192 / 1024 % 2 * 1024 + idx % 1024) := by
  have h_ps : prodShape [16, 8, 64, 16] = 131072 := by decide
  have h2x4 : (2 : Nat) * 4 = 8 := by norm_num
  have h2x1024 : (2 : Nat) * 1024 = 2048 := by norm_num
  have h8x1024 : (8 : Nat) * 1024 = 8192 := by norm_num
  have h64x16x1 : (64 : Nat) * (16 * 1) = 1024 := by norm_num
  have h1x64 : (1 : Nat) * 64 = 64 := by norm_num
  unfold allGatherPrimDimN
  rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps, h2x4, h2x1024, h8x1024, h64x16x1, h1x64,
    List.getD, List.drop, List.foldl, List.length,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    dif_pos hidx]

-- valAt of chunkPrimDimN 1 4 for shape [16, 8, 64, 16]
set_option linter.style.longLine false in
private theorem valAt_chunk1_16_8_64_16
    (x : Tensor) (hx : x.shape = [16, 8, 64, 16])
    (r idx : Nat) (hidx : idx < 32768) :
    valAt (chunkPrimDimN 1 4 r x) idx =
    valAt x (idx / 2048 * 8192 + (r % 4 * 2 + idx % 2048 / 1024) * 1024 + idx % 1024) := by
  have h_ps_chunk : prodShape [16, 2, 64, 16] = 32768 := by decide
  have h8div4 : (8 : Nat) / 4 = 2 := by norm_num
  have h2x1024 : (2 : Nat) * 1024 = 2048 := by norm_num
  have h8x1024 : (8 : Nat) * 1024 = 8192 := by norm_num
  have h64x16x1 : (64 : Nat) * (16 * 1) = 1024 := by norm_num
  have h1x64 : (1 : Nat) * 64 = 64 := by norm_num
  unfold chunkPrimDimN
  rw [hx]
  simp [valAt, Tensor.mkShape, h_ps_chunk, h8div4, h2x1024, h8x1024, h64x16x1, h1x64,
    List.getD, List.drop, List.foldl, List.length, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, dif_pos hidx]
-- valAt of batchedMatmul for shapes [16, d1, 64, 64] × [16, d1, 64, 16]
set_option linter.style.longLine false in
private theorem valAt_batchedMatmul_64_16
    (x y : Tensor) (d1 : Nat) (_hd1 : 0 < d1)
    (hx : x.shape = [16, d1, 64, 64]) (hy : y.shape = [16, d1, 64, 16])
    (idx : Nat) (hidx : idx < 16 * d1 * 64 * 16) :
    valAt (batchedMatmul x y) idx =
    ∑ l ∈ Finset.range 64,
      valAt x (idx / 1024 * 4096 + (idx % 1024) / 16 * 64 + l) *
      valAt y (idx / 1024 * 1024 + l * 16 + idx % 16) := by
  have hps : prodShape [16, d1, 64, 16] = 16 * d1 * 1024 := by
    simp [prodShape, List.foldl]; ring
  have hidx' : idx < 16 * d1 * 1024 := by omega
  unfold batchedMatmul
  rw [hx, hy]
  simp only [List.reverse, List.reverseAux]
  simp only [valAt, Tensor.mkShape, hps]
  rw [dif_pos hidx']
  simp only [show (64 : Nat) * 16 ≠ 0 from by omega, ↓reduceIte,
    show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) * 16 = 1024 from by norm_num,
    show (64 : Nat) * 64 = 4096 from by norm_num]
  simp_rw [show idx % 1024 % 16 = idx % 16 from by omega]

-- ===== Key commutativity lemma =====
-- batchedMatmul distributes over allGatherPrimDimN along batch dim 1
set_option linter.style.longLine false in
private theorem batchedMatmul_gather1_distrib
    (A0 A1 A2 A3 Y : Tensor)
    (hA0 : A0.shape = [16, 2, 64, 64]) (hA1 : A1.shape = [16, 2, 64, 64])
    (hA2 : A2.shape = [16, 2, 64, 64]) (hA3 : A3.shape = [16, 2, 64, 64])
    (hY : Y.shape = [16, 8, 64, 16]) :
    batchedMatmul (allGatherPrimDimN 1 4 0 [A0, A1, A2, A3]) Y =
    allGatherPrimDimN 1 4 0 [batchedMatmul A0 (chunkPrimDimN 1 4 0 Y),
                              batchedMatmul A1 (chunkPrimDimN 1 4 1 Y),
                              batchedMatmul A2 (chunkPrimDimN 1 4 2 Y),
                              batchedMatmul A3 (chunkPrimDimN 1 4 3 Y)] := by
  have hA_shape : (allGatherPrimDimN 1 4 0 [A0, A1, A2, A3]).shape = [16, 8, 64, 64] := by
    rw [allGatherPrimDimN_shape 1 4 _ [16, 2, 64, 64] (by simp [List.head?, Option.map, hA0])]
    decide
  have hLHS_shape := batchedMatmul_4d_shape _ _ 16 8 64 64 16 hA_shape hY
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r Y).shape = [16, 2, 64, 16] :=
    fun r => chunkPrimDimN_shape 1 4 r Y _ hY (by omega)
  have hhead_out : (([batchedMatmul A0 (chunkPrimDimN 1 4 0 Y),
      batchedMatmul A1 (chunkPrimDimN 1 4 1 Y),
      batchedMatmul A2 (chunkPrimDimN 1 4 2 Y),
      batchedMatmul A3 (chunkPrimDimN 1 4 3 Y)].head?.map (·.shape)).getD []) = [16, 2, 64, 16] := by
    simp [List.head?, Option.map, batchedMatmul_4d_shape _ _ 16 2 64 64 16 hA0 (hchunk_shape 0)]
  have hRHS_shape : (allGatherPrimDimN 1 4 0 [batchedMatmul A0 (chunkPrimDimN 1 4 0 Y),
      batchedMatmul A1 (chunkPrimDimN 1 4 1 Y),
      batchedMatmul A2 (chunkPrimDimN 1 4 2 Y),
      batchedMatmul A3 (chunkPrimDimN 1 4 3 Y)]).shape = [16, 8, 64, 16] := by
    rw [allGatherPrimDimN_shape 1 4 _ [16, 2, 64, 16] hhead_out]; decide
  apply Tensor.ext (hLHS_shape.symm ▸ hRHS_shape.symm ▸ rfl)
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 131072 := by simp [prodShape, List.foldl] at hidx; omega
  have hhead_A : (([A0, A1, A2, A3].head?.map (·.shape)).getD []) = [16, 2, 64, 64] := by
    simp [List.head?, Option.map, hA0]
  -- LHS: unfold batchedMatmul(gather1[A0..A3], Y)
  rw [valAt_batchedMatmul_64_16 _ Y 8 (by omega) hA_shape hY idx hidx']
  -- RHS: unfold gather1[matmul pieces]
  rw [valAt_gather1_16_2_64_16 _ hhead_out idx hidx']
  set r := idx % 8192 / 1024 / 2
  set localIdx := idx / 8192 * 2048 + idx % 8192 / 1024 % 2 * 1024 + idx % 1024
  have hr_lt : r < 4 := by omega
  have hlocalIdx_lt : localIdx < 32768 := by omega
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with hr | hr | hr | hr <;> (
    simp only [hr, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    rw [valAt_batchedMatmul_64_16 _ _ 2 (by omega) (by assumption) (hchunk_shape _) localIdx hlocalIdx_lt]
    apply Finset.sum_congr rfl; intro l hl
    simp only [Finset.mem_range] at hl
    -- Rewrite LHS: valAt(gather[A0..A3]) → valAt(piece)
    rw [valAt_gather1_16_2_64_64 _ hhead_A _ (by omega)]
    -- The gather piece index is complex; prove it equals r
    have h_piece : (idx / 1024 * 4096 + idx % 1024 / 16 * 64 + l) % 32768 / 4096 / 2 = r := by
      omega
    simp only [h_piece, hr, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    -- Rewrite RHS: valAt(chunk(Y)) → valAt(Y)
    rw [valAt_chunk1_16_8_64_16 Y hY _ _ (by omega)]
    -- Both sides: valAt A_r (idx_a) * valAt Y (idx_y) = valAt A_r (idx_a') * valAt Y (idx_y')
    exact congr (congrArg (· * ·) (congrArg (valAt _) (by omega)))
               (congrArg (valAt Y) (by omega))
  )
-- ===== Main theorem =====

set_option linter.style.longLine false in
theorem prove_goal_15_cut : goal_15_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Extract prerequisites
  have hInit112 : InitGoalHolds pm_goal_15.numRanks intermediateGoal_112 initSM initPM := by
    apply hInitGoals; simp [goal_15_cut_initGoals, goal_15_prereqs, initGoals]
  have hInit108 : InitGoalHolds pm_goal_15.numRanks intermediateGoal_108 initSM initPM := by
    apply hInitGoals; simp [goal_15_cut_initGoals, goal_15_prereqs, initGoals]
  -- Lineage facts
  have h112_rec : initSM 112 = reconstructWithDim 1 pm_goal_15.numRanks 0
      [initPM 400, initPM 401, initPM 402, initPM 403] := by
    have hrec := hInit112.2.2
    simp only [intermediateGoal_112, pm_goal_15, List.map] at hrec; exact hrec
  have h108_rec : initSM 108 = reconstructWithDim 3 pm_goal_15.numRanks 0
      [initPM 304, initPM 305, initPM 306, initPM 307] := by
    have hrec := hInit108.2.2
    simp only [intermediateGoal_108, pm_goal_15, List.map] at hrec; exact hrec
  -- Shapes
  have h112_shape : (initSM 112).shape = [16, 8, 64, 64] := hInit112.1
  have h108_shape : (initSM 108).shape = [16, 8, 64, 16] := hInit108.1
  have htp112_shapes := hInit112.2.1
  simp only [intermediateGoal_112, List.map] at htp112_shapes
  have h400_shape : (initPM 400).shape = [16, 2, 64, 64] := by
    have := congrArg List.head? htp112_shapes; simpa using this
  have h401_shape : (initPM 401).shape = [16, 2, 64, 64] := by
    have := congrArg List.tail htp112_shapes; have := congrArg List.head? this; simpa using this
  have h402_shape : (initPM 402).shape = [16, 2, 64, 64] := by
    have := congrArg (List.tail ∘ List.tail) htp112_shapes
    have := congrArg List.head? this; simpa using this
  have h403_shape : (initPM 403).shape = [16, 2, 64, 64] := by
    have := congrArg (List.tail ∘ List.tail ∘ List.tail) htp112_shapes
    have := congrArg List.head? this; simpa using this
  have htp108_shapes := hInit108.2.1
  simp only [intermediateGoal_108, List.map] at htp108_shapes
  have h304_shape : (initPM 304).shape = [16, 8, 64, 4] := by
    have := congrArg List.head? htp108_shapes; simpa using this
  have h305_shape : (initPM 305).shape = [16, 8, 64, 4] := by
    have := congrArg List.tail htp108_shapes; have := congrArg List.head? this; simpa using this
  have h306_shape : (initPM 306).shape = [16, 8, 64, 4] := by
    have := congrArg (List.tail ∘ List.tail) htp108_shapes
    have := congrArg List.head? this; simpa using this
  have h307_shape : (initPM 307).shape = [16, 8, 64, 4] := by
    have := congrArg (List.tail ∘ List.tail ∘ List.tail) htp108_shapes
    have := congrArg List.head? this; simpa using this
  -- SM computation
  have hsm : (denoteGraph sm_goal_15 initSM) 113 = batchedMatmul (initSM 112) (initSM 108) := by
    simp [sm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet]
  -- PM computations: AllToAllPrim on A returns A_rank; AllToAllPrimWithDims on B
  have hpm428 : (denoteGraph pm_goal_15 initPM) 428 =
      batchedMatmul (initPM 400) (allToAllPrimWithDims 4 0 [initPM 304, initPM 305, initPM 306, initPM 307] 3 1) := by
    simp [pm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrim, h400_shape]
  have hpm429 : (denoteGraph pm_goal_15 initPM) 429 =
      batchedMatmul (initPM 401) (allToAllPrimWithDims 4 1 [initPM 304, initPM 305, initPM 306, initPM 307] 3 1) := by
    simp [pm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrim, h401_shape]
  have hpm430 : (denoteGraph pm_goal_15 initPM) 430 =
      batchedMatmul (initPM 402) (allToAllPrimWithDims 4 2 [initPM 304, initPM 305, initPM 306, initPM 307] 3 1) := by
    simp [pm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrim, h402_shape]
  have hpm431 : (denoteGraph pm_goal_15 initPM) 431 =
      batchedMatmul (initPM 403) (allToAllPrimWithDims 4 3 [initPM 304, initPM 305, initPM 306, initPM 307] 3 1) := by
    simp [pm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet, allToAllPrim, h403_shape]
  -- allToAllPrimWithDims = chunkPrimDimN 1 4 r (allGatherPrimDimN 3 4 0 [B0..B3])
  -- = chunkPrimDimN 1 4 r (initSM 108) since initSM 108 = gather3 [B0..B3]
  have h108_dimN : initSM 108 = allGatherPrimDimN 3 pm_goal_15.numRanks 0
      [initPM 304, initPM 305, initPM 306, initPM 307] := by
    rw [h108_rec]; simp [reconstructWithDim, h304_shape]
  have h112_dimN : initSM 112 = allGatherPrimDimN 1 pm_goal_15.numRanks 0
      [initPM 400, initPM 401, initPM 402, initPM 403] := by
    rw [h112_rec]; simp [reconstructWithDim, h400_shape]
  have hata_eq : ∀ r, allToAllPrimWithDims 4 r [initPM 304, initPM 305, initPM 306, initPM 307] 3 1 =
      chunkPrimDimN 1 4 r (initSM 108) := by
    intro r; rw [h108_dimN]; rfl
  -- Simplify the goal structure
  dsimp only [goal_15_stmt_cut, CoarseLineageHoldsWithInit, goal_15] at *
  simp only [List.map]
  rw [hsm, hpm428, hpm429, hpm430, hpm431, hata_eq 0, hata_eq 1, hata_eq 2, hata_eq 3]
  -- Shape goals
  have hsm_shape : (batchedMatmul (initSM 112) (initSM 108)).shape = [16, 8, 64, 16] :=
    batchedMatmul_4d_shape _ _ 16 8 64 64 16 h112_shape h108_shape
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r (initSM 108)).shape = [16, 2, 64, 16] :=
    fun r => chunkPrimDimN_shape 1 4 r _ _ h108_shape (by omega)
  refine ⟨hsm_shape, ?_, ?_⟩
  · -- Piece shapes
    simp only [batchedMatmul_4d_shape _ _ 16 2 64 64 16 h400_shape (hchunk_shape 0),
      batchedMatmul_4d_shape _ _ 16 2 64 64 16 h401_shape (hchunk_shape 1),
      batchedMatmul_4d_shape _ _ 16 2 64 64 16 h402_shape (hchunk_shape 2),
      batchedMatmul_4d_shape _ _ 16 2 64 64 16 h403_shape (hchunk_shape 3)]
  · -- Reconstruction: batchedMatmul(initSM 112, initSM 108) = gather1[pieces]
    simp only [pm_goal_15] at *
    rw [h112_dimN]
    -- Convert reconstructWithDim to allGatherPrimDimN
    have hpiece0_shape := batchedMatmul_4d_shape _ _ 16 2 64 64 16 h400_shape (hchunk_shape 0)
    conv_rhs => unfold reconstructWithDim
    simp only [List.head?, Option.map, hpiece0_shape]
    exact batchedMatmul_gather1_distrib (initPM 400) (initPM 401) (initPM 402) (initPM 403)
      (initSM 108) h400_shape h401_shape h402_shape h403_shape h108_shape

end TrainVerify.Denote.GeneratedGoals
