/- Pattern_2 proof: goal_2_stmt_cut.
   Pattern: 2
   Hash: f12bb08992f5e7eb
   Goals: 2
   Op flavour: FW_inner_chunk_ce (cross-entropy zLoss) context-parallel
     SM=1 op (fw_inner_chunk_ce), PM=5 ops (2×ChunkPrim + 2×FW_inner_chunk_ce + 1×AllGatherPrim)
   Depends on: denote.InnerChunkCEShard for the top-level equivalence lemma.

   Proves goal_2_stmt_cut (on sm_goal_2/pm_goal_2 slices with
   goal_2_cut_initGoals = initGoals ++ goal_2_prereqs, which includes
   intermediateGoal_5930). The uncut goal_2_stmt is derivable via
   Goal_2_CutToFull.lean once M2 non-base emitter is extended.
-/
import denote.yoco_goals.Goal_2
import denote.InnerChunkCEShard

set_option linter.style.longLine false
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_2_goalIds : List Nat := [2]
inductive pattern_2_target : Prop → Prop
  | goal_2 : pattern_2_target goal_2_stmt_cut

def pattern_2_stmt : Prop :=
  ∀ {target : Prop}, pattern_2_target target → target

-- ============================================================
-- Helper: `applyNode_fw_inner_chunk_ce_snd_out` for 1-param nodes.
--
-- The library lemma requires `params := [chunkSize, zLossScaleInt]`, but
-- YOCO Pattern_2 nodes have `params := [1024]` only.
-- ============================================================

theorem applyNode_fw_inner_chunk_ce_snd_out_1param
    (g : GraphDecl) (s : Store) (rank chunkSize : Nat)
    (xTid wTid yTid t1 t2 : Tid)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_inner_chunk_ce",
                    ins := [xTid, wTid, yTid], outs := [t1, t2],
                    params := [chunkSize] } t2 =
      (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
          (((s wTid).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
  unfold applyNode
  simp only [List.map_cons, List.map_nil]
  show storeSet s ([t1, t2].zip
      (evalOp g.numRanks rank "OpName.FW_inner_chunk_ce" [chunkSize]
        [s xTid, s wTid, s yTid])) t2 = _
  have hevalOp : evalOp g.numRanks rank "OpName.FW_inner_chunk_ce" [chunkSize]
      [s xTid, s wTid, s yTid] =
    [ (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid) (((s wTid).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).1,
      (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid) (((s wTid).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 ] := by
    rfl
  rw [hevalOp]
  change storeSet s
    [(t1, (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
              (((s wTid).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).1),
     (t2, (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
              (((s wTid).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

-- ============================================================
-- SM-side (sm_goal_2 slice): tid 4674 = fw_inner_chunk_ce.snd of
-- the (unsharded) inputs 5930, 5931, 4678.
-- ============================================================

/-- On the SM slice `sm_goal_2` (which has 1 node), tid 4674 unfolds
    to `(fw_inner_chunk_ce (initSM 5930) (initSM 5931) (initSM 4678)).snd`. -/
theorem denote_sm_goal_2_4674 (initSM : Store) :
    denoteGraph sm_goal_2 initSM 4674 =
      (fw_inner_chunk_ce (initSM 5930) (initSM 5931) (initSM 4678)
          (((initSM 5931).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
  -- sm_goal_2 has only 1 node at position 0. Reduce via unfold + simp.
  unfold denoteGraph
  simp only [sm_goal_2, List.foldl]
  exact applyNode_fw_inner_chunk_ce_snd_out_1param sm_goal_2 initSM 0 1024 5930 5931 4678
    4673 4674 (by decide)

-- ============================================================
-- PM-side (pm_goal_2 slice): tid 4674 = allGather of per-shard
-- fw_inner_chunk_ce.snd applied to chunk-sharded x/y.
-- ============================================================

/-- PM slice at prefix take 1 (just pm_goal_2[0]): tid 11835 = ChunkPrim
    rank=0 of initPM 4678. -/
theorem denote_pm_goal_2_prefix_11835 (initPM : Store) :
    denoteGraph {pm_goal_2 with nodes := pm_goal_2.nodes.take 1} initPM 11835 =
      chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4678) := by
  unfold denoteGraph
  simp only [pm_goal_2, List.take, List.foldl]
  exact applyNode_chunkPrimDimN_out pm_goal_2 initPM 0 4678 11835 0

/-- PM slice at prefix take 2 (through pm_goal_2[1]): tid 11836 = ChunkPrim
    rank=1. -/
theorem denote_pm_goal_2_prefix_11836 (initPM : Store) :
    denoteGraph {pm_goal_2 with nodes := pm_goal_2.nodes.take 2} initPM 11836 =
      chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4678) := by
  unfold denoteGraph
  simp only [pm_goal_2, List.take, List.foldl]
  -- After foldl unfolding, we have applyNode g1 (applyNode g1 initPM node0) node1 11836,
  -- where g1 = {numRanks := 2, nodes := [node0, node1]}. Since applyNode's semantics
  -- depend only on g.numRanks (not g.nodes), we can rewrite via applyNode_congr_numRanks.
  have hnR : ({pm_goal_2 with nodes := pm_goal_2.nodes.take 2} : GraphDecl).numRanks = pm_goal_2.numRanks := rfl
  set g1 : GraphDecl := { numRanks := 2, nodes :=
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] },
     { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] }] }
  have hg1_ranks : g1.numRanks = pm_goal_2.numRanks := by rfl
  rw [applyNode_chunkPrimDimN_out g1 _ 1 4678 11836 0]
  -- Reduce inner applyNode read at 4678 (node0 doesn't write 4678).
  have h : applyNode g1 initPM
    { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] } 4678
    = initPM 4678 := by
    apply applyNode_eq_of_not_mem_outs
    decide
  rw [h]

/-- PM slice final: tid 4674 = allGather of per-shard fw_inner_chunk_ce.snd.
    pm_goal_2 has 5 nodes total; 4674 is written by node[4]. -/
theorem denote_pm_goal_2_4674 (initPM : Store) :
    denoteGraph pm_goal_2 initPM 4674 =
      allGatherPrimDimN 0 pm_goal_2.numRanks 0
        [ (fw_inner_chunk_ce (initPM 11833) (initPM 5931)
              (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4678))
              (((initPM 5931).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2,
          (fw_inner_chunk_ce (initPM 11834) (initPM 5931)
              (chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4678))
              (((initPM 5931).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2 ] := by
  -- Bind literal g and rewrite pm_goal_2 = g.
  set g : GraphDecl := { numRanks := 2, nodes :=
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] },
     { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] },
     { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835],
       outs := [11837, 11839], params := [1024] },
     { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836],
       outs := [11838, 11840], params := [1024] },
     { rank := 0, op := "OpName.AllGatherPrim", ins := [11839, 11840], outs := [4674],
       params := [0] }] } with hg_def
  have hpm_eq : pm_goal_2 = g := by show pm_goal_2 = _; rfl
  rw [hpm_eq]
  -- Node literals (used many times below).
  set n0 : NodeDecl :=
    { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] } with hn0
  set n1 : NodeDecl :=
    { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] } with hn1
  set n2 : NodeDecl :=
    { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835],
      outs := [11837, 11839], params := [1024] } with hn2
  set n3 : NodeDecl :=
    { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836],
      outs := [11838, 11840], params := [1024] } with hn3
  set n4 : NodeDecl :=
    { rank := 0, op := "OpName.AllGatherPrim", ins := [11839, 11840], outs := [4674],
      params := [0] } with hn4
  -- Intermediate stores S1..S4.
  set S1 : Store := applyNode g initPM n0 with hS1
  set S2 : Store := applyNode g S1 n1 with hS2
  set S3 : Store := applyNode g S2 n2 with hS3
  set S4 : Store := applyNode g S3 n3 with hS4
  -- The full graph denotation at 4674 = applyNode g S4 n4 4674.
  have hgoal : denoteGraph g initPM 4674 = applyNode g S4 n4 4674 := by
    show (g.nodes.foldl (applyNode g) initPM) 4674 = _
    simp only [hg_def, List.foldl]
    rfl
  rw [hgoal]
  -- Step 1: applyNode g S4 n4 4674 = allGather 0 g.numRanks 0 [S4 11839, S4 11840].
  rw [applyNode_allGatherPrimDimN_out g S4 0 [11839, 11840] 4674 0]
  simp only [List.map_cons, List.map_nil]
  -- Reduce S4 11839: n3 doesn't write 11839.
  have hS4_11839 : S4 11839 = S3 11839 := by
    show applyNode g S3 n3 11839 = S3 11839
    apply applyNode_eq_of_not_mem_outs; decide
  -- Reduce S4 11840: n3 writes 11840 as .snd.
  have hS4_11840 : S4 11840 =
      (fw_inner_chunk_ce (S3 11834) (S3 5931) (S3 11836)
          (((S3 5931).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
    show applyNode g S3 n3 11840 = _
    exact applyNode_fw_inner_chunk_ce_snd_out_1param g S3 1 1024 11834 5931 11836 11838 11840
      (by decide)
  -- Reduce S3 11839: n2 writes 11839 as .snd.
  have hS3_11839 : S3 11839 =
      (fw_inner_chunk_ce (S2 11833) (S2 5931) (S2 11835)
          (((S2 5931).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
    show applyNode g S2 n2 11839 = _
    exact applyNode_fw_inner_chunk_ce_snd_out_1param g S2 0 1024 11833 5931 11835 11837 11839
      (by decide)
  -- Skip lemmas: nodes n0/n1/n2/n3 not writing specific tids.
  have hS3_11833 : S3 11833 = S2 11833 := by
    show applyNode g S2 n2 11833 = S2 11833; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_5931 : S3 5931 = S2 5931 := by
    show applyNode g S2 n2 5931 = S2 5931; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_11834 : S3 11834 = S2 11834 := by
    show applyNode g S2 n2 11834 = S2 11834; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_11835 : S3 11835 = S2 11835 := by
    show applyNode g S2 n2 11835 = S2 11835; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_11836 : S3 11836 = S2 11836 := by
    show applyNode g S2 n2 11836 = S2 11836; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11833 : S2 11833 = S1 11833 := by
    show applyNode g S1 n1 11833 = S1 11833; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_5931 : S2 5931 = S1 5931 := by
    show applyNode g S1 n1 5931 = S1 5931; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11834 : S2 11834 = S1 11834 := by
    show applyNode g S1 n1 11834 = S1 11834; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11835 : S2 11835 = S1 11835 := by
    show applyNode g S1 n1 11835 = S1 11835; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11836 : S2 11836 = chunkPrimDimN 0 g.numRanks 1 (S1 4678) := by
    show applyNode g S1 n1 11836 = _; exact applyNode_chunkPrimDimN_out g S1 1 4678 11836 0
  have hS2_4678 : S2 4678 = S1 4678 := by
    show applyNode g S1 n1 4678 = S1 4678; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_11833 : S1 11833 = initPM 11833 := by
    show applyNode g initPM n0 11833 = initPM 11833; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_5931 : S1 5931 = initPM 5931 := by
    show applyNode g initPM n0 5931 = initPM 5931; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_11834 : S1 11834 = initPM 11834 := by
    show applyNode g initPM n0 11834 = initPM 11834; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_11835 : S1 11835 = chunkPrimDimN 0 g.numRanks 0 (initPM 4678) := by
    show applyNode g initPM n0 11835 = _; exact applyNode_chunkPrimDimN_out g initPM 0 4678 11835 0
  have hS1_4678 : S1 4678 = initPM 4678 := by
    show applyNode g initPM n0 4678 = initPM 4678; apply applyNode_eq_of_not_mem_outs; decide
  -- Combine: rewrite S4 → S3 → S2 → S1 → initPM. Use `try` since some rewrites
  -- may not apply (e.g., hS3_11839 already reduces S3 11833 in one branch).
  rw [hS4_11839, hS4_11840, hS3_11839]
  try rw [hS3_11833]
  try rw [hS3_11834]
  try rw [hS3_5931]
  try rw [hS3_5931]  -- second occurrence in the other branch
  try rw [hS3_11835]
  try rw [hS3_11836]
  try rw [hS2_11833]
  try rw [hS2_11834]
  try rw [hS2_5931]
  try rw [hS2_5931]
  try rw [hS2_11835]
  try rw [hS2_11836]
  try rw [hS2_4678]
  try rw [hS1_11833]
  try rw [hS1_11834]
  try rw [hS1_5931]
  try rw [hS1_5931]
  try rw [hS1_11835]
  try rw [hS1_4678]

-- ============================================================
-- Main proof: goal_2_stmt_cut.
--
-- Signature (from Goal_2.lean):
--   CoarseLineageHoldsWithInit sm_goal_2 pm_goal_2 goal_2
--     sm_goal_2InitEnv pm_goal_2InitEnv goal_2_cut_initGoals
--
-- where goal_2_cut_initGoals = initGoals ++ goal_2_prereqs (includes
-- intermediateGoal_5930 giving us initSM 5930 = allGather [initPM 11833,
-- initPM 11834]).
--
-- Plan (per README block earlier):
--   1. Intro initSM, initPM, hSM, hPM, hInit.
--   2. refine ⟨shape_sm, shape_pm, value⟩
--   3. shape_sm: use denote_sm_goal_2_4674 + fw_inner_chunk_ce_snd_shape.
--   4. shape_pm: use denote_pm_goal_2_4674 + fw_inner_chunk_ce_snd_shape +
--      allGatherPrimDimN_shape.
--   5. value: use denote_sm_goal_2_4674 + denote_pm_goal_2_4674 +
--      intermediateGoal_5930 hypothesis (from hInit) +
--      InnerChunkCEShard.fw_inner_chunk_ce_snd_allGatherDim0_shards.
-- ============================================================
/-- The `.snd` output (`z_losses`) of `fw_inner_chunk_ce` does not depend on `y`. -/
theorem fw_inner_chunk_ce_snd_y_independent
    (x w y y' : Tensor) (vocab : Nat) (zScale : Scalar) :
    (fw_inner_chunk_ce x w y vocab zScale).snd =
    (fw_inner_chunk_ce x w y' vocab zScale).snd := by
  unfold fw_inner_chunk_ce
  rfl

theorem prove_goal_2 : goal_2_stmt_cut := by
  intro initSM initPM hSM hPM hInit
  simp only [goal_2]
  -- Shape witnesses.
  have h4678_sm : (initSM 4678).shape = [4096] :=
    hSM 4678 [4096] (by native_decide)
  have h5930_sm : (initSM 5930).shape = [4096, 1024] :=
    hSM 5930 [4096, 1024] (by native_decide)
  have h5931_sm : (initSM 5931).shape = [154880, 1024] :=
    hSM 5931 [154880, 1024] (by native_decide)
  have h4678_pm : (initPM 4678).shape = [4096] :=
    hPM 4678 [4096] (by native_decide)
  have h5931_pm : (initPM 5931).shape = [154880, 1024] :=
    hPM 5931 [154880, 1024] (by native_decide)
  have h11833_pm : (initPM 11833).shape = [2048, 1024] :=
    hPM 11833 [2048, 1024] (by native_decide)
  have h11834_pm : (initPM 11834).shape = [2048, 1024] :=
    hPM 11834 [2048, 1024] (by native_decide)
  -- Get intermediateGoal_5930 from hInit: initSM 5930 = reconstruct [initPM 11833, initPM 11834].
  have hg5930 : InitGoalHolds pm_goal_2.numRanks intermediateGoal_5930 initSM initPM := by
    apply hInit
    unfold goal_2_cut_initGoals
    apply List.mem_append_right
    -- intermediateGoal_5930 is in goal_2_prereqs.
    native_decide
  unfold InitGoalHolds at hg5930
  obtain ⟨_, _, hval5930⟩ := hg5930
  simp only [intermediateGoal_5930, List.map] at hval5930
  -- pm_goal_2.numRanks = 2.
  have hpmR : pm_goal_2.numRanks = 2 := rfl
  -- reconstructWithDim on [x, y] with non-scalar shape = allGatherPrimDimN.
  have hreconstr :
      reconstructWithDim 0 pm_goal_2.numRanks 0 [initPM 11833, initPM 11834] =
      allGatherPrimDimN 0 pm_goal_2.numRanks 0 [initPM 11833, initPM 11834] := by
    unfold reconstructWithDim
    simp only [List.head?_cons, Option.map_some, Option.getD_some, h11833_pm]
    rfl
  rw [hreconstr] at hval5930
  refine ⟨?shape_sm, ?shape_pm, ?value⟩
  case shape_sm =>
    -- (denoteGraph sm_goal_2 initSM 4674).shape = [4096]
    rw [denote_sm_goal_2_4674]
    -- Use fw_inner_chunk_ce_snd_shape.
    have hL : (initSM 5930).shape.head? = some 4096 := by rw [h5930_sm]; rfl
    have hshape := fw_inner_chunk_ce_snd_shape
      (initSM 5930) (initSM 5931) (initSM 4678)
      (((initSM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar) 4096 hL
    exact hshape
  case shape_pm =>
    -- goal.tpShapes = [[4096]], tps = [{rank:=0, tid:=4674}].
    simp only [List.map]
    rw [denote_pm_goal_2_4674]
    -- Chunk shape lemma: (chunk 0 2 r [4096]).shape = [2048].
    have hchunk_0_shape : (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4678)).shape = [2048] := by
      rw [hpmR, chunkPrimDimN_shape 0 2 0 (initPM 4678) [4096] h4678_pm (by decide)]; rfl
    have hchunk_1_shape : (chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4678)).shape = [2048] := by
      rw [hpmR, chunkPrimDimN_shape 0 2 1 (initPM 4678) [4096] h4678_pm (by decide)]; rfl
    -- Each shard's fw_inner_chunk_ce.snd shape = [2048] (via x.shape.head? = some 2048).
    have hL_r0 : (initPM 11833).shape.head? = some 2048 := by rw [h11833_pm]; rfl
    have hshape_r0 :
        (fw_inner_chunk_ce (initPM 11833) (initPM 5931)
            (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4678))
            (((initPM 5931).shape.head?).getD 0)
            ((0 : Nat) : Scalar)).2.shape = [2048] :=
      fw_inner_chunk_ce_snd_shape (initPM 11833) (initPM 5931) _
        (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar) 2048 hL_r0
    -- head? = some (first shard). Use `2` directly since hpmR : pm_goal_2.numRanks = 2.
    rw [hpmR]
    have hhead : (([(fw_inner_chunk_ce (initPM 11833) (initPM 5931)
          (chunkPrimDimN 0 2 0 (initPM 4678))
          (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar)).2,
        (fw_inner_chunk_ce (initPM 11834) (initPM 5931)
          (chunkPrimDimN 0 2 1 (initPM 4678))
          (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar)).2] : List Tensor).head?.map
          (fun t => t.shape)).getD [] = [2048] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      -- After `rw [hpmR]` above, chunkPrimDimN 0 pm_goal_2.numRanks → chunkPrimDimN 0 2.
      -- But hshape_r0's chunkPrimDimN still uses pm_goal_2.numRanks. Rederive.
      have hL_r0' : (initPM 11833).shape.head? = some 2048 := by rw [h11833_pm]; rfl
      exact fw_inner_chunk_ce_snd_shape (initPM 11833) (initPM 5931) _
        (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar) 2048 hL_r0'
    rw [allGatherPrimDimN_shape 0 2 _ _ hhead]
    rfl
  case value =>
    -- Goal: denoteGraph sm_goal_2 initSM 4674 = reconstructWithDim 0 numRanks 0 [denoteGraph pm_goal_2 initPM 4674]
    simp only [List.map, reconstructWithDim_singleton]
    rw [denote_sm_goal_2_4674, denote_pm_goal_2_4674]
    -- Use intermediateGoal_5930 hypothesis: initSM 5930 = allGather [initPM 11833, initPM 11834].
    rw [hval5930]
    -- 4678 unsharded: initSM 4678 = initPM 4678 via initGoal_4678.
    have hg4678 : InitGoalHolds pm_goal_2.numRanks initGoal_4678 initSM initPM := by
      apply hInit
      unfold goal_2_cut_initGoals
      apply List.mem_append_left
      native_decide
    unfold InitGoalHolds at hg4678
    obtain ⟨_, _, hval4678⟩ := hg4678
    simp only [initGoal_4678, List.map, reconstructWithDim_singleton] at hval4678
    rw [hval4678]
    -- 5931 unsharded similarly.
    have hg5931 : InitGoalHolds pm_goal_2.numRanks initGoal_5931 initSM initPM := by
      apply hInit
      unfold goal_2_cut_initGoals
      apply List.mem_append_left
      native_decide
    unfold InitGoalHolds at hg5931
    obtain ⟨_, _, hval5931⟩ := hg5931
    simp only [initGoal_5931, List.map, reconstructWithDim_singleton] at hval5931
    rw [hval5931]
    -- Now apply the top-level lemma from InnerChunkCEShard.
    -- Goal shape:
    --   (fw_ice (allGather [pm 11833, pm 11834]) (pm 5931) (pm 4678) vocab 0).snd
    --   = allGather [(fw_ice (pm 11833) (pm 5931) (chunk_0 pm 4678) vocab 0).snd,
    --                (fw_ice (pm 11834) (pm 5931) (chunk_1 pm 4678) vocab 0).snd]
    -- Strategy:
    -- (1) Use `fw_inner_chunk_ce_snd_y_independent` to change the y arg on each shard
    --     from `chunk_r (pm 4678)` to `pm 4678` (same for all shards).
    -- (2) Apply `fw_inner_chunk_ce_snd_allGatherDim0_shards` with y = initPM 4678
    --     (unshared, since .snd doesn't depend on y).
    -- (3) Convert List.ofFn (Fin 2) to explicit 2-element list.
    -- Step 1: rewrite each shard's y from chunk to pm 4678.
    have hy0 :
        (fw_inner_chunk_ce (initPM 11833) (initPM 5931)
            (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4678))
            (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 =
        (fw_inner_chunk_ce (initPM 11833) (initPM 5931) (initPM 4678)
            (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 :=
      fw_inner_chunk_ce_snd_y_independent _ _ _ _ _ _
    have hy1 :
        (fw_inner_chunk_ce (initPM 11834) (initPM 5931)
            (chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4678))
            (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 =
        (fw_inner_chunk_ce (initPM 11834) (initPM 5931) (initPM 4678)
            (((initPM 5931).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 :=
      fw_inner_chunk_ce_snd_y_independent _ _ _ _ _ _
    rw [hy0, hy1]
    -- Step 2: apply main lemma. Get hypotheses.
    have hL_shard_pos : 0 < 2048 := by decide
    have hh_pos : 0 < 1024 := by decide
    have hv_pos : 0 < 154880 := by decide
    have hparts_pos : 0 < pm_goal_2.numRanks := by rw [hpmR]; decide
    have hxs_head_pm : (([initPM 11833, initPM 11834] : List Tensor).head?.map (fun t => t.shape)).getD [] =
        [2048, 1024] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact h11833_pm
    have hxs_shape_pm : ∀ r (_ : r < pm_goal_2.numRanks),
        (([initPM 11833, initPM 11834] : List Tensor).getD r (zeroTensor [2048, 1024])).shape =
        [2048, 1024] := by
      intro r hr
      rw [hpmR] at hr
      interval_cases r
      · exact h11833_pm
      · exact h11834_pm
    -- Vocab reduces to 154880.
    have hvocab_eq : ((initPM 5931).shape.head?).getD 0 = 154880 := by rw [h5931_pm]; rfl
    rw [hvocab_eq]
    -- Apply main lemma.
    rw [fw_inner_chunk_ce_snd_allGatherDim0_shards pm_goal_2.numRanks 2048 1024 154880
      ((0 : Nat) : Scalar) [initPM 11833, initPM 11834] (initPM 5931) (initPM 4678)
      hparts_pos hL_shard_pos hh_pos hv_pos hxs_head_pm hxs_shape_pm h5931_pm]
    -- Step 3: expand List.ofFn (Fin 2) to explicit list.
    rw [hpmR]
    have hofFn : (List.ofFn (n := 2) (fun r : Fin 2 =>
        (fw_inner_chunk_ce (([initPM 11833, initPM 11834] : List Tensor).getD r.val
              (zeroTensor [2048, 1024]))
          (initPM 5931) (initPM 4678) 154880 ((0 : Nat) : Scalar)).snd)) =
        [ (fw_inner_chunk_ce (initPM 11833) (initPM 5931) (initPM 4678) 154880
              ((0 : Nat) : Scalar)).snd,
          (fw_inner_chunk_ce (initPM 11834) (initPM 5931) (initPM 4678) 154880
              ((0 : Nat) : Scalar)).snd ] := by
      rfl
    rw [hofFn]

-- Placeholder proof to be filled in the next iteration.

theorem prove_pattern_2 : pattern_2_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_2

end TrainVerify.Denote.GeneratedPatterns
