/- Pattern_2 proof: goal_2_stmt_cut.
   Pattern: 2
   Authority: final GeneratedYOCOMoE Goal 2
   Goals: 2
   Op flavour: FW_inner_chunk_ce (cross-entropy zLoss) context-parallel
     SM=1 op (fw_inner_chunk_ce), PM=5 ops (2×ChunkPrim + 2×FW_inner_chunk_ce + 1×AllGatherPrim)
   Depends on: denote.InnerChunkCEShard for the top-level equivalence lemma.

   Proves goal_2_stmt_cut (on sm_goal_2/pm_goal_2 slices with
   goal_2_cut_initGoals = initGoals ++ goal_2_prereqs, which includes
   intermediateGoal_6255). The uncut goal_2_stmt is derivable via
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
-- SM-side (sm_goal_2 slice): tid 4927 = fw_inner_chunk_ce.snd of
-- the (unsharded) inputs 6255, 6256, 4931.
-- ============================================================

/-- On the SM slice `sm_goal_2` (which has 1 node), tid 4927 unfolds
    to `(fw_inner_chunk_ce (initSM 6255) (initSM 6256) (initSM 4931)).snd`. -/
theorem denote_sm_goal_2_4927 (initSM : Store) :
    denoteGraph sm_goal_2 initSM 4927 =
      (fw_inner_chunk_ce (initSM 6255) (initSM 6256) (initSM 4931)
          (((initSM 6256).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
  -- sm_goal_2 has only 1 node at position 0. Reduce via unfold + simp.
  unfold denoteGraph
  simp only [sm_goal_2, List.foldl]
  exact applyNode_fw_inner_chunk_ce_snd_out_1param sm_goal_2 initSM 0 1024 6255 6256 4931
    4926 4927 (by decide)

-- ============================================================
-- PM-side (pm_goal_2 slice): tid 4927 = allGather of per-shard
-- fw_inner_chunk_ce.snd applied to chunk-sharded x/y.
-- ============================================================

/-- PM slice at prefix take 1 (just pm_goal_2[0]): tid 11714 = ChunkPrim
    rank=0 of initPM 4931. -/
theorem denote_pm_goal_2_prefix_11714 (initPM : Store) :
    denoteGraph {pm_goal_2 with nodes := pm_goal_2.nodes.take 1} initPM 11714 =
      chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4931) := by
  unfold denoteGraph
  simp only [pm_goal_2, List.take, List.foldl]
  exact applyNode_chunkPrimDimN_out pm_goal_2 initPM 0 4931 11714 0

/-- PM slice at prefix take 2 (through pm_goal_2[1]): tid 11715 = ChunkPrim
    rank=1. -/
theorem denote_pm_goal_2_prefix_11715 (initPM : Store) :
    denoteGraph {pm_goal_2 with nodes := pm_goal_2.nodes.take 2} initPM 11715 =
      chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4931) := by
  unfold denoteGraph
  simp only [pm_goal_2, List.take, List.foldl]
  -- After foldl unfolding, we have applyNode g1 (applyNode g1 initPM node0) node1 11715,
  -- where g1 = {numRanks := 2, nodes := [node0, node1]}. Since applyNode's semantics
  -- depend only on g.numRanks (not g.nodes), we can rewrite via applyNode_congr_numRanks.
  have hnR : ({pm_goal_2 with nodes := pm_goal_2.nodes.take 2} : GraphDecl).numRanks = pm_goal_2.numRanks := rfl
  set g1 : GraphDecl := { numRanks := 2, nodes :=
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [4931], outs := [11714], params := [0] },
     { rank := 1, op := "OpName.ChunkPrim", ins := [4931], outs := [11715], params := [0] }] }
  have hg1_ranks : g1.numRanks = pm_goal_2.numRanks := by rfl
  rw [applyNode_chunkPrimDimN_out g1 _ 1 4931 11715 0]
  -- Reduce inner applyNode read at 4931 (node0 doesn't write 4931).
  have h : applyNode g1 initPM
    { rank := 0, op := "OpName.ChunkPrim", ins := [4931], outs := [11714], params := [0] } 4931
    = initPM 4931 := by
    apply applyNode_eq_of_not_mem_outs
    decide
  rw [h]

/-- PM slice final: tid 4927 = allGather of per-shard fw_inner_chunk_ce.snd.
    pm_goal_2 has 5 nodes total; 4927 is written by node[4]. -/
theorem denote_pm_goal_2_4927 (initPM : Store) :
    denoteGraph pm_goal_2 initPM 4927 =
      allGatherPrimDimN 0 pm_goal_2.numRanks 0
        [ (fw_inner_chunk_ce (initPM 11712) (initPM 6256)
              (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4931))
              (((initPM 6256).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2,
          (fw_inner_chunk_ce (initPM 11713) (initPM 6256)
              (chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4931))
              (((initPM 6256).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2 ] := by
  -- Bind literal g and rewrite pm_goal_2 = g.
  set g : GraphDecl := { numRanks := 2, nodes :=
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [4931], outs := [11714], params := [0] },
     { rank := 1, op := "OpName.ChunkPrim", ins := [4931], outs := [11715], params := [0] },
     { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11712, 6256, 11714],
       outs := [11716, 11718], params := [1024] },
     { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11713, 6256, 11715],
       outs := [11717, 11719], params := [1024] },
     { rank := 0, op := "OpName.AllGatherPrim", ins := [11718, 11719], outs := [4927],
       params := [0] }] } with hg_def
  have hpm_eq : pm_goal_2 = g := by show pm_goal_2 = _; rfl
  rw [hpm_eq]
  -- Node literals (used many times below).
  set n0 : NodeDecl :=
    { rank := 0, op := "OpName.ChunkPrim", ins := [4931], outs := [11714], params := [0] } with hn0
  set n1 : NodeDecl :=
    { rank := 1, op := "OpName.ChunkPrim", ins := [4931], outs := [11715], params := [0] } with hn1
  set n2 : NodeDecl :=
    { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11712, 6256, 11714],
      outs := [11716, 11718], params := [1024] } with hn2
  set n3 : NodeDecl :=
    { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11713, 6256, 11715],
      outs := [11717, 11719], params := [1024] } with hn3
  set n4 : NodeDecl :=
    { rank := 0, op := "OpName.AllGatherPrim", ins := [11718, 11719], outs := [4927],
      params := [0] } with hn4
  -- Intermediate stores S1..S4.
  set S1 : Store := applyNode g initPM n0 with hS1
  set S2 : Store := applyNode g S1 n1 with hS2
  set S3 : Store := applyNode g S2 n2 with hS3
  set S4 : Store := applyNode g S3 n3 with hS4
  -- The full graph denotation at 4927 = applyNode g S4 n4 4927.
  have hgoal : denoteGraph g initPM 4927 = applyNode g S4 n4 4927 := by
    show (g.nodes.foldl (applyNode g) initPM) 4927 = _
    simp only [hg_def, List.foldl]
    rfl
  rw [hgoal]
  -- Step 1: applyNode g S4 n4 4927 = allGather 0 g.numRanks 0 [S4 11718, S4 11719].
  rw [applyNode_allGatherPrimDimN_out g S4 0 [11718, 11719] 4927 0]
  simp only [List.map_cons, List.map_nil]
  -- Reduce S4 11718: n3 doesn't write 11718.
  have hS4_11718 : S4 11718 = S3 11718 := by
    show applyNode g S3 n3 11718 = S3 11718
    apply applyNode_eq_of_not_mem_outs; decide
  -- Reduce S4 11719: n3 writes 11719 as .snd.
  have hS4_11719 : S4 11719 =
      (fw_inner_chunk_ce (S3 11713) (S3 6256) (S3 11715)
          (((S3 6256).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
    show applyNode g S3 n3 11719 = _
    exact applyNode_fw_inner_chunk_ce_snd_out_1param g S3 1 1024 11713 6256 11715 11717 11719
      (by decide)
  -- Reduce S3 11718: n2 writes 11718 as .snd.
  have hS3_11718 : S3 11718 =
      (fw_inner_chunk_ce (S2 11712) (S2 6256) (S2 11714)
          (((S2 6256).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
    show applyNode g S2 n2 11718 = _
    exact applyNode_fw_inner_chunk_ce_snd_out_1param g S2 0 1024 11712 6256 11714 11716 11718
      (by decide)
  -- Skip lemmas: nodes n0/n1/n2/n3 not writing specific tids.
  have hS3_11712 : S3 11712 = S2 11712 := by
    show applyNode g S2 n2 11712 = S2 11712; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_6256 : S3 6256 = S2 6256 := by
    show applyNode g S2 n2 6256 = S2 6256; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_11713 : S3 11713 = S2 11713 := by
    show applyNode g S2 n2 11713 = S2 11713; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_11714 : S3 11714 = S2 11714 := by
    show applyNode g S2 n2 11714 = S2 11714; apply applyNode_eq_of_not_mem_outs; decide
  have hS3_11715 : S3 11715 = S2 11715 := by
    show applyNode g S2 n2 11715 = S2 11715; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11712 : S2 11712 = S1 11712 := by
    show applyNode g S1 n1 11712 = S1 11712; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_6256 : S2 6256 = S1 6256 := by
    show applyNode g S1 n1 6256 = S1 6256; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11713 : S2 11713 = S1 11713 := by
    show applyNode g S1 n1 11713 = S1 11713; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11714 : S2 11714 = S1 11714 := by
    show applyNode g S1 n1 11714 = S1 11714; apply applyNode_eq_of_not_mem_outs; decide
  have hS2_11715 : S2 11715 = chunkPrimDimN 0 g.numRanks 1 (S1 4931) := by
    show applyNode g S1 n1 11715 = _; exact applyNode_chunkPrimDimN_out g S1 1 4931 11715 0
  have hS2_4931 : S2 4931 = S1 4931 := by
    show applyNode g S1 n1 4931 = S1 4931; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_11712 : S1 11712 = initPM 11712 := by
    show applyNode g initPM n0 11712 = initPM 11712; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_6256 : S1 6256 = initPM 6256 := by
    show applyNode g initPM n0 6256 = initPM 6256; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_11713 : S1 11713 = initPM 11713 := by
    show applyNode g initPM n0 11713 = initPM 11713; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_11714 : S1 11714 = chunkPrimDimN 0 g.numRanks 0 (initPM 4931) := by
    show applyNode g initPM n0 11714 = _; exact applyNode_chunkPrimDimN_out g initPM 0 4931 11714 0
  have hS1_4931 : S1 4931 = initPM 4931 := by
    show applyNode g initPM n0 4931 = initPM 4931; apply applyNode_eq_of_not_mem_outs; decide
  -- Combine: rewrite S4 → S3 → S2 → S1 → initPM. Use `try` since some rewrites
  -- may not apply (e.g., hS3_11718 already reduces S3 11712 in one branch).
  rw [hS4_11718, hS4_11719, hS3_11718]
  try rw [hS3_11712]
  try rw [hS3_11713]
  try rw [hS3_6256]
  try rw [hS3_6256]  -- second occurrence in the other branch
  try rw [hS3_11714]
  try rw [hS3_11715]
  try rw [hS2_11712]
  try rw [hS2_11713]
  try rw [hS2_6256]
  try rw [hS2_6256]
  try rw [hS2_11714]
  try rw [hS2_11715]
  try rw [hS2_4931]
  try rw [hS1_11712]
  try rw [hS1_11713]
  try rw [hS1_6256]
  try rw [hS1_6256]
  try rw [hS1_11714]
  try rw [hS1_4931]

-- ============================================================
-- Main proof: goal_2_stmt_cut.
--
-- Signature (from Goal_2.lean):
--   CoarseLineageHoldsWithInit sm_goal_2 pm_goal_2 goal_2
--     sm_goal_2InitEnv pm_goal_2InitEnv goal_2_cut_initGoals
--
-- where goal_2_cut_initGoals = initGoals ++ goal_2_prereqs (includes
-- intermediateGoal_6255 giving us initSM 6255 = allGather [initPM 11712,
-- initPM 11713]).
--
-- Plan (per README block earlier):
--   1. Intro initSM, initPM, hSM, hPM, hInit.
--   2. refine ⟨shape_sm, shape_pm, value⟩
--   3. shape_sm: use denote_sm_goal_2_4927 + fw_inner_chunk_ce_snd_shape.
--   4. shape_pm: use denote_pm_goal_2_4927 + fw_inner_chunk_ce_snd_shape +
--      allGatherPrimDimN_shape.
--   5. value: use denote_sm_goal_2_4927 + denote_pm_goal_2_4927 +
--      intermediateGoal_6255 hypothesis (from hInit) +
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
  have h4931_sm : (initSM 4931).shape = [4096] :=
    hSM 4931 [4096] (by native_decide)
  have h6255_sm : (initSM 6255).shape = [4096, 1024] :=
    hSM 6255 [4096, 1024] (by native_decide)
  have h6256_sm : (initSM 6256).shape = [154880, 1024] :=
    hSM 6256 [154880, 1024] (by native_decide)
  have h4931_pm : (initPM 4931).shape = [4096] :=
    hPM 4931 [4096] (by native_decide)
  have h6256_pm : (initPM 6256).shape = [154880, 1024] :=
    hPM 6256 [154880, 1024] (by native_decide)
  have h11712_pm : (initPM 11712).shape = [2048, 1024] :=
    hPM 11712 [2048, 1024] (by native_decide)
  have h11713_pm : (initPM 11713).shape = [2048, 1024] :=
    hPM 11713 [2048, 1024] (by native_decide)
  -- Get intermediateGoal_6255 from hInit: initSM 6255 = reconstruct [initPM 11712, initPM 11713].
  have hg6255 : InitGoalHolds pm_goal_2.numRanks intermediateGoal_6255 initSM initPM := by
    apply hInit
    unfold goal_2_cut_initGoals
    apply List.mem_append_right
    -- intermediateGoal_6255 is in goal_2_prereqs.
    native_decide
  unfold InitGoalHolds at hg6255
  obtain ⟨_, _, hval6255⟩ := hg6255
  simp only [intermediateGoal_6255, List.map, reconstructForGoal, Bool.false_eq_true,
             if_false] at hval6255
  -- pm_goal_2.numRanks = 2.
  have hpmR : pm_goal_2.numRanks = 2 := rfl
  -- reconstructWithDim on [x, y] with non-scalar shape = allGatherPrimDimN.
  have hreconstr :
      reconstructWithDim 0 pm_goal_2.numRanks 0 [initPM 11712, initPM 11713] =
      allGatherPrimDimN 0 pm_goal_2.numRanks 0 [initPM 11712, initPM 11713] := by
    unfold reconstructWithDim
    simp only [List.head?_cons, Option.map_some, Option.getD_some, h11712_pm]
    rfl
  rw [hreconstr] at hval6255
  refine ⟨?shape_sm, ?shape_pm, ?value⟩
  case shape_sm =>
    -- (denoteGraph sm_goal_2 initSM 4927).shape = [4096]
    rw [denote_sm_goal_2_4927]
    -- Use fw_inner_chunk_ce_snd_shape.
    have hL : (initSM 6255).shape.head? = some 4096 := by rw [h6255_sm]; rfl
    have hshape := fw_inner_chunk_ce_snd_shape
      (initSM 6255) (initSM 6256) (initSM 4931)
      (((initSM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar) 4096 hL
    exact hshape
  case shape_pm =>
    -- goal.tpShapes = [[4096]], tps = [{rank:=0, tid:=4927}].
    simp only [List.map]
    rw [denote_pm_goal_2_4927]
    -- Chunk shape lemma: (chunk 0 2 r [4096]).shape = [2048].
    have hchunk_0_shape : (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4931)).shape = [2048] := by
      rw [hpmR, chunkPrimDimN_shape 0 2 0 (initPM 4931) [4096] h4931_pm (by decide)]; rfl
    have hchunk_1_shape : (chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4931)).shape = [2048] := by
      rw [hpmR, chunkPrimDimN_shape 0 2 1 (initPM 4931) [4096] h4931_pm (by decide)]; rfl
    -- Each shard's fw_inner_chunk_ce.snd shape = [2048] (via x.shape.head? = some 2048).
    have hL_r0 : (initPM 11712).shape.head? = some 2048 := by rw [h11712_pm]; rfl
    have hshape_r0 :
        (fw_inner_chunk_ce (initPM 11712) (initPM 6256)
            (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4931))
            (((initPM 6256).shape.head?).getD 0)
            ((0 : Nat) : Scalar)).2.shape = [2048] :=
      fw_inner_chunk_ce_snd_shape (initPM 11712) (initPM 6256) _
        (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar) 2048 hL_r0
    -- head? = some (first shard). Use `2` directly since hpmR : pm_goal_2.numRanks = 2.
    rw [hpmR]
    have hhead : (([(fw_inner_chunk_ce (initPM 11712) (initPM 6256)
          (chunkPrimDimN 0 2 0 (initPM 4931))
          (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar)).2,
        (fw_inner_chunk_ce (initPM 11713) (initPM 6256)
          (chunkPrimDimN 0 2 1 (initPM 4931))
          (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar)).2] : List Tensor).head?.map
          (fun t => t.shape)).getD [] = [2048] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      -- After `rw [hpmR]` above, chunkPrimDimN 0 pm_goal_2.numRanks → chunkPrimDimN 0 2.
      -- But hshape_r0's chunkPrimDimN still uses pm_goal_2.numRanks. Rederive.
      have hL_r0' : (initPM 11712).shape.head? = some 2048 := by rw [h11712_pm]; rfl
      exact fw_inner_chunk_ce_snd_shape (initPM 11712) (initPM 6256) _
        (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar) 2048 hL_r0'
    rw [allGatherPrimDimN_shape 0 2 _ _ hhead]
    rfl
  case value =>
    -- Goal: denoteGraph sm_goal_2 initSM 4927 = reconstructWithDim 0 numRanks 0 [denoteGraph pm_goal_2 initPM 4927]
    simp only [List.map, reconstructForGoal, Bool.false_eq_true, if_false,
               reconstructWithDim_singleton]
    rw [denote_sm_goal_2_4927, denote_pm_goal_2_4927]
    -- Use intermediateGoal_6255 hypothesis: initSM 6255 = allGather [initPM 11712, initPM 11713].
    rw [hval6255]
    -- 4931 unsharded: initSM 4931 = initPM 4931 via initGoal_4931.
    have hg4931 : InitGoalHolds pm_goal_2.numRanks initGoal_4931 initSM initPM := by
      apply hInit
      unfold goal_2_cut_initGoals
      apply List.mem_append_left
      native_decide
    unfold InitGoalHolds at hg4931
    obtain ⟨_, _, hval4931⟩ := hg4931
    simp only [initGoal_4931, List.map, reconstructForGoal, Bool.false_eq_true, if_false,
               reconstructWithDim_singleton] at hval4931
    rw [hval4931]
    -- 6256 unsharded similarly.
    have hg6256 : InitGoalHolds pm_goal_2.numRanks initGoal_6256 initSM initPM := by
      apply hInit
      unfold goal_2_cut_initGoals
      apply List.mem_append_left
      native_decide
    unfold InitGoalHolds at hg6256
    obtain ⟨_, _, hval6256⟩ := hg6256
    simp only [initGoal_6256, List.map, reconstructForGoal, Bool.false_eq_true, if_false,
               reconstructWithDim_singleton] at hval6256
    rw [hval6256]
    -- Now apply the top-level lemma from InnerChunkCEShard.
    -- Goal shape:
    --   (fw_ice (allGather [pm 11712, pm 11713]) (pm 6256) (pm 4931) vocab 0).snd
    --   = allGather [(fw_ice (pm 11712) (pm 6256) (chunk_0 pm 4931) vocab 0).snd,
    --                (fw_ice (pm 11713) (pm 6256) (chunk_1 pm 4931) vocab 0).snd]
    -- Strategy:
    -- (1) Use `fw_inner_chunk_ce_snd_y_independent` to change the y arg on each shard
    --     from `chunk_r (pm 4931)` to `pm 4931` (same for all shards).
    -- (2) Apply `fw_inner_chunk_ce_snd_allGatherDim0_shards` with y = initPM 4931
    --     (unshared, since .snd doesn't depend on y).
    -- (3) Convert List.ofFn (Fin 2) to explicit 2-element list.
    -- Step 1: rewrite each shard's y from chunk to pm 4931.
    have hy0 :
        (fw_inner_chunk_ce (initPM 11712) (initPM 6256)
            (chunkPrimDimN 0 pm_goal_2.numRanks 0 (initPM 4931))
            (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 =
        (fw_inner_chunk_ce (initPM 11712) (initPM 6256) (initPM 4931)
            (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 :=
      fw_inner_chunk_ce_snd_y_independent _ _ _ _ _ _
    have hy1 :
        (fw_inner_chunk_ce (initPM 11713) (initPM 6256)
            (chunkPrimDimN 0 pm_goal_2.numRanks 1 (initPM 4931))
            (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 =
        (fw_inner_chunk_ce (initPM 11713) (initPM 6256) (initPM 4931)
            (((initPM 6256).shape.head?).getD 0) ((0 : Nat) : Scalar)).2 :=
      fw_inner_chunk_ce_snd_y_independent _ _ _ _ _ _
    rw [hy0, hy1]
    -- Step 2: apply main lemma. Get hypotheses.
    have hL_shard_pos : 0 < 2048 := by decide
    have hh_pos : 0 < 1024 := by decide
    have hv_pos : 0 < 154880 := by decide
    have hparts_pos : 0 < pm_goal_2.numRanks := by rw [hpmR]; decide
    have hxs_head_pm : (([initPM 11712, initPM 11713] : List Tensor).head?.map (fun t => t.shape)).getD [] =
        [2048, 1024] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact h11712_pm
    have hxs_shape_pm : ∀ r (_ : r < pm_goal_2.numRanks),
        (([initPM 11712, initPM 11713] : List Tensor).getD r (zeroTensor [2048, 1024])).shape =
        [2048, 1024] := by
      intro r hr
      rw [hpmR] at hr
      interval_cases r
      · exact h11712_pm
      · exact h11713_pm
    -- Vocab reduces to 154880.
    have hvocab_eq : ((initPM 6256).shape.head?).getD 0 = 154880 := by rw [h6256_pm]; rfl
    rw [hvocab_eq]
    -- Apply main lemma.
    rw [fw_inner_chunk_ce_snd_allGatherDim0_shards pm_goal_2.numRanks 2048 1024 154880
      ((0 : Nat) : Scalar) [initPM 11712, initPM 11713] (initPM 6256) (initPM 4931)
      hparts_pos hL_shard_pos hh_pos hv_pos hxs_head_pm hxs_shape_pm h6256_pm]
    -- Step 3: expand List.ofFn (Fin 2) to explicit list.
    rw [hpmR]
    have hofFn : (List.ofFn (n := 2) (fun r : Fin 2 =>
        (fw_inner_chunk_ce (([initPM 11712, initPM 11713] : List Tensor).getD r.val
              (zeroTensor [2048, 1024]))
          (initPM 6256) (initPM 4931) 154880 ((0 : Nat) : Scalar)).snd)) =
        [ (fw_inner_chunk_ce (initPM 11712) (initPM 6256) (initPM 4931) 154880
              ((0 : Nat) : Scalar)).snd,
          (fw_inner_chunk_ce (initPM 11713) (initPM 6256) (initPM 4931) 154880
              ((0 : Nat) : Scalar)).snd ] := by
      rfl
    rw [hofFn]

-- Placeholder proof to be filled in the next iteration.

theorem prove_pattern_2 : pattern_2_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_2

end TrainVerify.Denote.GeneratedPatterns
