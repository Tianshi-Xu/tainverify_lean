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
    pm_goal_2 has 5 nodes total; 4674 is written by node[4].

    ⚠️ PARTIAL (sorry): the outer AllGatherPrim step reduces cleanly, but the
    inner value chain (11839, 11840 lookups through nested applyNodes) needs
    tedious step-by-step `applyNode_eq_of_not_mem_outs` calls plus the 1-param
    fw_inner_chunk_ce rewrite. Leaving as a scaffold for next session — the
    strategy is clear, just LOC-heavy. -/
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
  sorry -- Strategy documented above; multi-step applyNode chain reduction.

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
theorem prove_goal_2 : goal_2_stmt_cut := by
  sorry

-- Placeholder proof to be filled in the next iteration.

theorem prove_pattern_2 : pattern_2_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_2

end TrainVerify.Denote.GeneratedPatterns
