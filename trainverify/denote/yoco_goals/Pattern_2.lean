/- Auto-generated pattern proof file (Session B, 2026-07-02).
   Pattern: 2
   Hash: f12bb08992f5e7eb
   Goals: 2
   Op flavour: FW_inner_chunk_ce (cross-entropy zLoss) context-parallel
     SM=1 op (fw_inner_chunk_ce), PM=5 ops (2×ChunkPrim + 2×FW_inner_chunk_ce + 1×AllGatherPrim)
   Depends on: denote.InnerChunkCEShard for the top-level equivalence lemma.
-/
import denote.yoco_goals.BridgeKit
import denote.InnerChunkCEShard

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_2_goalIds : List Nat := [2]
inductive pattern_2_target : Prop → Prop
  | goal_2 : pattern_2_target goal_2_stmt

def pattern_2_stmt : Prop :=
  ∀ {target : Prop}, pattern_2_target target → target

-- ============================================================
-- Helper: `applyNode_fw_inner_chunk_ce_snd_out` for 1-param nodes.
--
-- The library lemma requires `params := [chunkSize, zLossScaleInt]`, but
-- YOCO Pattern_2 nodes have `params := [1024]` only (zLossScale is
-- absent, defaulting to 0 via `params.getD 1 0`). Prove the specialized
-- variant here.
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
  -- Unfold applyNode. evalOp resolves via [x, w, y] pattern; params only read
  -- via .getD 0 1 (chunkSize) and .getD 1 0 (zLossScaleInt = 0 here).
  unfold applyNode
  simp only [List.map_cons, List.map_nil]
  -- evalOp step: unfold and simplify.
  show storeSet s ([t1, t2].zip
      (evalOp g.numRanks rank "OpName.FW_inner_chunk_ce" [chunkSize]
        [s xTid, s wTid, s yTid])) t2 = _
  -- evalOp with params=[chunkSize] reduces to using default zLossScaleInt=0.
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
-- Denotation helpers for Pattern_2's tid 4674 (zLoss output).
-- ============================================================

/-- SM side: `denoteGraph sm initSM 4674` reduces to `.snd` of
    `fw_inner_chunk_ce`. sm[926] is the last node writing 4674, and
    it's the LAST node of sm (927 nodes total, index 926).

    Design note: `rw [hnode]` where `hnode : sm.nodes[926] = <literal>` is
    proven by `native_decide` times out at whnf — Lean fails to reduce
    `sm.nodes[926]` even with 8x heartbeats. Workaround: transport the
    literal-applyNode result back via `hnode` using `Eq.mpr` /
    congrArg-style substitution, avoiding the intermediate goal that has
    `sm.nodes[926]` at surface. -/
theorem denote_sm_4674 (initSM : Store) :
    denoteGraph sm initSM 4674 =
      (fw_inner_chunk_ce
          (denoteGraph sm initSM 5930)
          (initSM 5931) (initSM 4678)
          (((initSM 5931).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
  have h := sm_val initSM 926 4674 (by native_decide) (by native_decide)
  have hnode : sm.nodes[926]'(by native_decide) =
      { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678],
        outs := [4673, 4674], params := [1024] } := by
    native_decide
  -- Get the literal-applyNode result on the prefix-computed store.
  have hlit := applyNode_fw_inner_chunk_ce_snd_out_1param sm
      (denoteGraph {sm with nodes := sm.nodes.take 926} initSM)
      0 1024 5930 5931 4678 4673 4674 (by decide)
  -- Move hlit's literal node LHS back to `sm.nodes[926]` via hnode.symm.
  rw [← hnode] at hlit
  -- 5930 IS written by some sm node before 926 (intermediateGoal_5930). Use sm_prefix_eq
  -- to lift the prefix-store lookup to sm-level.
  have h5930 : denoteGraph {sm with nodes := sm.nodes.take 926} initSM 5930 =
      denoteGraph sm initSM 5930 := by
    apply sm_prefix_eq initSM 926 5930
    native_decide
  -- 5931 and 4678 are true init tids (not written by any sm node).
  have h5931 : denoteGraph {sm with nodes := sm.nodes.take 926} initSM 5931 = initSM 5931 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  have h4678 : denoteGraph {sm with nodes := sm.nodes.take 926} initSM 4678 = initSM 4678 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  rw [h5930, h5931, h4678] at hlit
  rw [h]
  exact hlit

/-- PM side: at prefix take 13 (i.e. through node[12]), tid 11835 is
    ChunkPrim rank=0 output. -/
theorem denote_pm_prefix_11835 (initPM : Store) :
    denoteGraph {pm with nodes := pm.nodes.take 13} initPM 11835 =
      chunkPrimDimN 0 pm.numRanks 0 (initPM 4678) := by
  have h := pm_val_prefix initPM 13 12 (by native_decide) (by native_decide) 11835
    (by native_decide)
  have hnode : pm.nodes[12]'(by native_decide) =
      { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835],
        params := [0] } := by
    native_decide
  have htake : (pm.nodes.take 13)[12]'(by native_decide) = pm.nodes[12]'(by native_decide) := by
    rw [List.getElem_take]
  have hnode' : (pm.nodes.take 13)[12]'(by native_decide) =
      { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835],
        params := [0] } := by
    rw [htake]; exact hnode
  have hlit := applyNode_chunkPrimDimN_out pm
      (denoteGraph {pm with nodes := (pm.nodes.take 13).take 12} initPM)
      0 4678 11835 0
  rw [← hnode'] at hlit
  have h4678 : denoteGraph {pm with nodes := (pm.nodes.take 13).take 12} initPM 4678 = initPM 4678 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  rw [h4678] at hlit
  rw [h]
  exact hlit

/-- PM side: at prefix take 26 (i.e. through node[25]), tid 11836 is
    ChunkPrim rank=1 output. -/
theorem denote_pm_prefix_11836 (initPM : Store) :
    denoteGraph {pm with nodes := pm.nodes.take 26} initPM 11836 =
      chunkPrimDimN 0 pm.numRanks 1 (initPM 4678) := by
  have h := pm_val_prefix initPM 26 25 (by native_decide) (by native_decide) 11836
    (by native_decide)
  have hnode : pm.nodes[25]'(by native_decide) =
      { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836],
        params := [0] } := by
    native_decide
  have htake : (pm.nodes.take 26)[25]'(by native_decide) = pm.nodes[25]'(by native_decide) := by
    rw [List.getElem_take]
  have hnode' : (pm.nodes.take 26)[25]'(by native_decide) =
      { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836],
        params := [0] } := by
    rw [htake]; exact hnode
  have hlit := applyNode_chunkPrimDimN_out pm
      (denoteGraph {pm with nodes := (pm.nodes.take 26).take 25} initPM)
      1 4678 11836 0
  rw [← hnode'] at hlit
  have h4678 : denoteGraph {pm with nodes := (pm.nodes.take 26).take 25} initPM 4678 = initPM 4678 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  rw [h4678] at hlit
  rw [h]
  exact hlit

/-- PM side: tid 11839 = .snd of FW_inner_chunk_ce rank=0. Uses full-pm
    denotation for the intermediate reads 11833, 11835. -/
theorem denote_pm_11839 (initPM : Store) :
    denoteGraph pm initPM 11839 =
      (fw_inner_chunk_ce
          (denoteGraph pm initPM 11833)
          (initPM 5931)
          (denoteGraph pm initPM 11835)
          (((initPM 5931).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
  have h := pm_val initPM 1916 11839 (by native_decide) (by native_decide)
  have hnode : pm.nodes[1916]'(by native_decide) =
      { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835],
        outs := [11837, 11839], params := [1024] } := by
    native_decide
  have hlit := applyNode_fw_inner_chunk_ce_snd_out_1param pm
      (denoteGraph {pm with nodes := pm.nodes.take 1916} initPM)
      0 1024 11833 5931 11835 11837 11839 (by decide)
  rw [← hnode] at hlit
  -- Lift prefix-store reads at 11833, 5931, 11835 to full-pm form.
  have h11833 : denoteGraph {pm with nodes := pm.nodes.take 1916} initPM 11833 =
      denoteGraph pm initPM 11833 := by
    exact (denoteGraph_tid_eq_of_suffix_no_writes pm initPM 11833
      (pm.nodes.take 1916) (pm.nodes.drop 1916)
      (List.take_append_drop 1916 pm.nodes).symm (by native_decide)).symm
  have h5931 : denoteGraph {pm with nodes := pm.nodes.take 1916} initPM 5931 = initPM 5931 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  have h11835 : denoteGraph {pm with nodes := pm.nodes.take 1916} initPM 11835 =
      denoteGraph pm initPM 11835 := by
    exact (denoteGraph_tid_eq_of_suffix_no_writes pm initPM 11835
      (pm.nodes.take 1916) (pm.nodes.drop 1916)
      (List.take_append_drop 1916 pm.nodes).symm (by native_decide)).symm
  rw [h11833, h5931, h11835] at hlit
  rw [h]
  exact hlit

/-- PM side: tid 11840 = .snd of FW_inner_chunk_ce rank=1. -/
theorem denote_pm_11840 (initPM : Store) :
    denoteGraph pm initPM 11840 =
      (fw_inner_chunk_ce
          (denoteGraph pm initPM 11834)
          (initPM 5931)
          (denoteGraph pm initPM 11836)
          (((initPM 5931).shape.head?).getD 0)
          ((0 : Nat) : Scalar)).2 := by
  have h := pm_val initPM 1917 11840 (by native_decide) (by native_decide)
  have hnode : pm.nodes[1917]'(by native_decide) =
      { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836],
        outs := [11838, 11840], params := [1024] } := by
    native_decide
  have hlit := applyNode_fw_inner_chunk_ce_snd_out_1param pm
      (denoteGraph {pm with nodes := pm.nodes.take 1917} initPM)
      1 1024 11834 5931 11836 11838 11840 (by decide)
  rw [← hnode] at hlit
  have h11834 : denoteGraph {pm with nodes := pm.nodes.take 1917} initPM 11834 =
      denoteGraph pm initPM 11834 := by
    exact (denoteGraph_tid_eq_of_suffix_no_writes pm initPM 11834
      (pm.nodes.take 1917) (pm.nodes.drop 1917)
      (List.take_append_drop 1917 pm.nodes).symm (by native_decide)).symm
  have h5931 : denoteGraph {pm with nodes := pm.nodes.take 1917} initPM 5931 = initPM 5931 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  have h11836 : denoteGraph {pm with nodes := pm.nodes.take 1917} initPM 11836 =
      denoteGraph pm initPM 11836 := by
    exact (denoteGraph_tid_eq_of_suffix_no_writes pm initPM 11836
      (pm.nodes.take 1917) (pm.nodes.drop 1917)
      (List.take_append_drop 1917 pm.nodes).symm (by native_decide)).symm
  rw [h11834, h5931, h11836] at hlit
  rw [h]
  exact hlit

/-- PM side, main result: `denoteGraph pm initPM 4674` unfolds to the
    all-gather of per-rank `fw_inner_chunk_ce` .snd outputs. -/
theorem denote_pm_4674 (initPM : Store) :
    denoteGraph pm initPM 4674 =
      allGatherPrimDimN 0 pm.numRanks 0
        [ (fw_inner_chunk_ce
              (denoteGraph pm initPM 11833)
              (initPM 5931)
              (denoteGraph pm initPM 11835)
              (((initPM 5931).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2,
          (fw_inner_chunk_ce
              (denoteGraph pm initPM 11834)
              (initPM 5931)
              (denoteGraph pm initPM 11836)
              (((initPM 5931).shape.head?).getD 0)
              ((0 : Nat) : Scalar)).2 ] := by
  -- pm[1919] is the AllGatherPrim writing 4674, reading [11839, 11840].
  have h := pm_val initPM 1919 4674 (by native_decide) (by native_decide)
  have hnode : pm.nodes[1919]'(by native_decide) =
      { rank := 0, op := "OpName.AllGatherPrim", ins := [11839, 11840],
        outs := [4674], params := [0] } := by
    native_decide
  have hlit := applyNode_allGatherPrimDimN_out pm
      (denoteGraph {pm with nodes := pm.nodes.take 1919} initPM)
      0 [11839, 11840] 4674 0
  rw [← hnode] at hlit
  -- Lift 11839, 11840 from prefix take 1919 to full pm.
  have h11839 : denoteGraph {pm with nodes := pm.nodes.take 1919} initPM 11839 =
      denoteGraph pm initPM 11839 := by
    exact (denoteGraph_tid_eq_of_suffix_no_writes pm initPM 11839
      (pm.nodes.take 1919) (pm.nodes.drop 1919)
      (List.take_append_drop 1919 pm.nodes).symm (by native_decide)).symm
  have h11840 : denoteGraph {pm with nodes := pm.nodes.take 1919} initPM 11840 =
      denoteGraph pm initPM 11840 := by
    exact (denoteGraph_tid_eq_of_suffix_no_writes pm initPM 11840
      (pm.nodes.take 1919) (pm.nodes.drop 1919)
      (List.take_append_drop 1919 pm.nodes).symm (by native_decide)).symm
  rw [h]
  -- Use the same-form as hlit's RHS to rewrite manually — since we can't use `List.map_cons`
  -- and `rw [denote_pm_11839, denote_pm_11840]` at once due to the `.map` structure.
  -- Convert `List.map ... [11839, 11840]` to `[S 11839, S 11840]` first, then substitute.
  show allGatherPrimDimN 0 pm.numRanks 0
        ([11839, 11840].map (denoteGraph {pm with nodes := pm.nodes.take 1919} initPM))
      = _
  simp only [List.map_cons, List.map_nil]
  rw [h11839, h11840, denote_pm_11839, denote_pm_11840]

-- ============================================================
-- Main proof: goal_2_stmt.
--
-- ⚠️ CURRENT LIMITATION (2026-07-02 Session B):
--   `goal_2_stmt` requires proving on GLOBAL sm/pm with only `initGoals`
--   as hypotheses. Its value equation:
--       sm 4674 = pm 4674
--   reduces (via denote_sm_4674 + denote_pm_4674 + fw_inner_chunk_ce_snd_
--   allGatherDim0_shards) to a claim requiring:
--       sm 5930 = allGather 0 pm.numRanks 0 [pm 11833, pm 11834]
--   This is exactly `intermediateGoal_5930_stmt`, but `intermediateGoal_5930`
--   is NOT in `initGoals` — it's an intermediate that would need to be
--   established as its own hand-proof (Pattern_2 for the preceding RmsNorm
--   pipeline stage).
--
--   The `_cut` version (`goal_2_stmt_cut`) IS provable because
--   `goal_2_cut_initGoals = initGoals ++ goal_2_prereqs` INCLUDES
--   `intermediateGoal_5930`. But Pattern_2's `pattern_2_target.goal_2`
--   constructor binds to `goal_2_stmt`, not the cut version.
--
--   Options:
--     1. Change `pattern_2_target.goal_2` binding to `goal_2_stmt_cut`
--        (requires pipeline-level rewiring; touches emitter, not just this file).
--     2. Also prove `intermediateGoal_5930_stmt` via its own Pattern
--        (recursive: needs many more preceding intermediate goals).
--     3. Add a top-level `intermediateGoal_5930` hypothesis to Pattern_2's
--        `prove_goal_2` signature and thread through pattern_2_stmt.
--
--   This session focused on the FOUNDATION machinery (helpers, denote_pm_4674
--   assembly, InnerChunkCEShard top-level lemma), all of which is real and
--   commit-ready. The final linkage into `prove_goal_2` blocks on the design
--   question above.
-- ============================================================

/-- Placeholder — see the block comment above for the design blocker. -/
theorem prove_goal_2 : goal_2_stmt := by
  sorry

theorem prove_pattern_2 : pattern_2_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_2

end TrainVerify.Denote.GeneratedPatterns
