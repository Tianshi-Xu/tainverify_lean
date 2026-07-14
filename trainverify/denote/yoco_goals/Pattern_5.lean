/- Pattern_5 proof: goal_5_stmt_cut.
   Pattern: 5
   Hash: 70ae1240263b50ea
   Goals: 5
   Op flavour: FW_embedding vocab-parallel
     SM=1 op (fw_embedding), PM=3 ops (2×FW_embedding + AllReducePrim)

   Migrated from goal_5_stmt (uncut, on global sm/pm) to goal_5_stmt_cut
   (on sm_goal_5/pm_goal_5 slices) per A-path decision 2026-07-02.
   Since Pattern_5 is a "base" goal, goal_5_cut_initGoals = initGoals
   (no intermediate prereqs), so the hInit hypothesis provides
   initGoal_4677 and initGoal_4679 directly.
-/
import denote.yoco_goals.Goal_5
import denote.yoco_goals.BridgeKit

set_option linter.style.longLine false
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_5_goalIds : List Nat := [5]
inductive pattern_5_target : Prop → Prop
  | goal_5 : pattern_5_target goal_5_stmt_cut

def pattern_5_stmt : Prop :=
  ∀ {target : Prop}, pattern_5_target target → target

-- ============================================================
-- Slice-side denotation helpers for tid 4680.
-- ============================================================

/-- SM slice: `denoteGraph sm_goal_5 initSM 4680 = fw_embedding (initSM 4677) (initSM 4679)`. -/
theorem denote_sm_goal_5_4680 (initSM : Store) :
    denoteGraph sm_goal_5 initSM 4680 = fw_embedding (initSM 4677) (initSM 4679) := by
  unfold denoteGraph
  simp only [sm_goal_5, List.foldl]
  exact applyNode_fw_embedding_out sm_goal_5 initSM 0 4677 4679 4680

/-- PM slice: `denoteGraph pm_goal_5 initPM 4680` unfolds all 3 nodes. -/
theorem denote_pm_goal_5_4680 (initPM : Store) :
    denoteGraph pm_goal_5 initPM 4680 =
      allReducePrim pm_goal_5.numRanks 0
        [ fw_embedding_offset 0 (initPM 4677) (initPM 7389),
          fw_embedding_offset 77440 (initPM 4677) (initPM 7390) ] := by
  set g : GraphDecl := { numRanks := 2, nodes :=
    [{ rank := 0, op := "OpName.FW_embedding", ins := [4677, 7389], outs := [7391], params := [0] },
     { rank := 1, op := "OpName.FW_embedding", ins := [4677, 7390], outs := [7392], params := [77440] },
     { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] }] } with hg_def
  have hpm_eq : pm_goal_5 = g := by show pm_goal_5 = _; rfl
  rw [hpm_eq]
  -- Node literals.
  set n0 : NodeDecl :=
    { rank := 0, op := "OpName.FW_embedding", ins := [4677, 7389], outs := [7391], params := [0] } with hn0
  set n1 : NodeDecl :=
    { rank := 1, op := "OpName.FW_embedding", ins := [4677, 7390], outs := [7392], params := [77440] } with hn1
  set n2 : NodeDecl :=
    { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] } with hn2
  -- Intermediate stores.
  set S1 : Store := applyNode g initPM n0 with hS1
  set S2 : Store := applyNode g S1 n1 with hS2
  -- Unfold to applyNode g S2 n2 4680.
  have hgoal : denoteGraph g initPM 4680 = applyNode g S2 n2 4680 := by
    show (g.nodes.foldl (applyNode g) initPM) 4680 = _
    simp only [hg_def, List.foldl]
    rfl
  rw [hgoal]
  -- Apply AllReducePrim.
  rw [applyNode_allReducePrim_out g S2 0 [7391, 7392] 4680]
  simp only [List.map_cons, List.map_nil]
  -- Reduce S2 7391: n1 doesn't write 7391 (writes 7392).
  have hS2_7391 : S2 7391 = S1 7391 := by
    show applyNode g S1 n1 7391 = S1 7391; apply applyNode_eq_of_not_mem_outs; decide
  -- Reduce S2 7392: n1 writes 7392 via fw_embedding_offset.
  have hS2_7392 : S2 7392 = fw_embedding_offset 77440 (S1 4677) (S1 7390) := by
    show applyNode g S1 n1 7392 = _
    exact applyNode_fw_embedding_offset_out g S1 1 77440 4677 7390 7392
  -- Reduce S1 lookups.
  have hS1_7391 : S1 7391 = fw_embedding_offset 0 (initPM 4677) (initPM 7389) := by
    show applyNode g initPM n0 7391 = _
    exact applyNode_fw_embedding_offset_out g initPM 0 0 4677 7389 7391
  have hS1_4677 : S1 4677 = initPM 4677 := by
    show applyNode g initPM n0 4677 = initPM 4677; apply applyNode_eq_of_not_mem_outs; decide
  have hS1_7390 : S1 7390 = initPM 7390 := by
    show applyNode g initPM n0 7390 = initPM 7390; apply applyNode_eq_of_not_mem_outs; decide
  rw [hS2_7391, hS2_7392, hS1_7391, hS1_4677, hS1_7390]

-- ============================================================
-- Main proof: goal_5_stmt_cut.
-- ============================================================

theorem prove_goal_5 : goal_5_stmt_cut := by
  intro initSM initPM hSM hPM hInit
  simp only [goal_5]
  -- Shape witnesses.
  have h4677_sm : (initSM 4677).shape = [4096] :=
    hSM 4677 [4096] (by native_decide)
  have h4679_sm : (initSM 4679).shape = [154880, 1024] :=
    hSM 4679 [154880, 1024] (by native_decide)
  have h4677_pm : (initPM 4677).shape = [4096] :=
    hPM 4677 [4096] (by native_decide)
  have h7389_pm : (initPM 7389).shape = [77440, 1024] :=
    hPM 7389 [77440, 1024] (by native_decide)
  have h7390_pm : (initPM 7390).shape = [77440, 1024] :=
    hPM 7390 [77440, 1024] (by native_decide)
  have hpmR : pm_goal_5.numRanks = 2 := rfl
  refine ⟨?shape_sm, ?shape_pm, ?value⟩
  case shape_sm =>
    rw [denote_sm_goal_5_4680, fw_embedding_shape, h4677_sm, h4679_sm]
    rfl
  case shape_pm =>
    simp only [List.map]
    rw [denote_pm_goal_5_4680]
    have hhead : ([fw_embedding_offset 0 (initPM 4677) (initPM 7389),
                   fw_embedding_offset 77440 (initPM 4677) (initPM 7390)]).head?
                 = some (fw_embedding_offset 0 (initPM 4677) (initPM 7389)) := rfl
    rw [hpmR]
    rw [allReducePrim_shape 2 0 _ _ hhead]
    rw [fw_embedding_offset_shape, h4677_pm, h7389_pm]
    rfl
  case value =>
    -- Value: sm_goal_5 4680 = reconstruct 0 numRanks 0 [pm_goal_5 4680]
    simp only [List.map, reconstructForGoal, Bool.false_eq_true, if_false,
               reconstructWithDim_singleton]
    rw [denote_sm_goal_5_4680, denote_pm_goal_5_4680]
    -- Use goal_5_cut_initGoals = initGoals, so hInit gives initGoal_4679 etc.
    have hInit' : InitGoalsHold pm_goal_5.numRanks initGoals initSM initPM := by
      unfold goal_5_cut_initGoals at hInit
      exact hInit
    have hg4679 := hInit' initGoal_4679 (by native_decide)
    unfold InitGoalHolds at hg4679
    obtain ⟨_, _, hval⟩ := hg4679
    simp only [initGoal_4679, hpmR, List.map, reconstructForGoal, Bool.false_eq_true,
               if_false] at hval
    have hreconstr :
        reconstructWithDim 0 2 0 [initPM 7389, initPM 7390] =
        allGatherPrimDimN 0 2 0 [initPM 7389, initPM 7390] := by
      unfold reconstructWithDim
      simp only [List.head?_cons, Option.map_some, Option.getD_some, h7389_pm]
      rfl
    rw [hreconstr] at hval
    rw [hval]
    -- initSM 4677 = initPM 4677 via initGoal_4677.
    have hg4677 := hInit' initGoal_4677 (by native_decide)
    unfold InitGoalHolds at hg4677
    obtain ⟨_, _, hval2⟩ := hg4677
    simp only [initGoal_4677, hpmR, List.map, reconstructForGoal, Bool.false_eq_true,
               if_false, reconstructWithDim_singleton] at hval2
    rw [hval2]
    -- Apply the top-level vocab-parallel embedding lemma.
    have hWs_head :
        (([initPM 7389, initPM 7390] : List Tensor).head?.map (fun t => t.shape)).getD [] =
        [77440, 1024] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact h7389_pm
    have hWs_shape : ∀ r (_ : r < 2),
        (([initPM 7389, initPM 7390]).getD r (zeroTensor [77440, 1024])).shape =
        [77440, 1024] := by
      intro r hr
      interval_cases r
      · exact h7389_pm
      · exact h7390_pm
    have hlen : ([initPM 7389, initPM 7390] : List Tensor).length = 2 := rfl
    have h := fw_embedding_eq_allReduce_offset_shards 2 77440 1024
      (by decide) (by decide) (by decide)
      (initPM 4677) [initPM 7389, initPM 7390] hlen hWs_head hWs_shape
    rw [hpmR]
    rw [h]
    have hofFn :
        (List.ofFn (fun r : Fin 2 =>
          fw_embedding_offset (r.val * 77440) (initPM 4677)
            ([initPM 7389, initPM 7390].getD r.val (zeroTensor [77440, 1024])))) =
        [fw_embedding_offset 0 (initPM 4677) (initPM 7389),
         fw_embedding_offset 77440 (initPM 4677) (initPM 7390)] := rfl
    rw [hofFn]

-- ============================================================
-- Pattern wrapper.
-- ============================================================

theorem prove_pattern_5 : pattern_5_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_5

end TrainVerify.Denote.GeneratedPatterns
