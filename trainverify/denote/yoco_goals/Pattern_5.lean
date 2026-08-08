/- Pattern_5 proof: hidden-sharded embedding followed by AllToAll. -/
import denote.yoco_goals.Goal_5
import denote.yoco_goals.BridgeKit
import denote.EmbeddingHiddenShard

set_option linter.style.longLine false
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_5_goalIds : List Nat := [5]
inductive pattern_5_target : Prop → Prop
  | goal_5 : pattern_5_target goal_5_stmt_full

def pattern_5_stmt : Prop :=
  ∀ {target : Prop}, pattern_5_target target → target

/-- SM slice evaluation at the observed embedding output. -/
theorem denote_sm_goal_5_4933 (initSM : Store) :
    denoteGraph sm_goal_5 initSM 4933 = fw_embedding (initSM 4930) (initSM 4932) := by
  unfold denoteGraph
  simp only [sm_goal_5, List.foldl]
  exact applyNode_fw_embedding_out sm_goal_5 initSM 0 4930 4932 4933

/-- Both PM observations evaluate to the corresponding ranks of hidden gather
followed by `(idim = 1, odim = 0)` all-to-all. -/
theorem denote_pm_goal_5_outputs (initPM : Store) :
    denoteGraph pm_goal_5 initPM 7744 =
      allToAllPrimWithDims 2 0
        [fw_embedding (initPM 4930) (initPM 7746),
         fw_embedding (initPM 4930) (initPM 7747)] 1 0 ∧
    denoteGraph pm_goal_5 initPM 7745 =
      allToAllPrimWithDims 2 1
        [fw_embedding (initPM 4930) (initPM 7746),
         fw_embedding (initPM 4930) (initPM 7747)] 1 0 := by
  set g : GraphDecl := { numRanks := 2, nodes :=
    [{ rank := 0, op := "OpName.FW_embedding", ins := [4930, 7746], outs := [7748] },
     { rank := 1, op := "OpName.FW_embedding", ins := [4930, 7747], outs := [7749] },
     { rank := 0, op := "OpName.AllToAllPrim", ins := [7748, 7749], outs := [7744], params := [1, 0] },
     { rank := 1, op := "OpName.AllToAllPrim", ins := [7748, 7749], outs := [7745], params := [1, 0] }] } with hg
  have hpm : pm_goal_5 = g := by rfl
  rw [hpm]
  set n0 : NodeDecl :=
    { rank := 0, op := "OpName.FW_embedding", ins := [4930, 7746], outs := [7748] }
  set n1 : NodeDecl :=
    { rank := 1, op := "OpName.FW_embedding", ins := [4930, 7747], outs := [7749] }
  set n2 : NodeDecl :=
    { rank := 0, op := "OpName.AllToAllPrim", ins := [7748, 7749], outs := [7744], params := [1, 0] }
  set n3 : NodeDecl :=
    { rank := 1, op := "OpName.AllToAllPrim", ins := [7748, 7749], outs := [7745], params := [1, 0] }
  set S1 : Store := applyNode g initPM n0
  set S2 : Store := applyNode g S1 n1
  set S3 : Store := applyNode g S2 n2
  have hS1_7748 : S1 7748 = fw_embedding (initPM 4930) (initPM 7746) := by
    exact applyNode_fw_embedding_out g initPM 0 4930 7746 7748
  have hS1_4930 : S1 4930 = initPM 4930 := by
    apply applyNode_eq_of_not_mem_outs
    decide
  have hS1_7747 : S1 7747 = initPM 7747 := by
    apply applyNode_eq_of_not_mem_outs
    decide
  have hS2_7748 : S2 7748 = fw_embedding (initPM 4930) (initPM 7746) := by
    rw [show S2 7748 = S1 7748 by
      apply applyNode_eq_of_not_mem_outs
      decide]
    exact hS1_7748
  have hS2_7749 : S2 7749 = fw_embedding (initPM 4930) (initPM 7747) := by
    rw [show S2 7749 = fw_embedding (S1 4930) (S1 7747) by
      exact applyNode_fw_embedding_out g S1 1 4930 7747 7749]
    rw [hS1_4930, hS1_7747]
  have hS3_7748 : S3 7748 = fw_embedding (initPM 4930) (initPM 7746) := by
    rw [show S3 7748 = S2 7748 by
      apply applyNode_eq_of_not_mem_outs
      decide]
    exact hS2_7748
  have hS3_7749 : S3 7749 = fw_embedding (initPM 4930) (initPM 7747) := by
    rw [show S3 7749 = S2 7749 by
      apply applyNode_eq_of_not_mem_outs
      decide]
    exact hS2_7749
  refine ⟨?_, ?_⟩
  · have hden : denoteGraph g initPM 7744 = applyNode g S3 n3 7744 := by
      unfold denoteGraph
      simp only [hg, List.foldl]
      rfl
    rw [hden]
    rw [show applyNode g S3 n3 7744 = S3 7744 by
      apply applyNode_eq_of_not_mem_outs
      decide]
    rw [show S3 7744 = allToAllPrimWithDims 2 0 [S2 7748, S2 7749] 1 0 by
      exact applyNode_allToAllPrimWithDims_out g S2 0 [7748, 7749] 7744 1 0]
    rw [hS2_7748, hS2_7749]
  · have hden : denoteGraph g initPM 7745 = applyNode g S3 n3 7745 := by
      unfold denoteGraph
      simp only [hg, List.foldl]
      rfl
    rw [hden]
    rw [show applyNode g S3 n3 7745 =
        allToAllPrimWithDims 2 1 [S3 7748, S3 7749] 1 0 by
      exact applyNode_allToAllPrimWithDims_out g S3 1 [7748, 7749] 7745 1 0]
    rw [hS3_7748, hS3_7749]

/-- Final full-ancestry authority Goal 5, with no model-specific algebraic axiom. -/
theorem prove_goal_5 : goal_5_stmt_full := by
  intro initSM initPM hSM hPM hInit
  simp only [goal_5]
  have h4930sm : (initSM 4930).shape = [4096] :=
    hSM 4930 [4096] (by native_decide)
  have h4932sm : (initSM 4932).shape = [154880, 1024] :=
    hSM 4932 [154880, 1024] (by native_decide)
  have h4930pm : (initPM 4930).shape = [4096] :=
    hPM 4930 [4096] (by native_decide)
  have h7746 : (initPM 7746).shape = [154880, 512] :=
    hPM 7746 [154880, 512] (by native_decide)
  have h7747 : (initPM 7747).shape = [154880, 512] :=
    hPM 7747 [154880, 512] (by native_decide)
  have hpmR : pm_goal_5.numRanks = 2 := rfl
  have hE0 : (fw_embedding (initPM 4930) (initPM 7746)).shape = [4096, 512] := by
    rw [fw_embedding_shape, h4930pm, h7746]
    rfl
  have hE1 : (fw_embedding (initPM 4930) (initPM 7747)).shape = [4096, 512] := by
    rw [fw_embedding_shape, h4930pm, h7747]
    rfl
  have hEhead : (([fw_embedding (initPM 4930) (initPM 7746),
      fw_embedding (initPM 4930) (initPM 7747)].head?.map
      (fun t => t.shape)).getD []) = [4096, 512] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hE0
  have houts := denote_pm_goal_5_outputs initPM
  have hA0 : (allToAllPrimWithDims 2 0
      [fw_embedding (initPM 4930) (initPM 7746),
       fw_embedding (initPM 4930) (initPM 7747)] 1 0).shape = [2048, 1024] := by
    rw [allToAllPrimWithDims_shape 2 0 _ 1 0 [4096, 512] hEhead (by decide)]
    decide
  have hA1 : (allToAllPrimWithDims 2 1
      [fw_embedding (initPM 4930) (initPM 7746),
       fw_embedding (initPM 4930) (initPM 7747)] 1 0).shape = [2048, 1024] := by
    rw [allToAllPrimWithDims_shape 2 1 _ 1 0 [4096, 512] hEhead (by decide)]
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [denote_sm_goal_5_4933, fw_embedding_shape, h4930sm, h4932sm]
    rfl
  · simp only [List.map]
    rw [houts.1, houts.2]
    rw [hA0, hA1]
  · simp only [List.map, reconstructForGoal, Bool.false_eq_true, if_false]
    rw [denote_sm_goal_5_4933, houts.1, houts.2]
    have hInit' : InitGoalsHold pm_goal_5.numRanks initGoals initSM initPM := by
      unfold goal_5_full_initGoals at hInit
      exact hInit
    have hg4930 := hInit' initGoal_4930 (by native_decide)
    unfold InitGoalHolds at hg4930
    obtain ⟨_, _, hval4930⟩ := hg4930
    simp only [initGoal_4930, hpmR, List.map, reconstructForGoal,
      Bool.false_eq_true, if_false, reconstructWithDim_singleton] at hval4930
    rw [hval4930]
    have hg4932 := hInit' initGoal_4932 (by native_decide)
    unfold InitGoalHolds at hg4932
    obtain ⟨_, _, hval4932⟩ := hg4932
    simp only [initGoal_4932, hpmR, List.map, reconstructForGoal,
      Bool.false_eq_true, if_false] at hval4932
    have hreconstructW :
        reconstructWithDim 1 2 0 [initPM 7746, initPM 7747] =
          allGatherPrimDimN 1 2 0 [initPM 7746, initPM 7747] := by
      unfold reconstructWithDim
      simp only [List.head?_cons, Option.map_some, Option.getD_some, h7746]
      rfl
    rw [hreconstructW] at hval4932
    rw [hval4932]
    have hreconstructOut : reconstructWithDim 0 pm_goal_5.numRanks 0
        [allToAllPrimWithDims 2 0
            [fw_embedding (initPM 4930) (initPM 7746),
             fw_embedding (initPM 4930) (initPM 7747)] 1 0,
         allToAllPrimWithDims 2 1
            [fw_embedding (initPM 4930) (initPM 7746),
             fw_embedding (initPM 4930) (initPM 7747)] 1 0] =
      allGatherPrimDimN 0 2 0
        [allToAllPrimWithDims 2 0
            [fw_embedding (initPM 4930) (initPM 7746),
             fw_embedding (initPM 4930) (initPM 7747)] 1 0,
         allToAllPrimWithDims 2 1
            [fw_embedding (initPM 4930) (initPM 7746),
             fw_embedding (initPM 4930) (initPM 7747)] 1 0] := by
      rw [hpmR]
      apply reconstructWithDim_cons_cons_nonscalar
      rw [hA0]
      decide
    rw [hreconstructOut]
    exact fw_embedding_hidden_shards_allToAll_two 2048 154880 512
      (initPM 4930) (initPM 7746) (initPM 7747)
      (by decide) (by decide) (by decide) h4930pm h7746 h7747

theorem prove_pattern_5 : pattern_5_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_5

end TrainVerify.Denote.GeneratedPatterns
