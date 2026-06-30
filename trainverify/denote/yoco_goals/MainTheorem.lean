/- Auto-generated main composition skeleton.
   This file composes reusable pattern proofs into all_goals_stmt.
-/
import denote.yoco_goals.Instances

set_option maxRecDepth 100000

set_option linter.style.emptyLine false

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedPatternInstances

namespace TrainVerify.Denote.GeneratedMain

def fullGraphSegment : SegmentDecl :=
  { name := "full", sm := sm, pm := pm, goals := goals }

def graphSegments : List SegmentDecl := [fullGraphSegment]

theorem graphSegments_cover : GraphCoverage sm pm graphSegments := by
  unfold GraphCoverage concatSMGraph concatPMGraph graphSegments fullGraphSegment
  refine ⟨rfl, rfl⟩

theorem forall_mem_append_goal {xs ys : List LineageGoal}
    (hx : ∀ g ∈ xs, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals)
    (hy : ∀ g ∈ ys, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals) :
    ∀ g ∈ xs ++ ys, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  have h := List.mem_append.mp hg
  cases h with
  | inl h => exact hx g h
  | inr h => exact hy g h

/-- Main generated composition theorem.

Assuming every reusable Pattern_N proof is complete, this file instantiates
those proofs for every concrete goal and composes them into `all_goals_stmt`.
It deliberately stops at the lineage-goal layer rather than claiming a
stronger full-graph equivalence theorem.
-/

theorem gpt_goal_chunk_1_all : ∀ g ∈ goalChunk_1, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_1 at hg
  cases hg with
  | head =>
    exact prove_goal_1_from_pattern_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_2_from_pattern_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_3_from_pattern_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_4_from_pattern_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_5_from_pattern_5
          | tail _ hg =>
            cases hg

theorem gpt_main_all_goals : all_goals_stmt := by
  unfold all_goals_stmt goals
  exact gpt_goal_chunk_1_all

end TrainVerify.Denote.GeneratedMain

