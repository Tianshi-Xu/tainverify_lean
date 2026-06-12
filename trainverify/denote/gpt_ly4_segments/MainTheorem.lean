/- Main composition theorem for the gpt_ly4 (46-goal, observable-only) scope.

   This file is hand-written (not auto-generated). It composes the 46 per-goal
   obligations `prove_goal_1 .. prove_goal_46` (defined in GeneratedData.lean)
   into the single top-level statement `all_goals_stmt`.

   Scope note: per `Verdict/graph_to_lean.py` design, goals are emitted ONLY for
   *observable* output tensors (final loss + every weight gradient), NOT for
   intermediate activations. For this GPT-2 ly4 graph that is exactly 46 goals
   (45 backward weight/param gradients + 1 forward loss). Proving SM/PM coarse
   lineage for all observables establishes the parallel/single-machine training
   equivalence; intermediate activations are internal and legitimately sharded
   differently, so they are not part of the observable contract.
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedMain

/-- The full graph theorem: every observable goal holds (SM/PM coarse lineage). -/
theorem gpt_main_all_goals : all_goals_stmt := by
  unfold all_goals_stmt
  intro g hg
  simp only [goals, goalChunk_1, goalChunk_2, goalChunk_3, goalChunk_4,
    goalChunk_5, goalChunk_6, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact prove_goal_1
  · exact prove_goal_2
  · exact prove_goal_3
  · exact prove_goal_4
  · exact prove_goal_5
  · exact prove_goal_6
  · exact prove_goal_7
  · exact prove_goal_8
  · exact prove_goal_9
  · exact prove_goal_10
  · exact prove_goal_11
  · exact prove_goal_12
  · exact prove_goal_13
  · exact prove_goal_14
  · exact prove_goal_15
  · exact prove_goal_16
  · exact prove_goal_17
  · exact prove_goal_18
  · exact prove_goal_19
  · exact prove_goal_20
  · exact prove_goal_21
  · exact prove_goal_22
  · exact prove_goal_23
  · exact prove_goal_24
  · exact prove_goal_25
  · exact prove_goal_26
  · exact prove_goal_27
  · exact prove_goal_28
  · exact prove_goal_29
  · exact prove_goal_30
  · exact prove_goal_31
  · exact prove_goal_32
  · exact prove_goal_33
  · exact prove_goal_34
  · exact prove_goal_35
  · exact prove_goal_36
  · exact prove_goal_37
  · exact prove_goal_38
  · exact prove_goal_39
  · exact prove_goal_40
  · exact prove_goal_41
  · exact prove_goal_42
  · exact prove_goal_43
  · exact prove_goal_44
  · exact prove_goal_45
  · exact prove_goal_46

end TrainVerify.Denote.GeneratedMain
