import denote.gpt_ly4_regen.Goal_234_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_234.lean and restructured for Lean v4.31.
-- The v4.27 proof reduced this against the full 12-node fold; under v4.31 the
-- `by decide` side goals of `repeat rw [applyNode_eq_of_not_mem_outs]`, and the
-- trailing `rfl`, make the kernel accumulate def-eq state without converging
-- (~3.5 GB/min; 27+ GB RSS measured on Goal_124). Truncating to the prefix that
-- ends at the writing node puts it at the head of the fold, so the same rewrites
-- close it against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem hpm0base_234 (initPM : Store) :
    (denoteGraph pm_goal_234 initPM) 3034 = allToAllPrimWithDims 4 0 [(denoteGraph pm_goal_234 initPM) 3057, (denoteGraph pm_goal_234 initPM) 3059, (denoteGraph pm_goal_234 initPM) 3061, (denoteGraph pm_goal_234 initPM) 3063] 1 2 := by
  have hL : denoteGraph pm_goal_234 initPM 3034
          = denoteGraph {pm_goal_234 with nodes := pm_goal_234.nodes.take 9} initPM 3034 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_234 initPM 3034 _ _
      (List.take_append_drop 9 _).symm (by decide)
  have hR : ∀ t : Tid, t = 3057 ∨ t = 3059 ∨ t = 3061 ∨ t = 3063 →
      denoteGraph pm_goal_234 initPM t
        = denoteGraph {pm_goal_234 with nodes := pm_goal_234.nodes.take 8} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_234 initPM _ _ _
        (List.take_append_drop 8 _).symm (by decide)
  rw [hL, hR 3057 (by tauto), hR 3059 (by tauto), hR 3061 (by tauto), hR 3063 (by tauto)]
  simp only [pm_goal_234, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
