import denote.gpt_ly4_regen.Goal_236_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_236.lean and restructured for Lean v4.31.
-- The v4.27 proof walked in from the end of the full 12-node fold via
-- `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`; under v4.31 those
-- `by decide` side goals run against the whole graph and make the kernel
-- accumulate def-eq state without converging. Truncating to the prefix that ends
-- at the writing node puts it at the head of the fold, so one rewrite closes it
-- and any remaining skips are decided against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxHeartbeats 400000 in
theorem hpm3base_236 (initPM : Store) :
    (denoteGraph pm_goal_236 initPM) 3092 = allToAllPrimWithDims 4 3
      [(denoteGraph pm_goal_236 initPM) 3109, (denoteGraph pm_goal_236 initPM) 3111,
       (denoteGraph pm_goal_236 initPM) 3113, (denoteGraph pm_goal_236 initPM) 3115] 2 3 := by
  have hL : denoteGraph pm_goal_236 initPM 3092
          = denoteGraph {pm_goal_236 with nodes := pm_goal_236.nodes.take 12} initPM 3092 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_236 initPM 3092 _ _
      (List.take_append_drop 12 _).symm (by decide)
  have hR : ∀ t : Tid, t = 3109 ∨ t = 3111 ∨ t = 3113 ∨ t = 3115 →
      denoteGraph pm_goal_236 initPM t
        = denoteGraph {pm_goal_236 with nodes := pm_goal_236.nodes.take 11} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_236 initPM _ _ _
        (List.take_append_drop 11 _).symm (by decide)
  rw [hL, hR 3109 (by tauto), hR 3111 (by tauto), hR 3113 (by tauto), hR 3115 (by tauto)]
  simp only [pm_goal_236, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
