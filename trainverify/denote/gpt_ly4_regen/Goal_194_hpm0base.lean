import denote.gpt_ly4_regen.Goal_194_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_194.lean and restructured for Lean v4.31.
-- The v4.27 proof walked in from the end of the full 12-node fold via
-- `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`; under v4.31 those
-- `by decide` side goals run against the whole graph and make the kernel
-- accumulate def-eq state without converging. Truncating to the prefix that ends
-- at the writing node puts it at the head of the fold, so one rewrite closes it
-- and any remaining skips are decided against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxHeartbeats 400000 in
theorem hpm0base_194 (initPM : Store) :
    (denoteGraph pm_goal_194 initPM) 2382 = allToAllPrimWithDims 4 0
      [(denoteGraph pm_goal_194 initPM) 2429, (denoteGraph pm_goal_194 initPM) 2431,
       (denoteGraph pm_goal_194 initPM) 2433, (denoteGraph pm_goal_194 initPM) 2435] 1 3 := by
  have hL : denoteGraph pm_goal_194 initPM 2382
          = denoteGraph {pm_goal_194 with nodes := pm_goal_194.nodes.take 9} initPM 2382 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_194 initPM 2382 _ _
      (List.take_append_drop 9 _).symm (by decide)
  have hR : ∀ t : Tid, t = 2429 ∨ t = 2431 ∨ t = 2433 ∨ t = 2435 →
      denoteGraph pm_goal_194 initPM t
        = denoteGraph {pm_goal_194 with nodes := pm_goal_194.nodes.take 8} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_194 initPM _ _ _
        (List.take_append_drop 8 _).symm (by decide)
  rw [hL, hR 2429 (by tauto), hR 2431 (by tauto), hR 2433 (by tauto), hR 2435 (by tauto)]
  simp only [pm_goal_194, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
