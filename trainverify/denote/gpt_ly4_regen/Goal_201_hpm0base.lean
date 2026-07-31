import denote.gpt_ly4_regen.Goal_201_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_201.lean and restructured for Lean v4.31.
-- The v4.27 proof walked in from the end of the full 12-node fold via
-- `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`; under v4.31 those
-- `by decide` side goals run against the whole graph and make the kernel
-- accumulate def-eq state without converging. Truncating to the prefix that ends
-- at the writing node puts it at the head of the fold, so one rewrite closes it
-- and any remaining skips are decided against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxHeartbeats 400000 in
theorem hpm0base_201 (initPM : Store) :
    (denoteGraph pm_goal_201 initPM) 2519 = allToAllPrimWithDims 4 0
      [(denoteGraph pm_goal_201 initPM) 2545, (denoteGraph pm_goal_201 initPM) 2547,
       (denoteGraph pm_goal_201 initPM) 2549, (denoteGraph pm_goal_201 initPM) 2551] 2 1 := by
  have hL : denoteGraph pm_goal_201 initPM 2519
          = denoteGraph {pm_goal_201 with nodes := pm_goal_201.nodes.take 9} initPM 2519 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_201 initPM 2519 _ _
      (List.take_append_drop 9 _).symm (by decide)
  have hR : ∀ t : Tid, t = 2545 ∨ t = 2547 ∨ t = 2549 ∨ t = 2551 →
      denoteGraph pm_goal_201 initPM t
        = denoteGraph {pm_goal_201 with nodes := pm_goal_201.nodes.take 8} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_201 initPM _ _ _
        (List.take_append_drop 8 _).symm (by decide)
  rw [hL, hR 2545 (by tauto), hR 2547 (by tauto), hR 2549 (by tauto), hR 2551 (by tauto)]
  simp only [pm_goal_201, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
