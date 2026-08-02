import denote.gpt_ly4_regen.Goal_229_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_229.lean and restructured for Lean v4.31.
-- The v4.27 proof walked in from the end of the full 12-node fold via
-- `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`; under v4.31 those
-- `by decide` side goals run against the whole graph and make the kernel
-- accumulate def-eq state without converging. Truncating to the prefix that ends
-- at the writing node puts it at the head of the fold, so one rewrite closes it
-- and any remaining skips are decided against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxHeartbeats 400000 in
theorem hpm0base_229 (initPM : Store) :
    (denoteGraph pm_goal_229 initPM) 2938 = allToAllPrimWithDims 4 0
      [(denoteGraph pm_goal_229 initPM) 2985, (denoteGraph pm_goal_229 initPM) 2987,
       (denoteGraph pm_goal_229 initPM) 2989, (denoteGraph pm_goal_229 initPM) 2991] 2 3 := by
  have hL : denoteGraph pm_goal_229 initPM 2938
          = denoteGraph {pm_goal_229 with nodes := pm_goal_229.nodes.take 9} initPM 2938 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_229 initPM 2938 _ _
      (List.take_append_drop 9 _).symm (by decide)
  have hR : ∀ t : Tid, t = 2985 ∨ t = 2987 ∨ t = 2989 ∨ t = 2991 →
      denoteGraph pm_goal_229 initPM t
        = denoteGraph {pm_goal_229 with nodes := pm_goal_229.nodes.take 8} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_229 initPM _ _ _
        (List.take_append_drop 8 _).symm (by decide)
  rw [hL, hR 2985 (by tauto), hR 2987 (by tauto), hR 2989 (by tauto), hR 2991 (by tauto)]
  simp only [pm_goal_229, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
