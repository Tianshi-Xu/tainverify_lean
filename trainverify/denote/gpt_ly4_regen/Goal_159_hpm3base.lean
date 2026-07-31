import denote.gpt_ly4_regen.Goal_159_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_159.lean and restructured for Lean v4.31.
-- The v4.27 proof walked in from the end of the full 12-node fold via
-- `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`; under v4.31 those
-- `by decide` side goals run against the whole graph and make the kernel
-- accumulate def-eq state without converging. Truncating to the prefix that ends
-- at the writing node puts it at the head of the fold, so one rewrite closes it
-- and any remaining skips are decided against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxHeartbeats 400000 in
theorem hpm3base_159 (initPM : Store) :
    (denoteGraph pm_goal_159 initPM) 1824 = allToAllPrimWithDims 4 3
      [(denoteGraph pm_goal_159 initPM) 1865, (denoteGraph pm_goal_159 initPM) 1867,
       (denoteGraph pm_goal_159 initPM) 1869, (denoteGraph pm_goal_159 initPM) 1871] 2 1 := by
  have hL : denoteGraph pm_goal_159 initPM 1824
          = denoteGraph {pm_goal_159 with nodes := pm_goal_159.nodes.take 12} initPM 1824 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_159 initPM 1824 _ _
      (List.take_append_drop 12 _).symm (by decide)
  have hR : ∀ t : Tid, t = 1865 ∨ t = 1867 ∨ t = 1869 ∨ t = 1871 →
      denoteGraph pm_goal_159 initPM t
        = denoteGraph {pm_goal_159 with nodes := pm_goal_159.nodes.take 11} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_159 initPM _ _ _
        (List.take_append_drop 11 _).symm (by decide)
  rw [hL, hR 1865 (by tauto), hR 1867 (by tauto), hR 1869 (by tauto), hR 1871 (by tauto)]
  simp only [pm_goal_159, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
