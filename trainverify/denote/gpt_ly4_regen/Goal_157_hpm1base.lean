import denote.gpt_ly4_regen.Goal_157_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_157.lean and restructured for Lean v4.31.
-- The v4.27 proof reduced this against the full 16-node fold; under v4.31 the
-- `by decide` side goals of `repeat rw [applyNode_eq_of_not_mem_outs]`, and the
-- trailing `rfl`, make the kernel accumulate def-eq state without converging
-- (~3.5 GB/min; 27+ GB RSS measured on Goal_124). Truncating to the prefix that
-- ends at the writing node puts it at the head of the fold, so the same rewrites
-- close it against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem hpm1base_157 (initPM : Store) :
    (denoteGraph pm_goal_157 initPM) 1796 = allToAllPrimWithDims 4 1 [(denoteGraph pm_goal_157 initPM) 1893, (denoteGraph pm_goal_157 initPM) 1896, (denoteGraph pm_goal_157 initPM) 1899, (denoteGraph pm_goal_157 initPM) 1902] 1 2 := by
  have hL : denoteGraph pm_goal_157 initPM 1796
          = denoteGraph {pm_goal_157 with nodes := pm_goal_157.nodes.take 14} initPM 1796 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_157 initPM 1796 _ _
      (List.take_append_drop 14 _).symm (by decide)
  have hR : ∀ t : Tid, t = 1893 ∨ t = 1896 ∨ t = 1899 ∨ t = 1902 →
      denoteGraph pm_goal_157 initPM t
        = denoteGraph {pm_goal_157 with nodes := pm_goal_157.nodes.take 13} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_157 initPM _ _ _
        (List.take_append_drop 13 _).symm (by decide)
  rw [hL, hR 1893 (by tauto), hR 1896 (by tauto), hR 1899 (by tauto), hR 1902 (by tauto)]
  simp only [pm_goal_157, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
