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
theorem hAA2_234 (initPM : Store) :
    (denoteGraph pm_goal_234 initPM) 3043 =
      allToAllPrimWithDims 4 2 [initPM 3021, initPM 3022, initPM 3023, initPM 3024] 2 1 := by
  have hL : denoteGraph pm_goal_234 initPM 3043
          = denoteGraph {pm_goal_234 with nodes := pm_goal_234.nodes.take 3} initPM 3043 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_234 initPM 3043 _ _
      (List.take_append_drop 3 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_234, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
