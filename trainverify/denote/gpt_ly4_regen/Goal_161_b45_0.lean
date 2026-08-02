import denote.gpt_ly4_regen.Goal_161_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_161.lean and restructured for Lean v4.31.
-- The v4.27 proof reduced this against the full 16-node fold; under v4.31 the
-- `by decide` side goals of `repeat rw [applyNode_eq_of_not_mem_outs]`, and the
-- trailing `rfl`, make the kernel accumulate def-eq state without converging
-- (~3.5 GB/min; 27+ GB RSS measured on Goal_124). Truncating to the prefix that
-- ends at the writing node puts it at the head of the fold, so the same rewrites
-- close it against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem b45_0_161 (initPM : Store) :
    (denoteGraph pm_goal_161 initPM) 1945 =
      allToAllPrimWithDims 4 0 [(denoteGraph pm_goal_161 initPM) 1929,
        (denoteGraph pm_goal_161 initPM) 1930, (denoteGraph pm_goal_161 initPM) 1931,
        (denoteGraph pm_goal_161 initPM) 1932] 2 3 := by
  have hL : denoteGraph pm_goal_161 initPM 1945
          = denoteGraph {pm_goal_161 with nodes := pm_goal_161.nodes.take 5} initPM 1945 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_161 initPM 1945 _ _
      (List.take_append_drop 5 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_161, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

end TrainVerify.Denote.GeneratedGoals
