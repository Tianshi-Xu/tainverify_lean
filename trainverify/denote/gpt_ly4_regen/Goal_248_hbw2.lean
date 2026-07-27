import denote.gpt_ly4_regen.Goal_248_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_248.lean and restructured for Lean v4.31.
-- The v4.27 proof reduced this against the full 12-node fold; under v4.31 the
-- `by decide` side goals of `repeat rw [applyNode_eq_of_not_mem_outs]`, and the
-- trailing `rfl`, make the kernel accumulate def-eq state without converging
-- (~3.5 GB/min; 27+ GB RSS measured on Goal_124). Truncating to the prefix that
-- ends at the writing node puts it at the head of the fold, so the same rewrites
-- close it against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem hbw2_248 (initPM : Store) :
    (denoteGraph pm_goal_248 initPM) 3309 =
      (bw_linear (initPM 889) (allToAllPrimWithDims 4 2 [initPM 3265, initPM 3266, initPM 3267, initPM 3268] 1 2) (initPM 3291)).1 := by
  have hL : denoteGraph pm_goal_248 initPM 3309
          = denoteGraph {pm_goal_248 with nodes := pm_goal_248.nodes.take 7} initPM 3309 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_248 initPM 3309 _ _
      (List.take_append_drop 7 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_248, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_linear_fst_out _ _ 2 889 3287 3291 3309 3310 (by decide)]
  congr 2

end TrainVerify.Denote.GeneratedGoals
