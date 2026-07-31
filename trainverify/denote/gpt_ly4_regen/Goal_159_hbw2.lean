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
theorem hbw2_159 (initPM : Store) :
    (denoteGraph pm_goal_159 initPM) 1869 = transposeAxes 2 3 (initPM 1870) := by
  have hL : denoteGraph pm_goal_159 initPM 1869
          = denoteGraph {pm_goal_159 with nodes := pm_goal_159.nodes.take 7} initPM 1869 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_159 initPM 1869 _ _
      (List.take_append_drop 7 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_159, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

end TrainVerify.Denote.GeneratedGoals
