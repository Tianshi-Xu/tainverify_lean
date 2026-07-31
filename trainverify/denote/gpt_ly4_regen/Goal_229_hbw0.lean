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
theorem hbw0_229 (initPM : Store) :
    (denoteGraph pm_goal_229 initPM) 2985 = transposeAxes 2 3 (initPM 2986) := by
  have hL : denoteGraph pm_goal_229 initPM 2985
          = denoteGraph {pm_goal_229 with nodes := pm_goal_229.nodes.take 5} initPM 2985 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_229 initPM 2985 _ _
      (List.take_append_drop 5 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_229, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

end TrainVerify.Denote.GeneratedGoals
