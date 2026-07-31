import denote.gpt_ly4_regen.Goal_124_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_124.lean and restructured for Lean v4.31.
-- The v4.27 proof used `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`
-- to walk in from the end of the full 12-node fold. Under v4.31 those `by decide`
-- side goals run against the whole graph and make the kernel accumulate def-eq
-- state without converging. Truncating to the prefix ending at the writing node
-- puts it at the head of the fold, and the remaining skips are decided against a
-- 5-node graph instead of a 12-node one.
set_option maxHeartbeats 400000 in
theorem hbw0_124 (initPM : Store) :
    (denoteGraph pm_goal_124 initPM) 1345 = transposeAxes 2 3 (initPM 1346) := by
  have hL : denoteGraph pm_goal_124 initPM 1345
          = denoteGraph {pm_goal_124 with nodes := pm_goal_124.nodes.take 5} initPM 1345 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_124 initPM 1345 _ _
      (List.take_append_drop 5 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_124, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

end TrainVerify.Denote.GeneratedGoals
