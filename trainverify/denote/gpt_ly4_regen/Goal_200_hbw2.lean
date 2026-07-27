import denote.gpt_ly4_regen.Goal_200_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_200.lean and restructured for Lean v4.31.
-- The v4.27 proof reduced this against the full 16-node fold; under v4.31 the
-- `by decide` side goals of `repeat rw [applyNode_eq_of_not_mem_outs]`, and the
-- trailing `rfl`, make the kernel accumulate def-eq state without converging
-- (~3.5 GB/min; 27+ GB RSS measured on Goal_124). Truncating to the prefix that
-- ends at the writing node puts it at the head of the fold, so the same rewrites
-- close it against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem hbw2_200 (initPM : Store) :
    (denoteGraph pm_goal_200 initPM) 2523 =
      batchedMatmul (initPM 2525)
        (transpose2d (allToAllPrimWithDims 4 2
          [initPM 2393, initPM 2394, initPM 2395, initPM 2396] 2 1)) := by
  have hL : denoteGraph pm_goal_200 initPM 2523
          = denoteGraph {pm_goal_200 with nodes := pm_goal_200.nodes.take 11} initPM 2523 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_200 initPM 2523 _ _
      (List.take_append_drop 11 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_200, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_matmul_fst_out _ _ 2 2525 2499 2503 2523 2524 (by decide), bw_matmul_fst_eq]
  congr 2

end TrainVerify.Denote.GeneratedGoals
