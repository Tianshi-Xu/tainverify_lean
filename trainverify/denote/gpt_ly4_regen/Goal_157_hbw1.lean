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
theorem hbw1_157 (initPM : Store) :
    (denoteGraph pm_goal_157 initPM) 1896 =
      batchedMatmul (initPM 1898)
        (transpose2d (allToAllPrimWithDims 4 1
          [initPM 1853, initPM 1854, initPM 1855, initPM 1856] 3 1)) := by
  have hL : denoteGraph pm_goal_157 initPM 1896
          = denoteGraph {pm_goal_157 with nodes := pm_goal_157.nodes.take 10} initPM 1896 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_157 initPM 1896 _ _
      (List.take_append_drop 10 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_157, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_matmul_fst_out _ _ 1 1898 1874 1878 1896 1897 (by decide), bw_matmul_fst_eq]
  congr 2

end TrainVerify.Denote.GeneratedGoals
