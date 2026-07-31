import denote.gpt_ly4_regen.Goal_145_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_145.lean and restructured for Lean v4.31.
-- The v4.27 proof reduced this against the full 12-node fold; under v4.31 the
-- `by decide` side goals of `repeat rw [applyNode_eq_of_not_mem_outs]`, and the
-- trailing `rfl`, make the kernel accumulate def-eq state without converging
-- (~3.5 GB/min; 27+ GB RSS measured on Goal_124). Truncating to the prefix that
-- ends at the writing node puts it at the head of the fold, so the same rewrites
-- close it against a much smaller graph.
-- Proof content is otherwise the v4.27 proof from commit c4f01699.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem hbw1_145 (initPM : Store) :
    (denoteGraph pm_goal_145 initPM) 1653 =
      (bw_add2 (initPM 1654) (initPM 1630)
        (allToAllPrimWithDims 4 1 [initPM 1605, initPM 1606, initPM 1607, initPM 1608] 1 2)).2 := by
  have hL : denoteGraph pm_goal_145 initPM 1653
          = denoteGraph {pm_goal_145 with nodes := pm_goal_145.nodes.take 6} initPM 1653 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_145 initPM 1653 _ _
      (List.take_append_drop 6 _).symm (by decide)
  rw [hL]
  simp only [pm_goal_145, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_bw_add2_snd_out_g145 _ _ 1 1654 1630 1634 1652 1653 (by decide)]
  congr 2 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

end TrainVerify.Denote.GeneratedGoals
