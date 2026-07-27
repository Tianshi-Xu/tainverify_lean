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
theorem hpm1base_145 (initPM : Store) :
    (denoteGraph pm_goal_145 initPM) 1622 = allToAllPrimWithDims 4 1 [(denoteGraph pm_goal_145 initPM) 1650, (denoteGraph pm_goal_145 initPM) 1653, (denoteGraph pm_goal_145 initPM) 1656, (denoteGraph pm_goal_145 initPM) 1659] 2 1 := by
  have hL : denoteGraph pm_goal_145 initPM 1622
          = denoteGraph {pm_goal_145 with nodes := pm_goal_145.nodes.take 10} initPM 1622 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_145 initPM 1622 _ _ (List.take_append_drop 10 _).symm (by decide)
  have hR1650 : denoteGraph pm_goal_145 initPM 1650 = denoteGraph {pm_goal_145 with nodes := pm_goal_145.nodes.take 8} initPM 1650 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_145 initPM 1650 _ _ (List.take_append_drop 8 _).symm (by decide)
  have hR1653 : denoteGraph pm_goal_145 initPM 1653 = denoteGraph {pm_goal_145 with nodes := pm_goal_145.nodes.take 8} initPM 1653 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_145 initPM 1653 _ _ (List.take_append_drop 8 _).symm (by decide)
  have hR1656 : denoteGraph pm_goal_145 initPM 1656 = denoteGraph {pm_goal_145 with nodes := pm_goal_145.nodes.take 8} initPM 1656 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_145 initPM 1656 _ _ (List.take_append_drop 8 _).symm (by decide)
  have hR1659 : denoteGraph pm_goal_145 initPM 1659 = denoteGraph {pm_goal_145 with nodes := pm_goal_145.nodes.take 8} initPM 1659 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_145 initPM 1659 _ _ (List.take_append_drop 8 _).symm (by decide)
  rw [hL, hR1650, hR1653, hR1656, hR1659]
  simp only [pm_goal_145, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
