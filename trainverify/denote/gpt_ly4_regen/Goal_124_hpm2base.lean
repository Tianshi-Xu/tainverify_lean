import denote.gpt_ly4_regen.Goal_124_Data

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

-- Split out of Goal_124.lean and restructured for Lean v4.31.
-- The v4.27 proof closed this with `repeat rw [applyNode_eq_of_not_mem_outs
-- (h := by decide)]` followed by a trailing `rfl`. Under v4.31 those `by decide`
-- side goals make the kernel accumulate def-eq state without converging
-- (measured 27 GB RSS and still climbing after 9 min).
-- Truncating both sides to their relevant prefixes FIRST puts the target node at
-- the head of the fold, so one `applyNode_allToAllPrimWithDims_out` rewrite
-- closes it and the only `rfl` left is the numRanks literal. ~4 s.
set_option maxHeartbeats 400000 in
theorem hpm2base_124 (initPM : Store) :
    (denoteGraph pm_goal_124 initPM) 1302 = allToAllPrimWithDims 4 2
      [(denoteGraph pm_goal_124 initPM) 1345, (denoteGraph pm_goal_124 initPM) 1347,
       (denoteGraph pm_goal_124 initPM) 1349, (denoteGraph pm_goal_124 initPM) 1351] 3 1 := by
  have hL : denoteGraph pm_goal_124 initPM 1302
          = denoteGraph {pm_goal_124 with nodes := pm_goal_124.nodes.take 11} initPM 1302 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm_goal_124 initPM 1302 _ _
      (List.take_append_drop 11 _).symm (by decide)
  have hR : ∀ t : Tid, t = 1345 ∨ t = 1347 ∨ t = 1349 ∨ t = 1351 →
      denoteGraph pm_goal_124 initPM t
        = denoteGraph {pm_goal_124 with nodes := pm_goal_124.nodes.take 10} initPM t := by
    rintro t (rfl | rfl | rfl | rfl) <;>
      exact denoteGraph_tid_eq_of_suffix_no_writes pm_goal_124 initPM _ _ _
        (List.take_append_drop 10 _).symm (by decide)
  rw [hL, hR 1345 (by tauto), hR 1347 (by tauto), hR 1349 (by tauto), hR 1351 (by tauto)]
  simp only [pm_goal_124, denoteGraph, GraphDecl.nodes, List.take, List.foldl, List.map]
  rw [applyNode_allToAllPrimWithDims_out]
  rfl

end TrainVerify.Denote.GeneratedGoals
