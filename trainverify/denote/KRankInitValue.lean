import denote.Denote

namespace TrainVerify.Denote

/-- A non-replicated multi-piece InitGoal exposes its ordered PM pieces through
`allGatherPrimDimN`.  The rank count is the authority list length. -/
theorem InitGoalHolds.sharded_value
    (numRanks : Nat) (g : LineageGoal) (sm pm : Store) (dim : Nat)
    (h : InitGoalHolds numRanks g sm pm)
    (hrep : g.replicated = false)
    (hdim : g.gatherDim = dim)
    (hlen : numRanks = g.tps.length)
    (hmulti : 2 ≤ g.tps.length)
    (hnonscalar :
      ((g.tps.map fun tp => pm tp.tid).head?.map fun t => t.shape).getD [] ≠ [1]) :
    sm g.ts = allGatherPrimDimN dim g.tps.length 0
      (g.tps.map fun tp => pm tp.tid) := by
  unfold InitGoalHolds reconstructForGoal at h
  rw [hrep, hdim] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases htps : g.tps with
  | nil => simp [htps] at hmulti
  | cons first rest =>
      cases hrest : rest with
      | nil => simp [htps, hrest] at hmulti
      | cons second tail =>
          have hvalue := h.2.2
          simp only [htps, hrest, List.map_cons, List.head?_cons, Option.map_some,
            Option.getD_some] at hnonscalar
          simp only [htps, hrest, List.map_cons, reconstructWithDim,
            List.head?_cons, Option.map_some, Option.getD_some] at hvalue
          rw [if_neg hnonscalar] at hvalue
          rw [hlen] at hvalue
          simpa [htps, hrest] using hvalue

end TrainVerify.Denote
