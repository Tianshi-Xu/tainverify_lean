/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagGoalStatement
import denote.yoco_goals.ZigzagExitGear
import denote.yoco_goals.ZigzagLayoutRelRegression

/-!
# Zigzag-aware lineage goals: bridges and non-vacuity

The goal structure and its `Prop` live in `ZigzagGoalStatement`, which is kept
free of generated-graph dependencies so `denote/GeneratedYOCOMoE.lean` can import
it and emit `ZigzagLineageGoal` definitions.

This module adds the parts that need the heavier machinery:

* `ZigzagGoalHolds.to_gather_after_unshuffle` — once the graph's
  `FW_maybe_unshuffle` has run, a zigzag goal becomes an ordinary `Gather2Rel`,
  which is exactly what the existing downstream machinery consumes. This is what
  makes the new form *useful* rather than merely honest.
* `ZigzagGoalHolds.satisfiable` — non-vacuity. A goal form that nothing can
  satisfy would make every downstream theorem vacuous (AGENTS #29, vacuity trap
  2), so this exhibits a concrete satisfying pair of stores.
-/

set_option linter.style.longLine false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-! ### The bridge back to ordinary reconstruction -/

/-- After unshuffling, a zigzag goal is an ordinary two-rank dim-0 gather. -/
theorem ZigzagGoalHolds.to_gather_after_unshuffle
    {g : ZigzagLineageGoal} {smStore pmStore : Store}
    (lDim hM : Nat)
    (h : ZigzagGoalHolds g smStore pmStore)
    (hts : g.tsShape = lDim * 2 :: [hM])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (hns : [lDim, hM] ≠ [1])
    (hdecoded : decodeCuSeqlens (pmStore g.cuTid) = [0, 2 * lDim]) :
    ∃ (t0 t1 : Tid),
      g.tps = [{ rank := 0, tid := t0 }, { rank := 1, tid := t1 }] ∧
      Gather2Rel (smStore g.ts)
        (fw_maybe_unshuffle_collective [pmStore t0, pmStore t1]
          (decodeCuSeqlens (pmStore g.cuTid)) 2 0)
        (fw_maybe_unshuffle_collective [pmStore t0, pmStore t1]
          (decodeCuSeqlens (pmStore g.cuTid)) 2 1)
        [lDim * 2, hM] [lDim, hM] := by
  obtain ⟨t0, t1, htps, hrel⟩ := h.zigzag2Rel
  refine ⟨t0, t1, htps, ?_⟩
  have hshape : (smStore g.ts).shape = lDim * 2 :: [hM] := by
    obtain ⟨_, _, _, _, _, hfs, _⟩ := h
    rw [hfs, hts]
  have hhead : (smStore g.ts).shape.headD 0 / 2 = lDim := by
    rw [hshape]
    simp only [List.headD_cons]
    omega
  rw [hts, hhead] at hrel
  exact Zigzag2Rel.to_gather2_unshuffle lDim hM (by simpa using hrel)
    hl heven hns hdecoded

/-! ### Non-vacuity -/

theorem ZigzagGoalHolds.satisfiable :
    ∃ (g : ZigzagLineageGoal) (smStore pmStore : Store),
      ZigzagGoalHolds g smStore pmStore := by
  classical
  -- Reuse the concrete cp=2 fixture from `ZigzagLayoutRelRegression`: a genuine
  -- `[8, 1]` tensor whose two `[4, 1]` shards are in real zigzag layout (rank 0
  -- owning global positions [0, 1, 6, 7], not [0, 1, 2, 3]). Using a real
  -- fixture rather than a zero tensor matters: a degenerate witness could
  -- satisfy the relation for the wrong reason and would not rule out vacuity.
  refine ⟨{ ts := 10, tsShape := [8, 1],
            tps := [{ rank := 0, tid := 11 }, { rank := 1, tid := 12 }],
            tpShapes := [[4, 1], [4, 1]], cuTid := 13, cpSize := 2 },
          fun _ => ZigzagLayoutRelRegression.full,
          fun t =>
            if t = 11 then ZigzagLayoutRelRegression.z0
            else if t = 12 then ZigzagLayoutRelRegression.z1
            else ZigzagLayoutRelRegression.cu,
          ?_⟩
  refine ZigzagGoalHolds.of_zigzag2Rel _ _ _ 11 12 4 [1] rfl rfl rfl rfl
    ZigzagLayoutRelRegression.full_shape ?_
  simpa using ZigzagLayoutRelRegression.concrete_zigzag2Rel

end

end TrainVerify.Denote.GeneratedPatterns
