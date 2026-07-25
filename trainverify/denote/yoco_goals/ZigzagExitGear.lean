/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel
import denote.yoco_goals.DistributedMigrationGears
import denote.yoco_goals.YOCInputValueClasses

/-!
# Exit gears for the zigzag context-parallel closure

Two glue lemmas needed by the final zigzag closure:

* `Zigzag2Rel.to_gather2_unshuffle` turns a zigzag layout relation into an
  ordinary `Gather2Rel` over the *unshuffled* shards.
* `pm_cuseq_q_5337_eq_5927` bridges two `cu_seqlens_q` tids of the same
  generated input value class.
-/

set_option linter.style.longLine false

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-- Unshuffling the two public zigzag shards yields an ordinary dim-0 gather
relation against the same full tensor. -/
theorem Zigzag2Rel.to_gather2_unshuffle
    {full z0 z1 cu : Tensor} (lDim hM : Nat)
    (h : Zigzag2Rel full z0 z1 cu [lDim * 2, hM] [lDim, hM])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (hns : [lDim, hM] ≠ [1])
    (hdecoded : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Gather2Rel full
      (fw_maybe_unshuffle_collective [z0, z1] (decodeCuSeqlens cu) 2 0)
      (fw_maybe_unshuffle_collective [z0, z1] (decodeCuSeqlens cu) 2 1)
      [lDim * 2, hM] [lDim, hM] := by
  obtain ⟨s0, s1, hfull, hu0, hu1⟩ :=
    h.unshuffle_sources_single lDim [hM] hl heven rfl hdecoded
  refine ⟨?_, h.full_shape, ?_, ?_, hns⟩
  · rw [hu0, hu1]
    exact hfull
  · rw [fw_maybe_unshuffle_collective_shape]
    rw [List.getD_cons_zero]
    exact h.rank0_shape
  · rw [fw_maybe_unshuffle_collective_shape]
    rw [List.getD_cons_succ, List.getD_cons_zero]
    exact h.rank1_shape

end
end TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.YOCInputValueClasses

open Generated

/-- Both tids are members of the generated `cu_seqlens_q` value class. -/
theorem tids_5337_5927_mem_cuseqQClass :
    5337 ∈ cuseqQClass.tids ∧ 5927 ∈ cuseqQClass.tids := by
  decide

/-- The generated PM input contract identifies q tids 5337 and 5927. -/
theorem pm_cuseq_q_5337_eq_5927 (init : Store)
    (h : InputValueClassesHold pmInputValueClasses init) :
    init 5337 = init 5927 := by
  exact h.eq_of_mem cuseqQClass_mem_pm tids_5337_5927_mem_cuseqQClass.1
    tids_5337_5927_mem_cuseqQClass.2

end TrainVerify.Denote.YOCInputValueClasses
