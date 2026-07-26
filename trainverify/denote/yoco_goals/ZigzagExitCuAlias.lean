/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagExitGear

/-!
# cu-seqlens alias between block 11's attention and the zigzag exit

The zigzag exit needs `Zigzag2Rel.to_gather2_unshuffle`, whose hypothesis `h`
and hypothesis `hdecoded` must mention the *same* cu tensor.

Those two arrive carrying different tids:

* the block-11 proof chain carries **5884** — block k's cu is `5345 + 49k`, and
  `FW_attn_zigzag` at SM 890 reads it as `ins[3]`;
* `decodeCuSeqlens_pm_5927` (in `ZigzagExitCuBridge`) speaks about **5927**, the
  separate init tid that only `FW_maybe_unshuffle` at SM 924 consumes.

Both are members of the generated `cu_seqlens_q` input value class (5884 is the
25th of its 26 tids, 5927 the last), so the generated PM input contract already
identifies them. This file records that identification; without it the exit
cannot be closed, and the gap is invisible until the very last step.

The same reasoning as `pm_cuseq_q_5337_eq_5927` in `ZigzagExitGear`, one tid over.
-/

namespace TrainVerify.Denote.YOCInputValueClasses

open TrainVerify.Denote
open Generated

/-- Both tids are members of the generated `cu_seqlens_q` value class. -/
theorem tids_5884_5927_mem_cuseqQClass :
    5884 ∈ cuseqQClass.tids ∧ 5927 ∈ cuseqQClass.tids := by
  decide

/-- The generated PM input contract identifies q tids 5884 and 5927. -/
theorem pm_cuseq_q_5884_eq_5927 (init : Store)
    (h : InputValueClassesHold pmInputValueClasses init) :
    init 5884 = init 5927 := by
  exact h.eq_of_mem cuseqQClass_mem_pm tids_5884_5927_mem_cuseqQClass.1
    tids_5884_5927_mem_cuseqQClass.2

end TrainVerify.Denote.YOCInputValueClasses
