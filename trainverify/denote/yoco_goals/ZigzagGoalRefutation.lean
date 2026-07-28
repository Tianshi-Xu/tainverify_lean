/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLineageGoal
import denote.StackGatherDim1

/-!
# Why `goal_3` / `goal_4` cannot be stated as ordinary gathers

`goal_3` (tid `4675`) and `goal_4` (tid `4676`) stack the 24 per-layer routing
tensors. The generated form asserts

```
SM 4675 = reconstructWithDim 1 2 0 [PM 11729, PM 11730]
```

i.e. an ordinary dim-1 gather of the two per-rank stacks. Twelve of the 24
stacked members (layers 12–23) are produced *after* the CP2 `FW_maybe_shuffle`
and are therefore zigzag-owned, so that equation is false.

Until now that claim rested on a dataflow argument. This module turns it into a
theorem: on a concrete cp=2 fixture, the zigzag shards of a tensor do **not**
ordinary-gather to the full tensor, while their unshuffled counterparts do.

The point is not that some abstract relation fails — it is that the two sides
disagree at a specific index on specific numbers.
-/

set_option linter.style.longLine false

namespace TrainVerify.Denote.ZigzagGoalRefutation

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.ZigzagLayoutRelRegression

noncomputable section

/-! ### The fixture, restated

`ZigzagLayoutRelRegression` gives a genuine cp=2 pair: sources `x0 = [0,1,2,3]`
and `x1 = [4,5,6,7]` (as `[4, 1]` tensors), `full = [0..7]`, and the two zigzag
shards `z0`/`z1`. Under cp=2 zigzag, rank 0 owns global positions `[0, 1, 6, 7]`
and rank 1 owns `[2, 3, 4, 5]` — the ordinary contiguous split would give rank 0
`[0, 1, 2, 3]`.
-/

/-- The ordinary dim-0 gather of the two **zigzag** shards. This is the tensor
the generated goal claims equals `full`. -/
def gatheredZigzag : Tensor := allGatherPrimDimN 0 2 0 [z0, z1]

@[simp] theorem z0_shape : z0.shape = [4, 1] := by
  unfold z0
  rw [fw_maybe_shuffle_collective_shape]
  simp

@[simp] theorem z1_shape : z1.shape = [4, 1] := by
  unfold z1
  rw [fw_maybe_shuffle_collective_shape]
  simp

theorem gatheredZigzag_shape : gatheredZigzag.shape = [8, 1] := by
  unfold gatheredZigzag
  rw [allGatherPrimDimN_shape 0 2 _ [4, 1] (by simp)]
  norm_num [List.set, List.getD]

/-! ### The refutation

Shapes agree — that is exactly why the shape-based emitter could not see the
problem — but the values do not.

The fixture's numbers make the disagreement concrete. `full` is the contiguous
`[0,1,2,3,4,5,6,7]`. The zigzag shards are `z0 = [0,1,6,7]` and `z1 = [2,3,4,5]`
(both already proven in `ZigzagLayoutRelRegression`). An ordinary dim-0 gather
concatenates them into `[0,1,6,7,2,3,4,5]`, so index 2 carries **6** where the
contiguous layout carries **2**. -/

/-- Shapes match, so shape checking cannot detect the error. -/
theorem shapes_agree : gatheredZigzag.shape = full.shape := by
  rw [gatheredZigzag_shape, full_shape]

/-- The zigzag gather reads rank 0's third slot at flat index 2. -/
theorem gatheredZigzag_valAt_2 : valAt gatheredZigzag 2 = 6 := by
  have h := allGatherPrimDimN0_valAt 2 4 1 [z0, z1] (by decide) (by decide) (by decide)
    (by simp) (by
      intro r hr
      match r, hr with
      | 0, _ => rw [List.getD_cons_zero]; exact z0_shape
      | 1, _ => rw [List.getD_cons_succ, List.getD_cons_zero]; exact z1_shape)
    0 (by decide) 2 (by decide) 0 (by decide)
  -- `(0 * 4 + 2) * 1 + 0 = 2`
  norm_num at h
  rw [show (2 : Nat) = (0 * 4 + 2) * 1 + 0 from by norm_num]
  unfold gatheredZigzag
  rw [h]
  have hz := observed_z0
  unfold observe4 at hz
  norm_num [List.range_succ] at hz
  exact hz.2.2.1

/-- The contiguous full tensor carries 2 at flat index 2. -/
theorem full_valAt_2 : valAt full 2 = 2 := by
  have h := allGatherPrimDimN0_valAt 2 4 1 [x0, x1] (by decide) (by decide) (by decide)
    (by simp) (by
      intro r hr
      match r, hr with
      | 0, _ => rw [List.getD_cons_zero]; exact x0_shape
      | 1, _ => rw [List.getD_cons_succ, List.getD_cons_zero]; exact x1_shape)
    0 (by decide) 2 (by decide) 0 (by decide)
  norm_num at h
  rw [show (2 : Nat) = (0 * 4 + 2) * 1 + 0 from by norm_num]
  unfold full
  rw [h]
  rw [valAt_of_lt _ _ (by norm_num [x0, Tensor.mkShape, prodShape])]
  show ((2 : Nat) : Scalar) = 2
  norm_num

/-- **The generated goal's equation is false on a concrete cp=2 input.**

Same shape, different values: the ordinary dim-0 gather of the zigzag shards
disagrees with the contiguous tensor at flat index 2 (6 versus 2). -/
theorem gatheredZigzag_ne_full : gatheredZigzag ≠ full := by
  intro hcontra
  have hv : valAt gatheredZigzag 2 = valAt full 2 := by rw [hcontra]
  rw [gatheredZigzag_valAt_2, full_valAt_2] at hv
  norm_num at hv

/-- Consequently, no `LineageGoal`-style ordinary dim-0 reconstruction over the
zigzag shards can hold for this tensor. -/
theorem no_ordinary_reconstruction :
    reconstructWithDim 0 2 0 [z0, z1] ≠ full := by
  have hne : (z0.shape ≠ [1]) := by simp
  unfold reconstructWithDim
  simp only [List.head?_cons, Option.map_some, Option.getD_some, if_neg hne]
  exact gatheredZigzag_ne_full

/-! ### The positive half: unshuffling repairs it

The same fixture shows the fix is real rather than a dodge. `Zigzag2Rel` already
holds for the fixture (`concrete_zigzag2Rel`), so the general bridge applies and
the unshuffled shards *do* ordinary-gather back to `full`. -/

theorem unshuffled_gather_recovers_full :
    Gather2Rel full
      (fw_maybe_unshuffle_collective [z0, z1] (decodeCuSeqlens cu) 2 0)
      (fw_maybe_unshuffle_collective [z0, z1] (decodeCuSeqlens cu) 2 1)
      [4 * 2, 1] [4, 1] :=
  Zigzag2Rel.to_gather2_unshuffle 4 1
    (by simpa using concrete_zigzag2Rel)
    (by norm_num) (by norm_num) (by decide)
    (by simpa using decode_cu)

/-- Spelled out as the value equation, for direct comparison with
`gatheredZigzag_ne_full`: the unshuffled gather **does** equal `full`, whereas
the raw zigzag gather does not. -/
theorem unshuffled_gather_eq_full :
    allGatherPrimDimN 0 2 0
      [fw_maybe_unshuffle_collective [z0, z1] (decodeCuSeqlens cu) 2 0,
       fw_maybe_unshuffle_collective [z0, z1] (decodeCuSeqlens cu) 2 1]
      = full :=
  unshuffled_gather_recovers_full.value.symm

/-! ### What this means for `goal_3` / `goal_4`

`goal_3` stacks 24 members, of which 12 are in the layout refuted above. The
stack is a single tensor, so the goal must state one uniform reconstruction for
all 24 — and no such statement is true. The goal is therefore not provable *as
generated*, which is why `Verdict/graph_to_lean.py` now suppresses it rather
than emitting it.

The stack/gather commute lemma needed for the honest version is already proven
(`fw_stack_allGather0_eq_allGather1_stack`): it turns a stack of dim-0 gathers
into a dim-1 gather of stacks. Applied to *unshuffled* members it discharges the
real obligation; applied to the zigzag members directly its hypothesis
`fulls[k] = allGatherPrimDimN 0 2 0 [as[k], bs[k]]` is exactly what
`no_ordinary_reconstruction` refutes. -/

theorem goal_3_shaped_obligation_needs_unshuffle
    (as bs fulls : List Tensor) (n rows cols : Nat)
    (hrows : 0 < rows) (hcols : 0 < cols) (hn : 0 < n)
    (hlenA : as.length = n) (hlenB : bs.length = n) (hlenF : fulls.length = n)
    (hA : ∀ k (_ : k < n), (as.getD k (zeroTensor [rows, cols])).shape = [rows, cols])
    (hB : ∀ k (_ : k < n), (bs.getD k (zeroTensor [rows, cols])).shape = [rows, cols])
    (hF : ∀ k (_ : k < n), fulls.getD k (zeroTensor [rows * 2, cols]) =
      allGatherPrimDimN 0 2 0
        [as.getD k (zeroTensor [rows, cols]), bs.getD k (zeroTensor [rows, cols])]) :
    fw_stack fulls = allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs] :=
  fw_stack_allGather0_eq_allGather1_stack as bs fulls n rows cols
    hrows hcols hn hlenA hlenB hlenF hA hB hF

end

end TrainVerify.Denote.ZigzagGoalRefutation
