/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagExitGear
import denote.yoco_goals.L12FaithfulRouterProj

/-!
# `cu_seqlens` bridge for the zigzag exit gear

`Zigzag2Rel.to_gather2_unshuffle` (`ZigzagExitGear.lean`) needs the side condition

```
hdecoded : decodeCuSeqlens cu = [0, 2 * lDim]
```

instantiated at the *exit* cu tid `5927`.  This file discharges that obligation from
facts already available on the closure route, and records an explicit non-vacuity
witness so the hypothesis cannot be silently unsatisfiable (AGENTS #29, trap 2).

Route:

* `5927` and `5337` are both members of the generated `cu_seqlens_q` input value class
  (`tids_5337_5927_mem_cuseqQClass`), so `InputValueClassesHold pmInputValueClasses`
  forces `initPM 5337 = initPM 5927`.
* Neither tid is written by any PM node (`cuBridge_cu_tids_not_written`), so the
  init-level identification lifts to the *denote* level
  (`dgdf_5927_eq_5337`).
* `ZigzagCuWF.cu_starts_zero` + `ZigzagCuWF.local_tokens`, together with the `[2]`
  shape of the cu tensor, pin the decoded two-element list down to `[0, 2 * lDim]`
  (`decode_of_cuWF`).  This is exactly the derivation already used inline by
  `recon_zigzagGoal_5359_faithful` for tid `5345`, factored out.

The `[2]` shape is *not* enough on its own — it only fixes the length.  The value
content comes entirely from the `ZigzagCuWF` contract carried by `hCu`.
-/

set_option linter.style.longLine false

open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

open TrainVerify.Denote.YOCInputValueClasses
open TrainVerify.Denote.Generated

/-! ### Generic decoder pinning -/

/-- A `[2]`-shaped cu tensor whose decoding is zigzag-well-formed against two shards
of leading dimension `lDim` decodes exactly to `[0, 2 * lDim]`.

`cu_starts_zero` fixes the head, `local_tokens` fixes the last entry, and the `[2]`
shape fixes the length; `list_eq_pair_of_length_head_last` then closes it. -/
theorem decode_of_cuWF (cu x0 x1 : Tensor) (lDim : Nat)
    (hshape : cu.shape = [2]) (hx0 : x0.shape.getD 0 0 = lDim)
    (hwf : ZigzagCuWF (decodeCuSeqlens cu) [x0, x1] 2) :
    decodeCuSeqlens cu = [0, 2 * lDim] := by
  have hlen : (decodeCuSeqlens cu).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hshape]
    rfl
  apply list_eq_pair_of_length_head_last _ (2 * lDim) hlen hwf.cu_starts_zero
  have ht := hwf.local_tokens
  simp only [List.getD_cons_zero] at ht
  rw [hx0] at ht
  rw [← ht, Nat.mul_comm]

/-! ### Lifting the value-class identification to the denote level -/

/-- Both `cu_seqlens_q` tids used by the exit gear are graph inputs: no PM node
writes them.  This is what allows the *init*-level identification supplied by
`pm_cuseq_q_5337_eq_5927` to be lifted to the *denote* level. -/
theorem cuBridge_cu_tids_not_written :
    (∀ n ∈ pm.nodes, 5927 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5337 ∉ n.outs) := by
  native_decide

/-- The exit cu tid `5927` denotes the same tensor as the layer-12 cu tid `5337`. -/
theorem dgdf_5927_eq_5337 (initPM : Store)
    (hValues : InputValueClassesHold pmInputValueClasses initPM) :
    denoteGraphDistributedFaithful pm initPM 5927 =
      denoteGraphDistributedFaithful pm initPM 5337 := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5927
      layer1_pm_nodes_nonempty cuBridge_cu_tids_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5337
      layer1_pm_nodes_nonempty cuBridge_cu_tids_not_written.2]
  exact (pm_cuseq_q_5337_eq_5927 initPM hValues).symm

/-- The `[2]` shape of the exit cu tensor, read off the generated PM init env. -/
theorem cuBridge_pm_5927_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5927).shape = [2] := by
  have e : denoteGraphDistributedFaithful pm initPM 5927 = initPM 5927 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5927
      layer1_pm_nodes_nonempty cuBridge_cu_tids_not_written.1
  rw [e]
  exact hPM 5927 [2] (by native_decide)

/-! ### The closure-side obligation -/

/-- **Main bridge.**  From the ambient input-value contract, the PM init shape env,
the zigzag metadata well-formedness `hCu` carried along the closure route, and the
shard leading dimension, the `hdecoded` side condition of
`Zigzag2Rel.to_gather2_unshuffle` holds at the exit cu tid `5927`. -/
theorem decodeCuSeqlens_pm_5927 (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hValues : InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2)
    (hx0 : (denoteGraphDistributedFaithful pm initPM 13257).shape.getD 0 0 = 2048) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5927) = [0, 2 * 2048] := by
  rw [dgdf_5927_eq_5337 initPM hValues]
  refine decode_of_cuWF _ _ _ 2048 ?_ hx0 hCu
  rw [← dgdf_5927_eq_5337 initPM hValues]
  exact cuBridge_pm_5927_shape initPM hPM

/-! ### Non-vacuity witness (AGENTS #29)

A concrete store simultaneously satisfying `InputValueClassesHold pmInputValueClasses`,
the `[2]` shape of the cu tensor, the `ZigzagCuWF` contract, and yielding the target
decoding `[0, 4096]`.  This rules out the "hypothesis never holds ⇒ theorem vacuous"
trap for `decodeCuSeqlens_pm_5927` and hence for `to_gather2_unshuffle` at tid 5927. -/

/-- Concrete `[2]`-shaped cu tensor holding the packed boundaries `[0, 4096]`. -/
def cuWitnessTensor : Tensor :=
  { shape := [2], val := fun i => if i.val = 0 then (0 : Scalar) else (4096 : Scalar) }

theorem cuWitnessTensor_shape : cuWitnessTensor.shape = [2] := rfl

/-- The witness tensor really decodes to `[0, 4096]`. -/
theorem decode_cuWitnessTensor : decodeCuSeqlens cuWitnessTensor = [0, 4096] := by
  have hp : prodShape cuWitnessTensor.shape = 2 := by
    norm_num [cuWitnessTensor, prodShape]
  unfold decodeCuSeqlens
  rw [hp]
  have h0 : valAt cuWitnessTensor 0 = (0 : Scalar) := by
    rw [valAt_of_lt cuWitnessTensor 0 (by rw [hp]; norm_num)]
    show (if (0 : Nat) = 0 then (0 : Scalar) else (4096 : Scalar)) = 0
    norm_num
  have h1 : valAt cuWitnessTensor 1 = (4096 : Scalar) := by
    rw [valAt_of_lt cuWitnessTensor 1 (by rw [hp]; norm_num)]
    show (if (1 : Nat) = 0 then (0 : Scalar) else (4096 : Scalar)) = 4096
    norm_num
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, h0, h1]
  norm_num [scalarToNat]

/-- The `ZigzagCuWF` contract is satisfiable at exactly the decoded list `[0, 4096]`
with two `[2048, 1024]` shards — the shapes the closure route actually uses. -/
theorem cuWitness_wf :
    ZigzagCuWF (decodeCuSeqlens cuWitnessTensor)
      [zeroTensor [2048, 1024], zeroTensor [2048, 1024]] 2 := by
  rw [decode_cuWitnessTensor]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have : s = 0 := Nat.lt_one_iff.mp (by simpa using hs)
    subst this; norm_num
  · intro s hs
    have : s = 0 := Nat.lt_one_iff.mp (by simpa using hs)
    subst this; norm_num
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [zeroTensor, Tensor.mkShape]
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [zeroTensor, Tensor.mkShape]
  · norm_num [zeroTensor, Tensor.mkShape, listLast!]

/-- The constant store at the witness cu tensor. -/
def cuWitnessStore : Store := fun _ => cuWitnessTensor

/-- The witness store satisfies the whole generated PM input value contract. -/
theorem cuWitnessStore_classes :
    InputValueClassesHold pmInputValueClasses cuWitnessStore :=
  inputValueClassesHold_const _ _

/-- **Existence witness.**  There is a store satisfying the input value contract on
which the exit cu tid decodes to `[0, 2 * 2048] = [0, 4096]`, together with a
satisfying instance of the `ZigzagCuWF` contract.  So the `hdecoded` premise of the
exit gear is genuinely satisfiable, not vacuous. -/
theorem cuBridge_nonvacuous :
    ∃ init : Store,
      InputValueClassesHold pmInputValueClasses init ∧
      (init 5927).shape = [2] ∧
      init 5337 = init 5927 ∧
      decodeCuSeqlens (init 5927) = [0, 2 * 2048] ∧
      ZigzagCuWF (decodeCuSeqlens (init 5337))
        [zeroTensor [2048, 1024], zeroTensor [2048, 1024]] 2 := by
  refine ⟨cuWitnessStore, cuWitnessStore_classes, rfl, rfl, ?_, ?_⟩
  · show decodeCuSeqlens cuWitnessTensor = [0, 2 * 2048]
    rw [decode_cuWitnessTensor]
  · show ZigzagCuWF (decodeCuSeqlens cuWitnessTensor) _ 2
    exact cuWitness_wf

end
end TrainVerify.Denote.GeneratedPatterns
