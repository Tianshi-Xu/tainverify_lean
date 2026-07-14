/- JointWitnessCore.lean

Core machinery for pattern joint-hypothesis witnesses:
  ∃ (initSM initPM : Store),
    StoreShapesHold initSM smEnv ∧
    StoreShapesHold initPM pmEnv ∧
    InitGoalsHold numRanks goals initSM initPM ∧
    <pattern-specific hypothesis>

Strategy: canonical zero-Tensor stores keyed by shape lookups derived from the
goal list. All pieces reconstruct into zero tensors, so `InitGoalHolds` reduces
to a shape check dischargeable by `native_decide`.
-/
import denote.Denote
import denote.GeneratedYOCOMoE
import Mathlib.Data.List.GetD

set_option maxHeartbeats 800000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.JointWitness

/-! ## Canonical zero store -/

/-- Canonical zero store keyed by a `Tid → Shape` map. -/
def zeroStore (shapeOf : Tid → Shape) : Store :=
  fun tid => zeroTensor (shapeOf tid)

theorem zeroStore_shape (shapeOf : Tid → Shape) (tid : Tid) :
    (zeroStore shapeOf tid).shape = shapeOf tid := by
  unfold zeroStore zeroTensor Tensor.mkShape; rfl

theorem zeroStore_shapes_hold (shapeOf : Tid → Shape) (env : ShapeEnv)
    (hconsistent : ∀ tid sh, env tid = some sh → shapeOf tid = sh) :
    StoreShapesHold (zeroStore shapeOf) env := by
  intro tid sh hsh
  rw [zeroStore_shape]; exact hconsistent tid sh hsh

/-! ## Zero-tensor arithmetic -/

@[simp] theorem valAt_zeroTensor (sh : Shape) (i : Nat) :
    valAt (zeroTensor sh) i = 0 := by
  unfold valAt zeroTensor Tensor.mkShape
  by_cases h : i < prodShape sh <;> simp [h]

/-- getD past the end returns the default. -/
theorem List_getD_of_length_le {α : Type*} (xs : List α) (r : Nat) (d : α)
    (h : xs.length ≤ r) : xs.getD r d = d := by
  induction xs generalizing r with
  | nil => rfl
  | cons _ t ih =>
    cases r with
    | zero => exact absurd h (by simp)
    | succ r' =>
      simp only [List.getD_cons_succ]
      exact ih r' (by simpa [Nat.succ_le_succ_iff] using h)

/-- Gathering zero tensors gives a zero tensor of the gathered shape. -/
theorem allGatherPrimDimN_of_zeroTensors (gatherDim numParts : Nat)
    (xs : List Tensor) (sh : Shape)
    (hall : ∀ t ∈ xs, t = zeroTensor sh)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = sh) :
    allGatherPrimDimN gatherDim numParts 0 xs =
      zeroTensor (sh.set gatherDim (sh.getD gatherDim 0 * numParts)) := by
  apply Tensor.ext
  · exact allGatherPrimDimN_shape gatherDim numParts xs sh hhead
  · intro idx hidx
    rw [valAt_zeroTensor]
    have hLHSshape : (allGatherPrimDimN gatherDim numParts 0 xs).shape =
        sh.set gatherDim (sh.getD gatherDim 0 * numParts) :=
      allGatherPrimDimN_shape gatherDim numParts xs sh hhead
    have hidx' : idx < prodShape (allGatherPrimDimN gatherDim numParts 0 xs).shape := hidx
    rw [valAt_of_lt _ _ hidx']
    show (allGatherPrimDimN gatherDim numParts 0 xs).val ⟨idx, hidx'⟩ = 0
    unfold allGatherPrimDimN
    simp only [Tensor.mkShape]
    generalize hshard : (Option.map (fun t : Tensor => t.shape) xs.head?).getD [] = shard
    have hshard_eq_sh : shard = sh := by rw [← hshard]; exact hhead
    set r := if _h : shard.getD gatherDim 0 = 0 then 0
             else _ / shard.getD gatherDim 0 with hr_def
    set piece := xs.getD r (zeroTensor shard) with hpiece_def
    have hpiece_zero : piece = zeroTensor sh := by
      by_cases hr : r < xs.length
      · rw [hpiece_def, List.getD_eq_getElem xs (zeroTensor shard) hr]
        exact hall _ (List.getElem_mem _)
      · rw [hpiece_def, List_getD_of_length_le _ _ _ (Nat.le_of_not_lt hr), hshard_eq_sh]
    show valAt piece _ = 0
    rw [hpiece_zero, valAt_zeroTensor]

/-- Foldl summing values that are all zero equals initial. -/
theorem foldl_add_zero_valAt (idx : Nat) (init : Scalar) (xs : List Tensor)
    (hall : ∀ t ∈ xs, valAt t idx = 0) :
    xs.foldl (fun acc t => acc + valAt t idx) init = init := by
  induction xs generalizing init with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    rw [hall a (by simp), add_zero]
    exact ih init (fun t ht => hall t (by simp [ht]))

/-- allReduce of zero tensors is a zero tensor. -/
theorem allReducePrim_of_zeroTensors (numParts : Nat) (xs : List Tensor) (sh : Shape)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = sh)
    (hall : ∀ t ∈ xs, t = zeroTensor sh) :
    allReducePrim numParts 0 xs = zeroTensor sh := by
  have hallval : ∀ t ∈ xs, ∀ i, valAt t i = 0 := by
    intro t ht i; rw [hall t ht, valAt_zeroTensor]
  apply Tensor.ext
  · unfold allReducePrim
    dsimp only
    rw [hhead]
    unfold zeroTensor Tensor.mkShape; rfl
  · intro idx hidx
    rw [valAt_zeroTensor]
    have hshapeeq : (allReducePrim numParts 0 xs).shape = sh := by
      unfold allReducePrim; dsimp only; rw [hhead]; rfl
    have hidx' : idx < prodShape (allReducePrim numParts 0 xs).shape := hidx
    rw [valAt_of_lt _ _ hidx']
    show (allReducePrim numParts 0 xs).val ⟨idx, hidx'⟩ = 0
    unfold allReducePrim
    simp only [Tensor.mkShape]
    exact foldl_add_zero_valAt idx 0 xs (fun t ht => hallval t ht idx)

end TrainVerify.Denote.JointWitness
