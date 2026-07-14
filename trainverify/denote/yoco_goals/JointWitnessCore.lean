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

/-! ## reconstructWithDim on zero stores -/

/-- reconstructWithDim of a list of zero tensors produces a zero tensor of a
    specific shape derived from the list content and gatherDim. -/
theorem reconstructWithDim_of_zeroTensors (gatherDim numParts : Nat)
    (xs : List Tensor) (sh : Shape)
    (hall : ∀ t ∈ xs, t = zeroTensor sh)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = sh) :
    ∃ resultShape,
      reconstructWithDim gatherDim numParts 0 xs = zeroTensor resultShape ∧
      -- the resultShape is determined by the case analysis on xs
      ((xs = [] ∧ resultShape = []) ∨
       (∃ x, xs = [x] ∧ x = zeroTensor sh ∧ resultShape = sh) ∨
       (sh = [1] ∧ resultShape = [1]) ∨
       (resultShape = sh.set gatherDim (sh.getD gatherDim 0 * numParts))) := by
  unfold reconstructWithDim
  match hxs : xs with
  | [] =>
    refine ⟨[], ?_, Or.inl ⟨rfl, rfl⟩⟩
    -- reconstructWithDim on [] = Tensor.mkShape [] (fun _ => 0) = zeroTensor []
    unfold zeroTensor Tensor.mkShape; rfl
  | [x] =>
    have hx_eq : x = zeroTensor sh := by
      apply hall x; simp
    refine ⟨sh, ?_, Or.inr (Or.inl ⟨x, rfl, hx_eq, rfl⟩)⟩
    exact hx_eq
  | x :: y :: rest =>
    -- Determine which branch we're in
    by_cases hsc : (((x :: y :: rest).head?).map (fun t => t.shape)).getD [] = [1]
    · -- allReduce branch
      simp only [hsc, if_true]
      have hshape1 : sh = [1] := by rw [← hsc]; exact hhead.symm
      refine ⟨[1], ?_, Or.inr (Or.inr (Or.inl ⟨hshape1, rfl⟩))⟩
      have := allReducePrim_of_zeroTensors numParts (x :: y :: rest) sh hhead hall
      rw [this, hshape1]
    · -- allGather branch
      simp only [hsc, if_false]
      refine ⟨sh.set gatherDim (sh.getD gatherDim 0 * numParts), ?_,
        Or.inr (Or.inr (Or.inr rfl))⟩
      exact allGatherPrimDimN_of_zeroTensors gatherDim numParts (x :: y :: rest) sh hall hhead

/-! ## Per-goal zeroStore soundness -/

/-- Predicate: a `LineageGoal` is "zero-store-satisfiable" given a shape map, if
    the shape-lookup values reconstruct the goal correctly under a zeroStore.

    We define a computable helper that checks the shape reconstruction; then
    prove `InitGoalHolds` follows when this returns `true`. -/
def goalShapeOK (shapeOf : Tid → Shape) (numParts : Nat) (g : LineageGoal) : Prop :=
  -- The reconstructed shape must equal g.tsShape, using the definitional cases
  -- of reconstructWithDim on zero tensors.
  shapeOf g.ts = g.tsShape ∧
  (g.tps.map (fun p => shapeOf p.tid)) = g.tpShapes ∧
  ( -- singleton reconstruction: reconstructWithDim on [x] = x, so tp shape = ts shape
    (g.tps.length = 1 ∧ ∃ tp, g.tps = [tp] ∧ shapeOf tp.tid = g.tsShape) ∨
    -- allReduce [1] case: nonempty tps required
    (g.tps ≠ [] ∧ (∀ tp ∈ g.tps, shapeOf tp.tid = [1]) ∧ g.tsShape = [1]) ∨
    -- allGather: tp shapes all equal shard sh, tsShape = sh with gatherDim scaled
    (∃ sh, (∀ tp ∈ g.tps, shapeOf tp.tid = sh) ∧
      sh ≠ [1] ∧
      g.tps.length ≥ 2 ∧
      g.tsShape = sh.set g.gatherDim (sh.getD g.gatherDim 0 * numParts)) )

/-- For a zeroStore, if goalShapeOK holds then InitGoalHolds holds. -/
theorem zeroStore_initGoalHolds (shapeOf : Tid → Shape) (numParts : Nat)
    (g : LineageGoal) (hOK : goalShapeOK shapeOf numParts g) :
    InitGoalHolds numParts g (zeroStore shapeOf) (zeroStore shapeOf) := by
  obtain ⟨hts, htps, hrec⟩ := hOK
  refine ⟨?_, ?_, ?_⟩
  · -- ts.shape = tsShape
    show (zeroStore shapeOf g.ts).shape = g.tsShape
    rw [zeroStore_shape, hts]
  · -- tps.map shape = tpShapes
    show (g.tps.map (fun p => (zeroStore shapeOf p.tid))).map (fun t => t.shape) = g.tpShapes
    rw [List.map_map]
    show (g.tps.map (fun p => (zeroStore shapeOf p.tid).shape)) = g.tpShapes
    simp only [zeroStore_shape]
    exact htps
  · -- ts = reconstructWithDim ... tps
    show (zeroStore shapeOf g.ts) =
      reconstructWithDim g.gatherDim numParts 0 (g.tps.map (fun p => zeroStore shapeOf p.tid))
    unfold zeroStore
    rw [hts]
    -- Now goal: zeroTensor g.tsShape = reconstructWithDim d n 0 (map ...)
    -- Case-analyze on hrec
    rcases hrec with ⟨hlen1, tp, htpseq, htp_ts⟩ | ⟨hnonempty, hall1, hts1⟩ | ⟨sh, hall, hne1, hlen2, htsShape⟩
    · -- singleton case
      rw [htpseq]
      simp only [List.map_cons, List.map_nil]
      rw [reconstructWithDim_singleton]
      rw [htp_ts]
    · -- allReduce [1] case
      have hmap : g.tps.map (fun p => zeroTensor (shapeOf p.tid)) =
          g.tps.map (fun _ => zeroTensor ([1] : Shape)) := by
        apply List.map_congr_left
        intro p hp
        rw [hall1 p hp]
      rw [hmap, hts1]
      generalize hL : g.tps.map (fun _ => zeroTensor ([1] : Shape)) = L
      have hallL : ∀ t ∈ L, t = zeroTensor [1] := by
        intro t ht; rw [← hL] at ht
        rcases List.mem_map.mp ht with ⟨p, _, hpeq⟩; exact hpeq.symm
      unfold reconstructWithDim
      cases L with
      | nil =>
        exfalso; apply hnonempty
        cases htps' : g.tps with
        | nil => rfl
        | cons a t => rw [htps'] at hL; simp at hL
      | cons a rest =>
        cases rest with
        | nil =>
          rw [show a = zeroTensor [1] from hallL a (by simp)]
        | cons b rest' =>
          have hhead1 : (Option.map (fun t : Tensor => t.shape) (a :: b :: rest').head?).getD [] = [1] := by
            simp; rw [hallL a (by simp)]; rfl
          simp only [hhead1, if_true]
          exact (allReducePrim_of_zeroTensors numParts _ _ hhead1 hallL).symm
    · -- allGather case
      have hmap : g.tps.map (fun p => zeroTensor (shapeOf p.tid)) =
          g.tps.map (fun _ => zeroTensor sh) := by
        apply List.map_congr_left
        intro p hp
        rw [hall p hp]
      rw [hmap, htsShape]
      generalize hL : g.tps.map (fun _ => zeroTensor sh) = L
      have hallL : ∀ t ∈ L, t = zeroTensor sh := by
        intro t ht; rw [← hL] at ht
        rcases List.mem_map.mp ht with ⟨_, _, hpeq⟩; exact hpeq.symm
      have hlenL : L.length ≥ 2 := by rw [← hL, List.length_map]; exact hlen2
      unfold reconstructWithDim
      cases L with
      | nil => simp at hlenL
      | cons a rest =>
        cases rest with
        | nil => simp at hlenL
        | cons b rest' =>
          have hhead_sh : (Option.map (fun t : Tensor => t.shape) (a :: b :: rest').head?).getD [] = sh := by
            simp; rw [hallL a (by simp)]; rfl
          have hne : (Option.map (fun t : Tensor => t.shape) (a :: b :: rest').head?).getD [] ≠ [1] := by
            rw [hhead_sh]; exact hne1
          simp only [hne, if_false]
          exact (allGatherPrimDimN_of_zeroTensors g.gatherDim numParts _ _ hallL hhead_sh).symm

end TrainVerify.Denote.JointWitness
