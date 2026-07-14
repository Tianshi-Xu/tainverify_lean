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

/-- Predicate: shape maps for SM (ts side) and PM (tps side) are consistent. -/
def goalShapeOK2 (shapeOfSM shapeOfPM : Tid → Shape) (numParts : Nat) (g : LineageGoal) : Prop :=
  shapeOfSM g.ts = g.tsShape ∧
  (g.tps.map (fun p => shapeOfPM p.tid)) = g.tpShapes ∧
  ( (g.tps.length = 1 ∧ ∃ tp, g.tps = [tp] ∧ shapeOfPM tp.tid = g.tsShape) ∨
    (g.replicated = false ∧ g.tps ≠ [] ∧ (∀ tp ∈ g.tps, shapeOfPM tp.tid = [1]) ∧ g.tsShape = [1]) ∨
    (g.replicated = false ∧ ∃ sh, (∀ tp ∈ g.tps, shapeOfPM tp.tid = sh) ∧
      sh ≠ [1] ∧
      g.tps.length ≥ 2 ∧
      g.tsShape = sh.set g.gatherDim (sh.getD g.gatherDim 0 * numParts)) ∨
    -- Replicated case: g.replicated = true, all shards = tsShape, pick head.
    (g.replicated = true ∧ g.tps ≠ [] ∧
      (∀ tp ∈ g.tps, shapeOfPM tp.tid = g.tsShape)) )

/-- Computable form for two-store version. -/
def goalShapeOK2_check (shapeOfSM shapeOfPM : Tid → Shape) (numParts : Nat)
    (g : LineageGoal) : Bool :=
  decide (shapeOfSM g.ts = g.tsShape) &&
  decide ((g.tps.map (fun p => shapeOfPM p.tid)) = g.tpShapes) &&
  ( match g.tps with
    | [] => false
    | [tp] => decide (shapeOfPM tp.tid = g.tsShape)
    | tp0 :: tps' =>
      let sh0 := shapeOfPM tp0.tid
      let allSame := (tp0 :: tps').all (fun p => decide (shapeOfPM p.tid = sh0))
      -- Replicated branch: g.replicated=true and all shards = tsShape
      if g.replicated then
        allSame && decide (sh0 = g.tsShape)
      else
        allSame &&
        ( (decide (sh0 = [1]) && decide (g.tsShape = [1])) ||
          (!decide (sh0 = [1]) &&
            decide (g.tsShape = sh0.set g.gatherDim (sh0.getD g.gatherDim 0 * numParts))) ) )

theorem goalShapeOK2_of_check {shapeOfSM shapeOfPM : Tid → Shape} {numParts : Nat}
    {g : LineageGoal}
    (h : goalShapeOK2_check shapeOfSM shapeOfPM numParts g = true) :
    goalShapeOK2 shapeOfSM shapeOfPM numParts g := by
  unfold goalShapeOK2_check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hts, htps⟩, hmatch⟩ := h
  refine ⟨hts, htps, ?_⟩
  match hg : g.tps, hmatch with
  | [], hm => simp at hm
  | [tp], hm =>
    left
    simp only at hm
    exact ⟨by simp, tp, rfl, of_decide_eq_true hm⟩
  | tp0 :: tp1 :: rest, hm =>
    right
    -- Case split on whether g.replicated is true (from computable check)
    by_cases hrepl : g.replicated
    · -- Replicated branch selected
      simp only [hrepl, if_true, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hm
      right; right
      obtain ⟨⟨hs0_self, hs1, hsRest⟩, hts_eq⟩ := hm
      refine ⟨hrepl, by simp, ?_⟩
      intro tp htp
      rcases List.mem_cons.mp htp with rfl | hp'
      · exact hts_eq
      · rcases List.mem_cons.mp hp' with rfl | hp''
        · rw [hs1, hts_eq]
        · have := (List.all_eq_true.mp hsRest) tp hp''
          rw [of_decide_eq_true this, hts_eq]
    · -- Non-replicated branch (original 3-way disjunct, all with hrp : g.replicated = false)
      have hrpFalse : g.replicated = false := Bool.not_eq_true _ |>.mp hrepl
      simp only [hrpFalse, Bool.false_eq_true, if_false, List.all_cons, Bool.and_eq_true,
                 decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hallB, hbranch⟩ := hm
      have hallSame : ∀ p ∈ (tp0 :: tp1 :: rest), shapeOfPM p.tid = shapeOfPM tp0.tid := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · rfl
        · rcases List.mem_cons.mp hp' with rfl | hp''
          · exact hallB.2.1
          · have hrest : (rest.all (fun q => decide (shapeOfPM q.tid = shapeOfPM tp0.tid))) = true := hallB.2.2
            exact of_decide_eq_true ((List.all_eq_true.mp hrest) p hp'')
      rcases hbranch with ⟨hsh1, hts1⟩ | ⟨hsh_ne, hts_gather⟩
      · left
        refine ⟨hrpFalse, by simp, ?_, hts1⟩
        intro tp htp; rw [hallSame tp htp, hsh1]
      · right; left
        refine ⟨hrpFalse, shapeOfPM tp0.tid, ?_, of_decide_eq_false hsh_ne, ?_, hts_gather⟩
        · intro tp htp; exact hallSame tp htp
        · simp

/-- Two-store zero InitGoalHolds. -/
theorem zeroStore2_initGoalHolds (shapeOfSM shapeOfPM : Tid → Shape) (numParts : Nat)
    (g : LineageGoal) (hOK : goalShapeOK2 shapeOfSM shapeOfPM numParts g) :
    InitGoalHolds numParts g (zeroStore shapeOfSM) (zeroStore shapeOfPM) := by
  obtain ⟨hts, htps, hrec⟩ := hOK
  refine ⟨?_, ?_, ?_⟩
  · show (zeroStore shapeOfSM g.ts).shape = g.tsShape
    rw [zeroStore_shape, hts]
  · show (g.tps.map (fun p => (zeroStore shapeOfPM p.tid))).map (fun t => t.shape) = g.tpShapes
    rw [List.map_map]
    have hfun : ((fun t : Tensor => t.shape) ∘ (fun p : Piece => zeroStore shapeOfPM p.tid)) =
        (fun p : Piece => shapeOfPM p.tid) := by
      funext p; exact zeroStore_shape shapeOfPM p.tid
    rw [hfun]; exact htps
  · show (zeroStore shapeOfSM g.ts) =
      reconstructForGoal g numParts (g.tps.map (fun p => zeroStore shapeOfPM p.tid))
    unfold zeroStore
    rw [hts]
    rcases hrec with ⟨hlen1, tp, htpseq, htp_ts⟩ | ⟨hrpF, hnonempty, hall1, hts1⟩ | ⟨hrpF, sh, hall, hne1, hlen2, htsShape⟩ | ⟨hrepl, hnonempty, hallRep⟩
    · -- singleton case: reconstructForGoal → reconstructWithDim on [x] → x
      rw [htpseq]
      simp only [List.map_cons, List.map_nil, reconstructForGoal]
      by_cases hrp : g.replicated
      · simp [hrp, List.headD]
        exact congrArg zeroTensor htp_ts.symm
      · simp [hrp, reconstructWithDim_singleton]
        exact congrArg zeroTensor htp_ts.symm
    · -- allReduce [1] case (non-replicated)
      have hmap : g.tps.map (fun p => zeroTensor (shapeOfPM p.tid)) =
          g.tps.map (fun _ => zeroTensor ([1] : Shape)) := by
        apply List.map_congr_left; intro p hp; rw [hall1 p hp]
      rw [hmap, hts1, reconstructForGoal, hrpF]
      simp only [Bool.false_eq_true, if_false]
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
        | nil => rw [show a = zeroTensor [1] from hallL a (by simp)]
        | cons b rest' =>
          have hhead1 : (Option.map (fun t : Tensor => t.shape) (a :: b :: rest').head?).getD [] = [1] := by
            simp; rw [hallL a (by simp)]; rfl
          simp only [hhead1, if_true]
          exact (allReducePrim_of_zeroTensors numParts _ _ hhead1 hallL).symm
    · -- allGather case (non-replicated)
      have hmap : g.tps.map (fun p => zeroTensor (shapeOfPM p.tid)) =
          g.tps.map (fun _ => zeroTensor sh) := by
        apply List.map_congr_left; intro p hp; rw [hall p hp]
      rw [hmap, htsShape, reconstructForGoal, hrpF]
      simp only [Bool.false_eq_true, if_false]
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
    · -- Replicated case: pick head
      have hmap : g.tps.map (fun p => zeroTensor (shapeOfPM p.tid)) =
          g.tps.map (fun _ => zeroTensor g.tsShape) := by
        apply List.map_congr_left; intro p hp; rw [hallRep p hp]
      rw [hmap, reconstructForGoal, hrepl]
      simp only [if_true]
      generalize hL : g.tps.map (fun _ : Piece => zeroTensor g.tsShape) = L
      cases L with
      | nil =>
        exfalso; apply hnonempty
        cases htps' : g.tps with
        | nil => rfl
        | cons a t => rw [htps'] at hL; simp at hL
      | cons a rest =>
        have haeq : a = zeroTensor g.tsShape := by
          have : a ∈ (a :: rest) := by simp
          rw [← hL] at this
          rcases List.mem_map.mp this with ⟨_, _, hpeq⟩; exact hpeq.symm
        simp [List.headD, haeq]

/-- Two-store list-level version. -/
def goalsShapeOK2_check_all (shapeOfSM shapeOfPM : Tid → Shape) (numParts : Nat)
    (goals : List LineageGoal) : Bool :=
  goals.all (goalShapeOK2_check shapeOfSM shapeOfPM numParts)

theorem zeroStore2_initGoalsHold (shapeOfSM shapeOfPM : Tid → Shape) (numParts : Nat)
    (goals : List LineageGoal)
    (h : goalsShapeOK2_check_all shapeOfSM shapeOfPM numParts goals = true) :
    InitGoalsHold numParts goals (zeroStore shapeOfSM) (zeroStore shapeOfPM) := by
  intro g hg
  apply zeroStore2_initGoalHolds
  apply goalShapeOK2_of_check
  exact (List.all_eq_true.mp h) g hg

/-- If a Tid → Shape function agrees with a shape env's list on every pair
    in the list, then StoreShapesHold holds for the corresponding zero store. -/
theorem zeroStore_shapes_hold_of_list {shapeOf : Tid → Shape} {xs : List (Tid × Shape)}
    (h : xs.all (fun p => decide (shapeOf p.1 = p.2)) = true) :
    StoreShapesHold (zeroStore shapeOf) (shapeEnvOfList xs) := by
  intro tid sh hsh
  rw [zeroStore_shape]
  -- shapeEnvOfList xs tid = some sh means find? returned (tid, sh)
  unfold shapeEnvOfList at hsh
  cases hf : xs.find? (fun p => p.1 = tid) with
  | none => rw [hf] at hsh; simp at hsh
  | some pair =>
    rw [hf] at hsh
    -- hsh : some pair.2 = some sh
    have : pair.2 = sh := by simp at hsh; exact hsh
    -- pair ∈ xs and pair.1 = tid
    have hmem : pair ∈ xs := List.mem_of_find?_eq_some hf
    have hkey : pair.1 = tid := by
      have := List.find?_some hf
      exact of_decide_eq_true this
    have hval := of_decide_eq_true ((List.all_eq_true.mp h) pair hmem)
    rw [← hkey, hval, this]

end TrainVerify.Denote.JointWitness
