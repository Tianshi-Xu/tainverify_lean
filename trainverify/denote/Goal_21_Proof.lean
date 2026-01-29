/- Manual proof for Goal 21 (split file). -/
import denote.Goal_21

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.ManualProofs

set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

/-!
## Goal 21

Outline:
- Unfold `goal_21_stmt_cut`.
- Use the assumption `goal_21_cut_initGoals = initGoals ++ goal_21_prereqs` to get
  intermediate consistency for tid=17.
- Unfold `denoteGraph` for `sm_goal_21` and `pm_goal_21` (small graphs).
- Use `BW_sum` + `AllGatherPrim` reconstruction lemma to show `tid=24` matches.
- Then use `BW_linear` lemma to conclude for `tid=21`.
-/

-- Precomputed facts about pm_goal_21 to avoid repeated simp calls
theorem pm_goal_21_numRanks_eq : pm_goal_21.numRanks = 4 := rfl
theorem pm_goal_21_numRanks_pos : 0 < pm_goal_21.numRanks := by decide

-- Helper: shape rewrite for pm_goal_21 with numRanks=4
theorem pm_goal_21_128_eq_4_times_32 : 128 = pm_goal_21.numRanks * 32 := rfl
theorem pm_goal_21_32_eq_128_div_4 : 32 = 128 / pm_goal_21.numRanks := rfl

-- Helper lemma for chunkPrim shape calculations
theorem pm_goal_21_chunkPrim_shape (t : Tensor) (r : Nat) (ht : t.shape = [128, 128]) :
    (chunkPrim pm_goal_21.numRanks r t).shape = [128, 32] := by
  have hsh : t.shape = [128, pm_goal_21.numRanks * 32] := by
    rw [pm_goal_21_128_eq_4_times_32] at ht; exact ht
  exact chunkPrim_shape' pm_goal_21.numRanks r 128 32 t hsh pm_goal_21_numRanks_pos

-- Prefix/suffix node lists for pm_goal_21 to keep proofs small.
abbrev pm21_n26 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [26] }
abbrev pm21_n17 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim", ins := [34, 35, 36, 37], outs := [17] }
abbrev pm21_n27 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [27] }
abbrev pm21_n28 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [28] }
abbrev pm21_n29 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [29] }
abbrev pm21_n54 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [17], outs := [54] }
abbrev pm21_n55 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [17], outs := [55] }
abbrev pm21_n56 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [17], outs := [56] }
abbrev pm21_n57 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [17], outs := [57] }
abbrev pm21_n70 : NodeDecl :=
  { rank := 0, op := "OpName.BW_sum", ins := [25, 54], outs := [70] }
abbrev pm21_n71 : NodeDecl :=
  { rank := 1, op := "OpName.BW_sum", ins := [25, 55], outs := [71] }
abbrev pm21_n72 : NodeDecl :=
  { rank := 2, op := "OpName.BW_sum", ins := [25, 56], outs := [72] }
abbrev pm21_n73 : NodeDecl :=
  { rank := 3, op := "OpName.BW_sum", ins := [25, 57], outs := [73] }

abbrev pm21_pre1a : List NodeDecl :=
  [pm21_n26, pm21_n17, pm21_n27, pm21_n28, pm21_n29]
abbrev pm21_pre1b : List NodeDecl :=
  [pm21_n54, pm21_n55, pm21_n56, pm21_n57]
abbrev pm21_pre1 : List NodeDecl :=
  pm21_pre1a ++ pm21_pre1b
abbrev pm21_pre2 : List NodeDecl :=
  [pm21_n70, pm21_n71, pm21_n72, pm21_n73]
abbrev pm21_prefix_pre : List NodeDecl :=
  pm21_pre1 ++ pm21_pre2

abbrev pm21_prefix_last : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [70, 71, 72, 73], outs := [24] }

abbrev pm21_prefix : List NodeDecl :=
  pm21_prefix_pre ++ [pm21_prefix_last]

abbrev pm21_suffix : List NodeDecl :=
  [ { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] },
    { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] },
    { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] },
    { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ]

-- Small structural lemmas for pm_goal_21
lemma pm21_split (initPM : Store) :
    denoteGraph pm_goal_21 initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) := by
  simpa [pm_goal_21, pm21_prefix, pm21_suffix] using
    (denoteGraph_nodes_append pm_goal_21 pm21_prefix pm21_suffix initPM)

lemma pm21_suffix_preserves_24 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 24 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 24 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_21)
    (s := denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)
    (tid := 24) (nodes := pm21_suffix)
  intro n hn
  have hn' :
      n = { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] } ∨
      n = { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] } ∨
      n = { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] } ∨
      n = { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ∨
      n ∈ [] := by
    simpa only [pm21_suffix, List.mem_cons] using hn
  rcases hn' with rfl | rfl | rfl | rfl | hnil
  · simp
  · simp
  · simp
  · simp
  · simp at hnil

lemma pm21_suffix_preserves_26 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 26 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 26 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_21)
    (s := denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)
    (tid := 26) (nodes := pm21_suffix)
  intro n hn
  have hn' :
      n = { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] } ∨
      n = { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] } ∨
      n = { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] } ∨
      n = { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ∨
      n ∈ [] := by
    simpa only [pm21_suffix, List.mem_cons] using hn
  rcases hn' with rfl | rfl | rfl | rfl | hnil
  · simp
  · simp
  · simp
  · simp
  · simp at hnil

lemma pm21_suffix_preserves_27 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 27 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 27 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_21)
    (s := denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)
    (tid := 27) (nodes := pm21_suffix)
  intro n hn
  have hn' :
      n = { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] } ∨
      n = { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] } ∨
      n = { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] } ∨
      n = { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ∨
      n ∈ [] := by
    simpa only [pm21_suffix, List.mem_cons] using hn
  rcases hn' with rfl | rfl | rfl | rfl | hnil
  · simp
  · simp
  · simp
  · simp
  · simp at hnil

lemma pm21_suffix_preserves_28 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 28 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 28 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_21)
    (s := denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)
    (tid := 28) (nodes := pm21_suffix)
  intro n hn
  have hn' :
      n = { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] } ∨
      n = { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] } ∨
      n = { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] } ∨
      n = { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ∨
      n ∈ [] := by
    simpa only [pm21_suffix, List.mem_cons] using hn
  rcases hn' with rfl | rfl | rfl | rfl | hnil
  · simp
  · simp
  · simp
  · simp
  · simp at hnil

lemma pm21_suffix_preserves_29 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 29 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 29 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_21)
    (s := denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)
    (tid := 29) (nodes := pm21_suffix)
  intro n hn
  have hn' :
      n = { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] } ∨
      n = { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] } ∨
      n = { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] } ∨
      n = { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ∨
      n ∈ [] := by
    simpa only [pm21_suffix, List.mem_cons] using hn
  rcases hn' with rfl | rfl | rfl | rfl | hnil
  · simp
  · simp
  · simp
  · simp
  · simp at hnil

lemma pm21_prefix_tid26 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 26 =
      chunkPrim pm_goal_21.numRanks 0 (initPM 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_prefix_tid27 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 27 =
      chunkPrim pm_goal_21.numRanks 1 (initPM 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_prefix_tid28 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 28 =
      chunkPrim pm_goal_21.numRanks 2 (initPM 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_prefix_tid29 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 29 =
      chunkPrim pm_goal_21.numRanks 3 (initPM 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_prefix_tid17 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 17 =
      allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37] := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet,
    storeSet_eq_of_not_mem_fst]

lemma pm21_suffix_preserves_17 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 17 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 17 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_21)
    (s := denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)
    (tid := 17) (nodes := pm21_suffix)
  intro n hn
  have hn' :
      n = { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] } ∨
      n = { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] } ∨
      n = { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] } ∨
      n = { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ∨
      n ∈ [] := by
    simpa only [pm21_suffix, List.mem_cons] using hn
  rcases hn' with rfl | rfl | rfl | rfl | hnil
  · simp
  · simp
  · simp
  · simp
  · simp at hnil

lemma pm21_suffix_tid46 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 46 =
      (bw_linear
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 24)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 26)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 30)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_suffix_tid48 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 48 =
      (bw_linear
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 24)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 27)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 31)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_suffix_tid50 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 50 =
      (bw_linear
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 24)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 28)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 32)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_suffix_tid52 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_suffix }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM)) 52 =
      (bw_linear
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 24)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 29)
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM 33)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm21_pre1a_tid17 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17 =
      allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37] := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM =
      denoteGraph { pm_goal_21 with nodes := [pm21_n27, pm21_n28, pm21_n29] }
        (denoteGraph { pm_goal_21 with nodes := [pm21_n26, pm21_n17] } initPM) := by
    simp [pm21_pre1a, pm21_n26, pm21_n17, pm21_n27, pm21_n28, pm21_n29]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n27, pm21_n28, pm21_n29] }
          (denoteGraph { pm_goal_21 with nodes := [pm21_n26, pm21_n17] } initPM)) 17 =
        (denoteGraph { pm_goal_21 with nodes := [pm21_n26, pm21_n17] } initPM) 17 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n27, pm21_n28, pm21_n29])
      (init := denoteGraph { pm_goal_21 with nodes := [pm21_n26, pm21_n17] } initPM)
      (tid := 17)
    intro n hn
    have hn' :
        n = pm21_n27 ∨ n = pm21_n28 ∨ n = pm21_n29 ∨ n ∈ [] := by
      simpa only [List.mem_cons] using hn
    rcases hn' with rfl | rfl | rfl | hnil
    · simp [pm21_n27]
    · simp [pm21_n28]
    · simp [pm21_n29]
    · simp at hnil
  have hpair :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n26, pm21_n17] } initPM) 17 =
        allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37] := by
    simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17
        = (denoteGraph { pm_goal_21 with nodes := [pm21_n26, pm21_n17] } initPM) 17 := by
            simpa [hsplit] using hpres
    _ = _ := hpair

lemma pm21_pre1_tid17 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 17 =
      allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37] := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) := by
    simp [pm21_pre1, pm21_pre1a, pm21_pre1b]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
          (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM)) 17 =
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := pm21_pre1b)
      (init := denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM)
      (tid := 17)
    intro n hn
    have hn' :
        n = pm21_n54 ∨ n = pm21_n55 ∨ n = pm21_n56 ∨ n = pm21_n57 ∨ n ∈ [] := by
      simpa only [pm21_pre1b, List.mem_cons] using hn
    rcases hn' with rfl | rfl | rfl | rfl | hnil
    · simp [pm21_n54]
    · simp [pm21_n55]
    · simp [pm21_n56]
    · simp [pm21_n57]
    · simp at hnil
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 17
        = (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17 := by
            simpa [hsplit] using hpres
    _ = _ := pm21_pre1a_tid17 initPM

lemma pm21_pre1_tid54 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 54 =
      chunkPrim pm_goal_21.numRanks 0
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) := by
    simp [pm21_pre1, pm21_pre1a, pm21_pre1b]
  have hpre1b :
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) =
      denoteGraph { pm_goal_21 with nodes := [pm21_n55, pm21_n56, pm21_n57] }
        (applyNode pm_goal_21
          (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54) := by
    simp [pm21_pre1b, pm21_n54, pm21_n55, pm21_n56, pm21_n57, denoteGraph_nodes_cons]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n55, pm21_n56, pm21_n57] }
        (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)) 54 =
        (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54) 54 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n55, pm21_n56, pm21_n57])
      (init := applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
      (tid := 54)
    intro n hn
    simp [pm21_n55, pm21_n56, pm21_n57] at hn
    rcases hn with rfl | rfl | rfl <;> simp
  have h54 :
      (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54) 54 =
        chunkPrim pm_goal_21.numRanks 0
          ((denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17) := by
    simpa [pm21_n54] using
      (applyNode_chunkPrim_out pm_goal_21
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 0 17 54)
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 54
        = (denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
            (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM)) 54 := by
        rw [hsplit]
    _ = (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54) 54 := by
        rw [hpre1b]
        exact hpres
    _ = chunkPrim pm_goal_21.numRanks 0
          (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
        rw [h54, pm21_pre1a_tid17]

lemma pm21_pre1_tid55 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 55 =
      chunkPrim pm_goal_21.numRanks 1
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) := by
    simp [pm21_pre1, pm21_pre1a, pm21_pre1b]
  have hpre1b :
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) =
      denoteGraph { pm_goal_21 with nodes := [pm21_n56, pm21_n57] }
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55) := by
    simp [pm21_pre1b, pm21_n54, pm21_n55, pm21_n56, pm21_n57, denoteGraph_nodes_cons]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n56, pm21_n57] }
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55)) 55 =
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55) 55 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n56, pm21_n57])
      (init := applyNode pm_goal_21
        (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54) pm21_n55)
      (tid := 55)
    intro n hn
    simp [pm21_n56, pm21_n57] at hn
    rcases hn with rfl | rfl <;> simp
  have h55 :
      (applyNode pm_goal_21
        (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
        pm21_n55) 55 =
        chunkPrim pm_goal_21.numRanks 1
          ((denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17) := by
    simpa [pm21_n55] using
      (applyNode_chunkPrim_out pm_goal_21
        (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
        1 17 55)
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 55
        = (denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
            (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM)) 55 := by
            rw [hsplit]
    _ = (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55) 55 := by
            rw [hpre1b]
            exact hpres
    _ = chunkPrim pm_goal_21.numRanks 1
          (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
            rw [h55, pm21_pre1a_tid17]

lemma pm21_pre1_tid56 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 56 =
      chunkPrim pm_goal_21.numRanks 2
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) := by
    simp [pm21_pre1, pm21_pre1a, pm21_pre1b]
  have hpre1b :
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) =
      denoteGraph { pm_goal_21 with nodes := [pm21_n57] }
        (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56) := by
    simp [pm21_pre1b, pm21_n54, pm21_n55, pm21_n56, pm21_n57, denoteGraph_nodes_cons]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n57] }
        (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56)) 56 =
        (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56) 56 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n57])
      (init := applyNode pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55) pm21_n56)
      (tid := 56)
    intro n hn
    simp [pm21_n57] at hn
    rcases hn with rfl <;> simp
  have h56 :
      (applyNode pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55)
        pm21_n56) 56 =
        chunkPrim pm_goal_21.numRanks 2
          ((denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17) := by
    simpa [pm21_n56] using
      (applyNode_chunkPrim_out pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
          pm21_n55)
        2 17 56)
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 56
        = (denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
            (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM)) 56 := by
            rw [hsplit]
    _ = (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56) 56 := by
            rw [hpre1b]
            exact hpres
    _ = chunkPrim pm_goal_21.numRanks 2
          (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
            rw [h56, pm21_pre1a_tid17]

lemma pm21_pre1_tid57 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 57 =
      chunkPrim pm_goal_21.numRanks 3
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) := by
    simp [pm21_pre1, pm21_pre1a, pm21_pre1b]
  have hpre1b :
      denoteGraph { pm_goal_21 with nodes := pm21_pre1b }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) =
      applyNode pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56)
        pm21_n57 := by
    simp [pm21_pre1b, pm21_n54, pm21_n55, pm21_n56, pm21_n57, denoteGraph_nodes_cons]
  have h57 :
      (applyNode pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56)
        pm21_n57) 57 =
        chunkPrim pm_goal_21.numRanks 3
          ((denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) 17) := by
    simpa [pm21_n57] using
      (applyNode_chunkPrim_out pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
            pm21_n55)
          pm21_n56)
        3 17 57)
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 57
        = (applyNode pm_goal_21
            (applyNode pm_goal_21
              (applyNode pm_goal_21
                (applyNode pm_goal_21 (denoteGraph { pm_goal_21 with nodes := pm21_pre1a } initPM) pm21_n54)
                pm21_n55)
              pm21_n56)
            pm21_n57) 57 := by
            rw [hsplit, hpre1b]
    _ = chunkPrim pm_goal_21.numRanks 3
          (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) := by
            rw [h57, pm21_pre1a_tid17]

lemma pm21_pre1_tid25 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) 25 = initPM 25 := by
  apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
    (nodes := pm21_pre1) (init := initPM) (tid := 25)
  intro n hn
  simp [pm21_pre1, pm21_pre1a, pm21_pre1b] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [pm21_n26, pm21_n17, pm21_n27, pm21_n28, pm21_n29, pm21_n54, pm21_n55, pm21_n56, pm21_n57]

lemma pm21_prefix_tid24 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 24 =
      allGatherPrim pm_goal_21.numRanks 0
        [ (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 70,
          (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 71,
          (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 72,
          (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 73 ] := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM =
      denoteGraph { pm_goal_21 with nodes := [pm21_prefix_last] }
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) := by
    simp [pm21_prefix, pm21_prefix_pre, pm21_prefix_last]
  -- apply the allGather node to the store after prefix
  rw [hsplit]
  simp [pm21_prefix_last, denoteGraph_nodes_cons, applyNode_allGatherPrim_out]

lemma pm21_prefix_pre_tid70 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 70 =
      bw_sum (initPM 25)
        (chunkPrim pm_goal_21.numRanks 0
          (allReducePrim pm_goal_21.numRanks 0
            [initPM 34, initPM 35, initPM 36, initPM 37])) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre2 }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) := by
    simp [pm21_prefix_pre, pm21_pre1, pm21_pre2]
  set s1 := denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM
  have hpre2 : denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1 =
      denoteGraph { pm_goal_21 with nodes := [pm21_n71, pm21_n72, pm21_n73] }
        (applyNode pm_goal_21 s1 pm21_n70) := by
    simp [pm21_pre2, pm21_n70, pm21_n71, pm21_n72, pm21_n73, denoteGraph_nodes_cons]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n71, pm21_n72, pm21_n73] }
        (applyNode pm_goal_21 s1 pm21_n70)) 70 =
        (applyNode pm_goal_21 s1 pm21_n70) 70 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n71, pm21_n72, pm21_n73])
      (init := applyNode pm_goal_21 s1 pm21_n70) (tid := 70)
    intro n hn
    simp [pm21_n71, pm21_n72, pm21_n73] at hn
    rcases hn with rfl | rfl | rfl <;> simp [pm21_n71, pm21_n72, pm21_n73]
  have h70 : (applyNode pm_goal_21 s1 pm21_n70) 70 = bw_sum (s1 25) (s1 54) :=
    applyNode_bw_sum_out pm_goal_21 s1 0 25 54 70
  have h25 : s1 25 = initPM 25 := pm21_pre1_tid25 initPM
  have h54 : s1 54 =
      chunkPrim pm_goal_21.numRanks 0
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) :=
    pm21_pre1_tid54 initPM
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 70
        = (denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1) 70 := by
          simp only [hsplit, s1]
    _ = (applyNode pm_goal_21 s1 pm21_n70) 70 := by
          rw [hpre2]
          exact hpres
    _ = bw_sum (initPM 25)
          (chunkPrim pm_goal_21.numRanks 0
            (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37])) := by
            simp only [h70, h25, h54]

lemma pm21_prefix_pre_tid71 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 71 =
      bw_sum (initPM 25)
        (chunkPrim pm_goal_21.numRanks 1
          (allReducePrim pm_goal_21.numRanks 0
            [initPM 34, initPM 35, initPM 36, initPM 37])) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre2 }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) := by
    simp [pm21_prefix_pre, pm21_pre1, pm21_pre2]
  set s1 := denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM
  have hpre2 : denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1 =
      denoteGraph { pm_goal_21 with nodes := [pm21_n72, pm21_n73] }
        (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) := by
    simp [pm21_pre2, pm21_n70, pm21_n71, pm21_n72, pm21_n73, denoteGraph_nodes_cons]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n72, pm21_n73] }
        (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71)) 71 =
        (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 71 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n72, pm21_n73])
      (init := applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) (tid := 71)
    intro n hn
    simp [pm21_n72, pm21_n73] at hn
    rcases hn with rfl | rfl <;> simp [pm21_n72, pm21_n73]
  have h71 :
      (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 71 =
        bw_sum ((applyNode pm_goal_21 s1 pm21_n70) 25) ((applyNode pm_goal_21 s1 pm21_n70) 55) :=
    applyNode_bw_sum_out pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) 1 25 55 71
  have h25 : (applyNode pm_goal_21 s1 pm21_n70) 25 = s1 25 := by
    apply applyNode_eq_of_not_mem_outs (g := pm_goal_21) (s := s1) (n := pm21_n70) (tid := 25)
    simp
  have h55 : (applyNode pm_goal_21 s1 pm21_n70) 55 = s1 55 := by
    apply applyNode_eq_of_not_mem_outs (g := pm_goal_21) (s := s1) (n := pm21_n70) (tid := 55)
    simp
  have hs1_25 : s1 25 = initPM 25 := pm21_pre1_tid25 initPM
  have hs1_55 : s1 55 =
      chunkPrim pm_goal_21.numRanks 1
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) :=
    pm21_pre1_tid55 initPM
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 71
      = (denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1) 71 := by
          simp only [hsplit]
    _ = (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 71 := by
          rw [hpre2]
          exact hpres
    _ = bw_sum (initPM 25)
          (chunkPrim pm_goal_21.numRanks 1
            (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37])) := by
            simp only [h71, h25, h55, hs1_25, hs1_55]

lemma pm21_prefix_pre_tid72 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 72 =
      bw_sum (initPM 25)
        (chunkPrim pm_goal_21.numRanks 2
          (allReducePrim pm_goal_21.numRanks 0
            [initPM 34, initPM 35, initPM 36, initPM 37])) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre2 }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) := by
    simp [pm21_prefix_pre, pm21_pre1, pm21_pre2]
  set s1 := denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM
  have hpre2 : denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1 =
      denoteGraph { pm_goal_21 with nodes := [pm21_n73] }
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72) := by
    simp [pm21_pre2, pm21_n70, pm21_n71, pm21_n72, pm21_n73, denoteGraph_nodes_cons]
  have hpres :
      (denoteGraph { pm_goal_21 with nodes := [pm21_n73] }
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72)) 72 =
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72) 72 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := pm_goal_21)
      (nodes := [pm21_n73])
      (init := applyNode pm_goal_21
        (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72) (tid := 72)
    intro n hn
    simp [pm21_n73] at hn
    rcases hn with rfl <;> simp [pm21_n73]
  have h72 :
      (applyNode pm_goal_21
        (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72) 72 =
        bw_sum ((applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 25)
          ((applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 56) :=
    applyNode_bw_sum_out pm_goal_21
        (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 2 25 56 72
  have h25a : (applyNode pm_goal_21 s1 pm21_n70) 25 = s1 25 := by
    apply applyNode_eq_of_not_mem_outs (g := pm_goal_21) (s := s1) (n := pm21_n70) (tid := 25)
    simp
  have h25 : (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 25 = s1 25 := by
    have h := applyNode_eq_of_not_mem_outs (g := pm_goal_21)
      (s := applyNode pm_goal_21 s1 pm21_n70) (n := pm21_n71) (tid := 25)
      (by simp)
    rw [h, h25a]
  have h56a : (applyNode pm_goal_21 s1 pm21_n70) 56 = s1 56 := by
    apply applyNode_eq_of_not_mem_outs (g := pm_goal_21) (s := s1) (n := pm21_n70) (tid := 56)
    simp
  have h56 : (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 56 = s1 56 := by
    have h := applyNode_eq_of_not_mem_outs (g := pm_goal_21)
      (s := applyNode pm_goal_21 s1 pm21_n70) (n := pm21_n71) (tid := 56)
      (by simp)
    rw [h, h56a]
  have hs1_25 : s1 25 = initPM 25 := pm21_pre1_tid25 initPM
  have hs1_56 : s1 56 =
      chunkPrim pm_goal_21.numRanks 2
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) :=
    pm21_pre1_tid56 initPM
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 72
      = (denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1) 72 := by
        simp only [hsplit]
    _ = (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72) 72 := by
            rw [hpre2]
            exact hpres
    _ = bw_sum (initPM 25)
          (chunkPrim pm_goal_21.numRanks 2
            (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37])) := by
            simp only [h72, h25, h56, hs1_25, hs1_56]

lemma pm21_prefix_pre_tid73 (initPM : Store) :
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 73 =
      bw_sum (initPM 25)
        (chunkPrim pm_goal_21.numRanks 3
          (allReducePrim pm_goal_21.numRanks 0
            [initPM 34, initPM 35, initPM 36, initPM 37])) := by
  have hsplit : denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM =
      denoteGraph { pm_goal_21 with nodes := pm21_pre2 }
        (denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM) := by
    simp [pm21_prefix_pre, pm21_pre1, pm21_pre2]
  set s1 := denoteGraph { pm_goal_21 with nodes := pm21_pre1 } initPM
  have hpre2 : denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1 =
      applyNode pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72)
        pm21_n73 := by
    simp [pm21_pre2, pm21_n70, pm21_n71, pm21_n72, pm21_n73, denoteGraph_nodes_cons]
  have h73 :
      (applyNode pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72)
        pm21_n73) 73 =
        bw_sum ((applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 25)
          ((applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 57) :=
    applyNode_bw_sum_out pm_goal_21
        (applyNode pm_goal_21
          (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72)
        3 25 57 73
  have h25a : (applyNode pm_goal_21 s1 pm21_n70) 25 = s1 25 := by
    apply applyNode_eq_of_not_mem_outs (g := pm_goal_21) (s := s1) (n := pm21_n70) (tid := 25)
    simp
  have h25 : (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 25 = s1 25 := by
    have h := applyNode_eq_of_not_mem_outs (g := pm_goal_21)
      (s := applyNode pm_goal_21 s1 pm21_n70) (n := pm21_n71) (tid := 25)
      (by simp)
    rw [h, h25a]
  have h57a : (applyNode pm_goal_21 s1 pm21_n70) 57 = s1 57 := by
    apply applyNode_eq_of_not_mem_outs (g := pm_goal_21) (s := s1) (n := pm21_n70) (tid := 57)
    simp
  have h57 : (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) 57 = s1 57 := by
    have h := applyNode_eq_of_not_mem_outs (g := pm_goal_21)
      (s := applyNode pm_goal_21 s1 pm21_n70) (n := pm21_n71) (tid := 57)
      (by simp)
    rw [h, h57a]
  have hs1_25 : s1 25 = initPM 25 := pm21_pre1_tid25 initPM
  have hs1_57 : s1 57 =
      chunkPrim pm_goal_21.numRanks 3
        (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37]) :=
    pm21_pre1_tid57 initPM
  calc
    (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 73
      = (denoteGraph { pm_goal_21 with nodes := pm21_pre2 } s1) 73 := by
        simp only [hsplit]
    _ = (applyNode pm_goal_21
          (applyNode pm_goal_21
            (applyNode pm_goal_21 (applyNode pm_goal_21 s1 pm21_n70) pm21_n71) pm21_n72)
          pm21_n73) 73 := by
            rw [hpre2]
    _ = bw_sum (initPM 25)
          (chunkPrim pm_goal_21.numRanks 3
            (allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37])) := by
            simp only [h73, h25, h57, hs1_25, hs1_57]

lemma sm21_tid24 (initSM : Store) :
    (denoteGraph sm_goal_21 initSM) 24 = bw_sum (initSM 25) (initSM 17) := by
  simp [sm_goal_21, denoteGraph, List.foldl, applyNode, evalOp, storeSet,
    storeSet_eq_of_not_mem_fst]

lemma sm21_tid21 (initSM : Store) :
    (denoteGraph sm_goal_21 initSM) 21 =
      (bw_linear (denoteGraph sm_goal_21 initSM 24) (initSM 20) (initSM 16)).1 := by
  simp [sm_goal_21, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

set_option maxHeartbeats 800000 in
-- Large proof with many rewrite steps for tid24 equality between SM and PM graphs
theorem goal_21_tid24_eq
    (initSM initPM : Store)
    (hSmInit : StoreShapesHold initSM sm_goal_21InitEnv)
    (hPmInit : StoreShapesHold initPM pm_goal_21InitEnv)
    (hInitGoals : InitGoalsHold pm_goal_21.numRanks goal_21_cut_initGoals initSM initPM) :
    (denoteGraph sm_goal_21 initSM) 24 = (denoteGraph pm_goal_21 initPM) 24 := by
  -- initGoal_25 aligns scalar gradOut
  have hInit25 : InitGoalHolds pm_goal_21.numRanks initGoal_25 initSM initPM := by
    have : initGoal_25 ∈ goal_21_cut_initGoals := by
      simp [goal_21_cut_initGoals, initGoals]
    exact hInitGoals initGoal_25 this
  have h25eq : initSM 25 = initPM 25 := by
    simpa [initGoal_25, reconstruct] using hInit25.2.2
  -- SM: tid24 = bw_sum initSM25 initSM17 (bw_linear does not overwrite tid24)
  have hsm24 : (denoteGraph sm_goal_21 initSM) 24 = bw_sum (initSM 25) (initSM 17) := by
    simpa using (sm21_tid24 initSM)
  -- PM: split nodes into prefix (up to allGather) and suffix (bw_linear nodes)
  have hsplit := pm21_split initPM
  have hpm24 : (denoteGraph pm_goal_21 initPM) 24 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 24 := by
    have hpres := pm21_suffix_preserves_24 initPM
    simpa [hsplit] using hpres
  -- tid17 is also preserved by the suffix
  have hpm17 : (denoteGraph pm_goal_21 initPM) 17 =
      allReducePrim pm_goal_21.numRanks 0 [initPM 34, initPM 35, initPM 36, initPM 37] := by
    have hpres := pm21_suffix_preserves_17 initPM
    have hpm17' : (denoteGraph pm_goal_21 initPM) 17 =
        (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 17 := by
      simpa [hsplit] using hpres
    simpa [hpm17'] using pm21_prefix_tid17 initPM
  -- Shared chunk list for tid17
  let xs17 : List Tensor :=
    [ chunkPrim pm_goal_21.numRanks 0 (denoteGraph pm_goal_21 initPM 17),
      chunkPrim pm_goal_21.numRanks 1 (denoteGraph pm_goal_21 initPM 17),
      chunkPrim pm_goal_21.numRanks 2 (denoteGraph pm_goal_21 initPM 17),
      chunkPrim pm_goal_21.numRanks 3 (denoteGraph pm_goal_21 initPM 17) ]
  -- Evaluate tid24 for the prefix
  have hpm24_prefix : (denoteGraph pm_goal_21 initPM) 24 =
      allGatherPrim pm_goal_21.numRanks 0 (List.map (fun x => bw_sum (initPM 25) x) xs17) := by
    have hpm24' : (denoteGraph pm_goal_21 initPM) 24 =
        allGatherPrim pm_goal_21.numRanks 0
          [ (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 70,
            (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 71,
            (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 72,
            (denoteGraph { pm_goal_21 with nodes := pm21_prefix_pre } initPM) 73 ] := by
      have h := pm21_prefix_tid24 initPM
      simpa [hpm24] using h
    rw [hpm24', pm21_prefix_pre_tid70, pm21_prefix_pre_tid71,
      pm21_prefix_pre_tid72, pm21_prefix_pre_tid73]
    simp [xs17, List.map, hpm17]
  -- Shape of PM tid17
  have hshape34 : (initPM 34).shape = [128, 128] := by
    have henv : pm_goal_21InitEnv 34 = some [128, 128] := by
      simp [pm_goal_21InitEnv, pm_goal_21InitShapes, shapeEnvOfList]
    exact hPmInit 34 [128, 128] henv
  have hshape17_pm : ((denoteGraph pm_goal_21 initPM) 17).shape = [128, 128] := by
    have hhead : ([initPM 34, initPM 35, initPM 36, initPM 37].head?) = some (initPM 34) := by
      rfl
    have hshape_ar := allReducePrim_shape pm_goal_21.numRanks 0
      [initPM 34, initPM 35, initPM 36, initPM 37] (initPM 34) hhead
    simpa [hpm17, hshape34] using hshape_ar
  -- Use allGatherPrim_bw_sum_eq_bw_sum_allGather
  have hpm24'' : (denoteGraph pm_goal_21 initPM) 24 =
      bw_sum (initPM 25)
        (allGatherPrim pm_goal_21.numRanks 0 xs17) := by
    have hparts : 0 < pm_goal_21.numRanks := pm_goal_21_numRanks_pos
    have hhead :
        (xs17.head?.map (fun t => t.shape)).getD [] = [128, 32] := by
      have hchunk : (chunkPrim pm_goal_21.numRanks 0 (denoteGraph pm_goal_21 initPM 17)).shape = [128, 32] :=
        pm_goal_21_chunkPrim_shape _ 0 hshape17_pm
      simp [xs17, hchunk]
    have hxs_shape : ∀ x ∈ xs17, x.shape = [128, 32] := by
      intro x hx
      simp [xs17] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        exact pm_goal_21_chunkPrim_shape _ _ hshape17_pm
    have hlen : xs17.length = pm_goal_21.numRanks := by
      simp only [xs17, List.length_cons, List.length_nil, pm_goal_21_numRanks_eq]
    have hshard : 0 < 32 := by decide
    have hlemma := allGatherPrim_bw_sum_eq_bw_sum_allGather
      (numParts := pm_goal_21.numRanks) (o := 128) (shard := 32)
      (g := initPM 25)
      (xs := xs17)
      (hhead := hhead) (hxs_shape := hxs_shape) (hlen := hlen) (hparts := hparts) (hshard := hshard)
    -- chain using hpm24_prefix
    calc
      (denoteGraph pm_goal_21 initPM) 24
          = allGatherPrim pm_goal_21.numRanks 0 (List.map (fun x => bw_sum (initPM 25) x) xs17) := by
                  simpa using hpm24_prefix
      _ = bw_sum (initPM 25) (allGatherPrim pm_goal_21.numRanks 0 xs17) := by
                  simpa [List.map] using hlemma
  -- bw_sum ignores its second argument; conclude by ext
  rw [hsm24, hpm24'']
  have hshape24 : (bw_sum (initSM 25) (initSM 17)).shape = [128, 128] := by
    have henv : sm_goal_21InitEnv 17 = some [128, 128] := by
      simp [sm_goal_21InitEnv, sm_goal_21InitShapes, shapeEnvOfList]
    have hshape17 : (initSM 17).shape = [128, 128] := hSmInit 17 [128, 128] henv
    simp [hshape17]
  have hshape24' : (bw_sum (initPM 25) (allGatherPrim pm_goal_21.numRanks 0 xs17)).shape = [128, 128] := by
    -- bw_sum preserves shape
    have hhead :
        (xs17.head?.map (fun t => t.shape)).getD [] = [128, 32] := by
      have hchunk : (chunkPrim pm_goal_21.numRanks 0 (denoteGraph pm_goal_21 initPM 17)).shape = [128, 32] :=
        pm_goal_21_chunkPrim_shape _ 0 hshape17_pm
      simp [xs17, hchunk]
    have hshape_ag : (allGatherPrim pm_goal_21.numRanks 0 xs17).shape = [128, 128] := by
      have h := allGatherPrim_shape pm_goal_21.numRanks 128 32 _ hhead
      rw [pm_goal_21_numRanks_eq] at h ⊢; exact h
    simp [bw_sum_shape, hshape_ag]
  have hshape_eq : (bw_sum (initSM 25) (initSM 17)).shape =
      (bw_sum (initPM 25) (allGatherPrim pm_goal_21.numRanks 0 xs17)).shape := by
    rw [hshape24, hshape24']
  apply Tensor.ext hshape_eq
  intro idx hidx
  have hidxL : idx < prodShape (initSM 17).shape := by
    have h1 : (bw_sum (initSM 25) (initSM 17)).shape = (initSM 17).shape := bw_sum_shape _ _
    rw [← h1]; exact hidx
  have hidxR : idx < prodShape (allGatherPrim pm_goal_21.numRanks 0 xs17).shape := by
    have h1 : (bw_sum (initPM 25) (allGatherPrim pm_goal_21.numRanks 0 xs17)).shape =
        (allGatherPrim pm_goal_21.numRanks 0 xs17).shape := bw_sum_shape _ _
    rw [← h1, ← hshape_eq]; exact hidx
  have hval_sm := bw_sum_valAt_of_lt (initSM 25) (initSM 17) idx hidxL
  have hval_pm := bw_sum_valAt_of_lt (initPM 25) (allGatherPrim pm_goal_21.numRanks 0 xs17) idx hidxR
  calc
    valAt (bw_sum (initSM 25) (initSM 17)) idx
        = valAt (initSM 25) 0 := hval_sm
    _ = valAt (initPM 25) 0 := by rw [h25eq]
    _ = valAt (bw_sum (initPM 25) (allGatherPrim pm_goal_21.numRanks 0 xs17)) idx := by
          symm; exact hval_pm

-- goal_21_proof will use goal_21_tid24_eq and a bw_linear shard/allGather lemma next.

set_option maxHeartbeats 800000 in
-- Large proof combining tid24_eq with bw_linear shard/allGather lemmas
theorem goal_21_proof : goal_21_stmt_cut := by
  -- Outline per file header.
  intro initSM initPM hSmInit hPmInit hInitGoals
  dsimp [goal_21_stmt_cut, CoarseLineageHoldsWithInit, goal_21]
  -- Init goals
  have hInit16 : InitGoalHolds pm_goal_21.numRanks initGoal_16 initSM initPM := by
    have : initGoal_16 ∈ goal_21_cut_initGoals := by
      simp [goal_21_cut_initGoals, initGoals]
    exact hInitGoals initGoal_16 this
  have hInit20 : InitGoalHolds pm_goal_21.numRanks initGoal_20 initSM initPM := by
    have : initGoal_20 ∈ goal_21_cut_initGoals := by
      simp [goal_21_cut_initGoals, initGoals]
    exact hInitGoals initGoal_20 this
  -- Reconstruct weights and inputs
  have hrec16 : initSM 16 = reconstruct pm_goal_21.numRanks 0
      [initPM 30, initPM 31, initPM 32, initPM 33] := by
    simpa [initGoal_16] using hInit16.2.2
  have hrec20 : initSM 20 = initPM 20 := by
    simpa [initGoal_20, reconstruct] using hInit20.2.2
  have hrec16' : initSM 16 = allGatherPrim pm_goal_21.numRanks 0
      [initPM 30, initPM 31, initPM 32, initPM 33] := by
    have hshape30 : (initPM 30).shape = [128, 32] := by
      have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
          [[128, 32], [128, 32], [128, 32], [128, 32]] := by
        simpa [initGoal_16] using hInit16.2.1
      simpa using congrArg List.head? hsh
    have hnon : (initPM 30).shape ≠ [1] := by
      intro h1; rw [hshape30] at h1; cases h1
    have hrec := reconstruct_cons_cons_nonscalar pm_goal_21.numRanks 0
      (initPM 30) (initPM 31) [initPM 32, initPM 33] hnon
    simpa [hrec] using hrec16
  -- tid24 equality
  have h24eq : (denoteGraph sm_goal_21 initSM) 24 = (denoteGraph pm_goal_21 initPM) 24 :=
    goal_21_tid24_eq initSM initPM hSmInit hPmInit hInitGoals
  -- SM tid21
  have hsm21 : (denoteGraph sm_goal_21 initSM) 21 =
      (bw_linear (denoteGraph sm_goal_21 initSM 24) (initSM 20) (initSM 16)).1 := by
    simpa using (sm21_tid21 initSM)
  -- PM tid26..29 and tid46..52 via prefix/suffix lemmas
  have hpmSplit := pm21_split initPM
  have hpm26 : (denoteGraph pm_goal_21 initPM) 26 = chunkPrim pm_goal_21.numRanks 0 (initPM 20) := by
    have hpres := pm21_suffix_preserves_26 initPM
    simpa [hpmSplit] using (by simpa using hpres.trans (pm21_prefix_tid26 initPM).symm)
  have hpm27 : (denoteGraph pm_goal_21 initPM) 27 = chunkPrim pm_goal_21.numRanks 1 (initPM 20) := by
    have hpres := pm21_suffix_preserves_27 initPM
    simpa [hpmSplit] using (by simpa using hpres.trans (pm21_prefix_tid27 initPM).symm)
  have hpm28 : (denoteGraph pm_goal_21 initPM) 28 = chunkPrim pm_goal_21.numRanks 2 (initPM 20) := by
    have hpres := pm21_suffix_preserves_28 initPM
    simpa [hpmSplit] using (by simpa using hpres.trans (pm21_prefix_tid28 initPM).symm)
  have hpm29 : (denoteGraph pm_goal_21 initPM) 29 = chunkPrim pm_goal_21.numRanks 3 (initPM 20) := by
    have hpres := pm21_suffix_preserves_29 initPM
    simpa [hpmSplit] using (by simpa using hpres.trans (pm21_prefix_tid29 initPM).symm)
  have hpm24 : (denoteGraph pm_goal_21 initPM) 24 =
      (denoteGraph { pm_goal_21 with nodes := pm21_prefix } initPM) 24 := by
    have hpres := pm21_suffix_preserves_24 initPM
    simpa [hpmSplit] using hpres
  have hpm46 : (denoteGraph pm_goal_21 initPM) 46 =
      (bw_linear (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 26) (initPM 30)).1 := by
    have h := pm21_suffix_tid46 initPM
    simpa [hpmSplit, hpm24, hpm26] using h
  have hpm48 : (denoteGraph pm_goal_21 initPM) 48 =
      (bw_linear (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 27) (initPM 31)).1 := by
    have h := pm21_suffix_tid48 initPM
    simpa [hpmSplit, hpm24, hpm27] using h
  have hpm50 : (denoteGraph pm_goal_21 initPM) 50 =
      (bw_linear (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 28) (initPM 32)).1 := by
    have h := pm21_suffix_tid50 initPM
    simpa [hpmSplit, hpm24, hpm28] using h
  have hpm52 : (denoteGraph pm_goal_21 initPM) 52 =
      (bw_linear (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 29) (initPM 33)).1 := by
    have h := pm21_suffix_tid52 initPM
    simpa [hpmSplit, hpm24, hpm29] using h

  -- Shapes
  refine And.intro ?shapeSM ?rest
  · -- SM tid21 shape
    have hshape20 : (initSM 20).shape = [128, 128] := by
      simpa [initGoal_20] using hInit20.1
    have hshape16 : (initSM 16).shape = [128, 128] := by
      simpa [initGoal_16] using hInit16.1
    have hshape24 : (denoteGraph sm_goal_21 initSM 24).shape = [128, 128] := by
      -- tid24 is bw_sum (initSM 25) (initSM 17)
      have henv : sm_goal_21InitEnv 17 = some [128, 128] := by
        simp [sm_goal_21InitEnv, sm_goal_21InitShapes, shapeEnvOfList]
      have hshape17 : (initSM 17).shape = [128, 128] := hSmInit 17 [128, 128] henv
      have hsm24 : (denoteGraph sm_goal_21 initSM) 24 = bw_sum (initSM 25) (initSM 17) := by
        simp [sm_goal_21, denoteGraph, List.foldl, applyNode, evalOp, storeSet,
          storeSet_eq_of_not_mem_fst]
      simp [hsm24, bw_sum_shape, hshape17]
    have hshape := bw_linear_fst_shape 128 128 128
      (denoteGraph sm_goal_21 initSM 24) (initSM 20) (initSM 16)
      (by simp [hshape24]) (by simp [hshape20]) (by simp [hshape16])
    simpa [hsm21] using hshape
  · refine And.intro ?shapePM ?eqval
    · -- PM tps shapes
      have hshape24pm : (denoteGraph pm_goal_21 initPM 24).shape = [128, 128] := by
        -- via SM tid24 shape
        have henv : sm_goal_21InitEnv 17 = some [128, 128] := by
          simp [sm_goal_21InitEnv, sm_goal_21InitShapes, shapeEnvOfList]
        have hshape17 : (initSM 17).shape = [128, 128] := hSmInit 17 [128, 128] henv
        have hsm24 : (denoteGraph sm_goal_21 initSM) 24 = bw_sum (initSM 25) (initSM 17) := by
          simpa using (sm21_tid24 initSM)
        have hshape24sm : (denoteGraph sm_goal_21 initSM 24).shape = [128, 128] := by
          simp [hsm24, bw_sum_shape, hshape17]
        simpa [h24eq] using hshape24sm
      have hx20 : (initPM 20).shape = [128, 128] := by
        have henv : pm_goal_21InitEnv 20 = some [128, 128] := by
          simp [pm_goal_21InitEnv, pm_goal_21InitShapes, shapeEnvOfList]
        exact hPmInit 20 [128, 128] henv
      have hshape26 : (denoteGraph pm_goal_21 initPM 26).shape = [128, 32] := by
        rw [hpm26]; exact pm_goal_21_chunkPrim_shape _ 0 hx20
      have hshape27 : (denoteGraph pm_goal_21 initPM 27).shape = [128, 32] := by
        rw [hpm27]; exact pm_goal_21_chunkPrim_shape _ 1 hx20
      have hshape28 : (denoteGraph pm_goal_21 initPM 28).shape = [128, 32] := by
        rw [hpm28]; exact pm_goal_21_chunkPrim_shape _ 2 hx20
      have hshape29 : (denoteGraph pm_goal_21 initPM 29).shape = [128, 32] := by
        rw [hpm29]; exact pm_goal_21_chunkPrim_shape _ 3 hx20
      have hshape30 : (initPM 30).shape = [128, 32] := by
        have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
            [[128, 32], [128, 32], [128, 32], [128, 32]] := by
          simpa [initGoal_16] using hInit16.2.1
        simpa using congrArg List.head? hsh
      have hshape31 : (initPM 31).shape = [128, 32] := by
        have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
            [[128, 32], [128, 32], [128, 32], [128, 32]] := by
          simpa [initGoal_16] using hInit16.2.1
        have hsh' := (List.cons.inj (List.cons.inj hsh).2).1
        simpa using hsh'
      have hshape32 : (initPM 32).shape = [128, 32] := by
        have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
            [[128, 32], [128, 32], [128, 32], [128, 32]] := by
          simpa [initGoal_16] using hInit16.2.1
        have hsh' := (List.cons.inj (List.cons.inj (List.cons.inj hsh).2).2).1
        simpa using hsh'
      have hshape33 : (initPM 33).shape = [128, 32] := by
        have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
            [[128, 32], [128, 32], [128, 32], [128, 32]] := by
          simpa [initGoal_16] using hInit16.2.1
        have hsh' := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj hsh).2).2).2).1
        simpa using hsh'
      have h46 : (denoteGraph pm_goal_21 initPM 46).shape = [128, 32] := by
        have h := bw_linear_fst_shape 128 32 128
          (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 26) (initPM 30)
          (by simpa [hshape24pm]) (by simpa [hshape26]) (by simpa [hshape30])
        simpa [hpm46] using h
      have h48 : (denoteGraph pm_goal_21 initPM 48).shape = [128, 32] := by
        have h := bw_linear_fst_shape 128 32 128
          (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 27) (initPM 31)
          (by simpa [hshape24pm]) (by simpa [hshape27]) (by simpa [hshape31])
        simpa [hpm48] using h
      have h50 : (denoteGraph pm_goal_21 initPM 50).shape = [128, 32] := by
        have h := bw_linear_fst_shape 128 32 128
          (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 28) (initPM 32)
          (by simpa [hshape24pm]) (by simpa [hshape28]) (by simpa [hshape32])
        simpa [hpm50] using h
      have h52 : (denoteGraph pm_goal_21 initPM 52).shape = [128, 32] := by
        have h := bw_linear_fst_shape 128 32 128
          (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 29) (initPM 33)
          (by simpa [hshape24pm]) (by simpa [hshape29]) (by simpa [hshape33])
        simpa [hpm52] using h
      simp [h46, h48, h50, h52]
    · -- value equality
      -- tid 46 shape
      have hshape24pm : (denoteGraph pm_goal_21 initPM 24).shape = [128, 128] := by
        have henv : sm_goal_21InitEnv 17 = some [128, 128] := by
          simp [sm_goal_21InitEnv, sm_goal_21InitShapes, shapeEnvOfList]
        have hshape17 : (initSM 17).shape = [128, 128] := hSmInit 17 [128, 128] henv
        have hsm24 : (denoteGraph sm_goal_21 initSM) 24 = bw_sum (initSM 25) (initSM 17) := by
          simpa using (sm21_tid24 initSM)
        have hshape24sm : (denoteGraph sm_goal_21 initSM 24).shape = [128, 128] := by
          simp [hsm24, bw_sum_shape, hshape17]
        simpa [h24eq] using hshape24sm
      have hshape30 : (initPM 30).shape = [128, 32] := by
        have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
            [[128, 32], [128, 32], [128, 32], [128, 32]] := by
          simpa [initGoal_16] using hInit16.2.1
        simpa using congrArg List.head? hsh
      have hshape26v : (denoteGraph pm_goal_21 initPM 26).shape = [128, 32] := by
        have hx20v : (initPM 20).shape = [128, 128] := by
          have henv : pm_goal_21InitEnv 20 = some [128, 128] := by
            simp [pm_goal_21InitEnv, pm_goal_21InitShapes, shapeEnvOfList]
          exact hPmInit 20 [128, 128] henv
        rw [hpm26]; exact pm_goal_21_chunkPrim_shape _ 0 hx20v
      have hshape46 : (denoteGraph pm_goal_21 initPM 46).shape = [128, 32] := by
        have hbl := bw_linear_fst_shape 128 32 128
          (denoteGraph pm_goal_21 initPM 24) (denoteGraph pm_goal_21 initPM 26) (initPM 30)
          (by simpa [hshape24pm]) (by simpa [hshape26v]) (by simpa [hshape30])
        simpa [hpm46] using hbl
      -- reconstruct is allGather (non-scalar)
      have hnon46 : (denoteGraph pm_goal_21 initPM 46).shape ≠ [1] := by
        intro h1; rw [hshape46] at h1; cases h1
      have hrec21 : reconstruct pm_goal_21.numRanks 0
          [denoteGraph pm_goal_21 initPM 46,
           denoteGraph pm_goal_21 initPM 48,
           denoteGraph pm_goal_21 initPM 50,
           denoteGraph pm_goal_21 initPM 52] =
          allGatherPrim pm_goal_21.numRanks 0
          [denoteGraph pm_goal_21 initPM 46,
           denoteGraph pm_goal_21 initPM 48,
           denoteGraph pm_goal_21 initPM 50,
           denoteGraph pm_goal_21 initPM 52] := by
        exact reconstruct_cons_cons_nonscalar _ _ _ _ _ hnon46
      -- apply bw_linear allGather lemma
      have hws_len : ([initPM 30, initPM 31, initPM 32, initPM 33] : List Tensor).length = pm_goal_21.numRanks := by
        simp [pm_goal_21]
      have hws_shapes : ∀ w ∈ ([initPM 30, initPM 31, initPM 32, initPM 33] : List Tensor), w.shape = [128, 32] := by
        intro w hw
        have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
            [[128, 32], [128, 32], [128, 32], [128, 32]] := by
          simpa [initGoal_16] using hInit16.2.1
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · simp at hsh; exact hsh.1
        · simp at hsh; exact hsh.2.1
        · simp at hsh; exact hsh.2.2.1
        · simp at hsh; exact hsh.2.2.2
      have hparts : 0 < pm_goal_21.numRanks := pm_goal_21_numRanks_pos
      have hshard : 0 < 32 := by decide
      have hbw := bw_linear_fst_allGather_eq_allGather_bw_linear_chunk
        (numParts := pm_goal_21.numRanks) (b := 128) (i := 128) (o := 128) (shard := 32)
        (g := denoteGraph pm_goal_21 initPM 24) (x := initPM 20)
        (ws := [initPM 30, initPM 31, initPM 32, initPM 33])
        (hg := by
          -- pm tid24 shape from sm tid24
          have henv : sm_goal_21InitEnv 17 = some [128, 128] := by
            simp [sm_goal_21InitEnv, sm_goal_21InitShapes, shapeEnvOfList]
          have hshape17 : (initSM 17).shape = [128, 128] := hSmInit 17 [128, 128] henv
          have hsm24 : (denoteGraph sm_goal_21 initSM) 24 = bw_sum (initSM 25) (initSM 17) := by
            simpa using (sm21_tid24 initSM)
          have hshape24sm : (denoteGraph sm_goal_21 initSM 24).shape = [128, 128] := by
            simpa [hsm24, bw_sum_shape, hshape17]
          simpa [h24eq] using hshape24sm)
        (hx := by
          have henv : pm_goal_21InitEnv 20 = some [128, 128] := by
            simp [pm_goal_21InitEnv, pm_goal_21InitShapes, shapeEnvOfList]
          exact hPmInit 20 [128, 128] henv)
        (hi := pm_goal_21_128_eq_4_times_32)
        (hws_len := hws_len)
        (hws_shapes := hws_shapes)
        (hparts := hparts)
        (hshard := hshard)
      -- rewrite SM and PM, then conclude
      have hsm21' : (denoteGraph sm_goal_21 initSM) 21 =
          (bw_linear (denoteGraph pm_goal_21 initPM 24) (initPM 20)
            (allGatherPrim pm_goal_21.numRanks 0 [initPM 30, initPM 31, initPM 32, initPM 33])).1 := by
        simpa [hsm21, h24eq, hrec20, hrec16']
      -- Prove the two lists are equal by showing each element is equal
      have hpm21' :
          [denoteGraph pm_goal_21 initPM 46,
           denoteGraph pm_goal_21 initPM 48,
           denoteGraph pm_goal_21 initPM 50,
           denoteGraph pm_goal_21 initPM 52] =
          (List.ofFn (fun r : Fin pm_goal_21.numRanks =>
              (bw_linear (denoteGraph pm_goal_21 initPM 24)
                (chunkPrim pm_goal_21.numRanks r.val (initPM 20))
                ([initPM 30, initPM 31, initPM 32, initPM 33].get ⟨r.val, by simp only [List.length_cons, List.length_nil, pm_goal_21_numRanks_eq]; exact r.isLt⟩)).1)) := by
        -- expand List.ofFn directly
        have h0 : (denoteGraph pm_goal_21 initPM 46) =
            (bw_linear (denoteGraph pm_goal_21 initPM 24)
              (chunkPrim pm_goal_21.numRanks 0 (initPM 20))
              (initPM 30)).1 := by rw [hpm46, hpm26]
        have h1 : (denoteGraph pm_goal_21 initPM 48) =
            (bw_linear (denoteGraph pm_goal_21 initPM 24)
              (chunkPrim pm_goal_21.numRanks 1 (initPM 20))
              (initPM 31)).1 := by rw [hpm48, hpm27]
        have h2 : (denoteGraph pm_goal_21 initPM 50) =
            (bw_linear (denoteGraph pm_goal_21 initPM 24)
              (chunkPrim pm_goal_21.numRanks 2 (initPM 20))
              (initPM 32)).1 := by rw [hpm50, hpm28]
        have h3 : (denoteGraph pm_goal_21 initPM 52) =
            (bw_linear (denoteGraph pm_goal_21 initPM 24)
              (chunkPrim pm_goal_21.numRanks 3 (initPM 20))
              (initPM 33)).1 := by rw [hpm52, hpm29]
        rw [h0, h1, h2, h3]
        rfl
      -- finish: chain equalities without calc to avoid elaboration overhead
      have step1 : (denoteGraph sm_goal_21 initSM) 21 =
          (bw_linear (denoteGraph pm_goal_21 initPM 24) (initPM 20)
            (allGatherPrim pm_goal_21.numRanks 0 [initPM 30, initPM 31, initPM 32, initPM 33])).1 := hsm21'
      have step2 : (bw_linear (denoteGraph pm_goal_21 initPM 24) (initPM 20)
            (allGatherPrim pm_goal_21.numRanks 0 [initPM 30, initPM 31, initPM 32, initPM 33])).1 =
          allGatherPrim pm_goal_21.numRanks 0
            [denoteGraph pm_goal_21 initPM 46,
             denoteGraph pm_goal_21 initPM 48,
             denoteGraph pm_goal_21 initPM 50,
             denoteGraph pm_goal_21 initPM 52] := by
        rw [hbw, ← hpm21']
      have step3 : allGatherPrim pm_goal_21.numRanks 0
            [denoteGraph pm_goal_21 initPM 46,
             denoteGraph pm_goal_21 initPM 48,
             denoteGraph pm_goal_21 initPM 50,
             denoteGraph pm_goal_21 initPM 52] =
          reconstruct pm_goal_21.numRanks 0
            [denoteGraph pm_goal_21 initPM 46,
             denoteGraph pm_goal_21 initPM 48,
             denoteGraph pm_goal_21 initPM 50,
             denoteGraph pm_goal_21 initPM 52] := hrec21.symm
      exact step1.trans (step2.trans step3)

end TrainVerify.Denote.ManualProofs
