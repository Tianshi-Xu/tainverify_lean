/- Manual proof for Goal 23 (split file). -/
import denote.mlp.GeneratedData
import denote.mlp.Goal_23

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
## Goal 23

Outline:
- Unfold `goal_23_stmt_cut`.
- Use `goal_23_cut_initGoals` to obtain intermediate consistency for tid=24.
- Unfold `denoteGraph` for `sm_goal_23` and `pm_goal_23`.
- Use `BW_linear` lemma to show shard reconstruction equals SM output for tid=23.

Goal 23 proves that SM tid23 (dW from bw_linear) equals the reconstruction of PM tid47,49,51,53.
Key insight: dW = gradOut.T @ x, and since x is chunked, the dW outputs are also chunked.
-/

-- Precomputed facts about pm_goal_23
theorem pm_goal_23_numRanks_eq : pm_goal_23.numRanks = 4 := rfl
theorem pm_goal_23_numRanks_pos : 0 < pm_goal_23.numRanks := by decide
theorem pm_goal_23_128_eq_4_times_32 : 128 = pm_goal_23.numRanks * 32 := rfl

-- Helper lemma for chunkPrim shape calculations
theorem pm_goal_23_chunkPrim_shape (t : Tensor) (r : Nat) (ht : t.shape = [128, 128]) :
    (chunkPrim pm_goal_23.numRanks r t).shape = [128, 32] := by
  have hsh : t.shape = [128, pm_goal_23.numRanks * 32] := by
    rw [pm_goal_23_128_eq_4_times_32] at ht; exact ht
  exact chunkPrim_shape' pm_goal_23.numRanks r 128 32 t hsh pm_goal_23_numRanks_pos

-- Node abbreviations for pm_goal_23
abbrev pm23_n26 : NodeDecl := { rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [26] }
abbrev pm23_n27 : NodeDecl := { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [27] }
abbrev pm23_n28 : NodeDecl := { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [28] }
abbrev pm23_n29 : NodeDecl := { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [29] }

abbrev pm23_prefix : List NodeDecl := [pm23_n26, pm23_n27, pm23_n28, pm23_n29]

abbrev pm23_suffix : List NodeDecl :=
  [ { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] },
    { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] },
    { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] },
    { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ]

-- Structural lemma: split pm_goal_23 nodes
lemma pm23_split (initPM : Store) :
    denoteGraph pm_goal_23 initPM =
      denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) := by
  simpa [pm_goal_23, pm23_prefix, pm23_suffix] using
    (denoteGraph_nodes_append pm_goal_23 pm23_prefix pm23_suffix initPM)

-- Prefix preserves tid 24 (it's an input, not modified by ChunkPrim nodes)
lemma pm23_prefix_preserves_24 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 24 = initPM 24 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_23)
    (s := initPM) (tid := 24) (nodes := pm23_prefix)
  intro n hn
  simp only [pm23_prefix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [pm23_n26, pm23_n27, pm23_n28, pm23_n29]

-- Prefix computes tid26..29 as chunks of tid20
lemma pm23_prefix_tid26 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 26 =
      chunkPrim pm_goal_23.numRanks 0 (initPM 20) := by
  simp [pm23_prefix, pm23_n26, pm23_n27, pm23_n28, pm23_n29,
    denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm23_prefix_tid27 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 27 =
      chunkPrim pm_goal_23.numRanks 1 (initPM 20) := by
  simp [pm23_prefix, pm23_n26, pm23_n27, pm23_n28, pm23_n29,
    denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm23_prefix_tid28 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 28 =
      chunkPrim pm_goal_23.numRanks 2 (initPM 20) := by
  simp [pm23_prefix, pm23_n26, pm23_n27, pm23_n28, pm23_n29,
    denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm23_prefix_tid29 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 29 =
      chunkPrim pm_goal_23.numRanks 3 (initPM 20) := by
  simp [pm23_prefix, pm23_n26, pm23_n27, pm23_n28, pm23_n29,
    denoteGraph, List.foldl, applyNode, evalOp, storeSet]

-- Prefix preserves tid30..33 (weights, not modified)
lemma pm23_prefix_tid30 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 30 = initPM 30 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_23)
    (s := initPM) (tid := 30) (nodes := pm23_prefix)
  intro n hn
  simp only [pm23_prefix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [pm23_n26, pm23_n27, pm23_n28, pm23_n29]

lemma pm23_prefix_tid31 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 31 = initPM 31 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_23)
    (s := initPM) (tid := 31) (nodes := pm23_prefix)
  intro n hn
  simp only [pm23_prefix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [pm23_n26, pm23_n27, pm23_n28, pm23_n29]

lemma pm23_prefix_tid32 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 32 = initPM 32 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_23)
    (s := initPM) (tid := 32) (nodes := pm23_prefix)
  intro n hn
  simp only [pm23_prefix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [pm23_n26, pm23_n27, pm23_n28, pm23_n29]

lemma pm23_prefix_tid33 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 33 = initPM 33 := by
  apply foldl_applyNode_preserves_tid (g := pm_goal_23)
    (s := initPM) (tid := 33) (nodes := pm23_prefix)
  intro n hn
  simp only [pm23_prefix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [pm23_n26, pm23_n27, pm23_n28, pm23_n29]

-- Suffix computes tid47,49,51,53 (dW outputs from bw_linear)
lemma pm23_suffix_tid47 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 47 =
      (bw_linear
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 24)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 26)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 30)).2 := by
  simp [pm23_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm23_suffix_tid49 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 49 =
      (bw_linear
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 24)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 27)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 31)).2 := by
  simp [pm23_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm23_suffix_tid51 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 51 =
      (bw_linear
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 24)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 28)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 32)).2 := by
  simp [pm23_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma pm23_suffix_tid53 (initPM : Store) :
    (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 53 =
      (bw_linear
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 24)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 29)
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM 33)).2 := by
  simp [pm23_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

-- SM computes tid23 = (bw_linear tid24 tid20 tid16).2
lemma sm23_tid23 (initSM : Store) :
    (denoteGraph sm_goal_23 initSM) 23 = (bw_linear (initSM 24) (initSM 20) (initSM 16)).2 := by
  simp [sm_goal_23, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

set_option maxHeartbeats 400000 in
-- Main proof: goal_23_stmt_cut
theorem goal_23_proof : goal_23_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  dsimp [goal_23_stmt_cut, CoarseLineageHoldsWithInit, goal_23]
  -- Get initGoals
  have hInit16 : InitGoalHolds pm_goal_23.numRanks initGoal_16 initSM initPM := by
    have : initGoal_16 ∈ goal_23_cut_initGoals := by simp [goal_23_cut_initGoals, initGoals]
    exact hInitGoals initGoal_16 this
  have hInit20 : InitGoalHolds pm_goal_23.numRanks initGoal_20 initSM initPM := by
    have : initGoal_20 ∈ goal_23_cut_initGoals := by simp [goal_23_cut_initGoals, initGoals]
    exact hInitGoals initGoal_20 this
  -- intermediateGoal_24 provides tid24 equality
  have hInit24 : InitGoalHolds pm_goal_23.numRanks intermediateGoal_24 initSM initPM := by
    have : intermediateGoal_24 ∈ goal_23_cut_initGoals := by
      simp [goal_23_cut_initGoals, goal_23_prereqs]
    exact hInitGoals intermediateGoal_24 this
  -- Extract equalities from initGoals
  have hrec16 : initSM 16 = reconstruct pm_goal_23.numRanks 0
      [initPM 30, initPM 31, initPM 32, initPM 33] := by
    simpa [initGoal_16] using hInit16.2.2
  have hrec20 : initSM 20 = initPM 20 := by
    simpa [initGoal_20, reconstruct] using hInit20.2.2
  have h24eq : initSM 24 = initPM 24 := by
    simpa [intermediateGoal_24, reconstruct] using hInit24.2.2
  -- Shapes from initGoals
  have hshape30 : (initPM 30).shape = [128, 32] := by
    have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
        [[128, 32], [128, 32], [128, 32], [128, 32]] := by
      simpa [initGoal_16] using hInit16.2.1
    simp at hsh; exact hsh.1
  have hnon30 : (initPM 30).shape ≠ [1] := by intro h; rw [hshape30] at h; cases h
  have hrec16' : initSM 16 = allGatherPrim pm_goal_23.numRanks 0
      [initPM 30, initPM 31, initPM 32, initPM 33] := by
    have hrec := reconstruct_cons_cons_nonscalar pm_goal_23.numRanks 0
      (initPM 30) (initPM 31) [initPM 32, initPM 33] hnon30
    simpa [hrec] using hrec16
  -- SM tid23
  have hsm23 : (denoteGraph sm_goal_23 initSM) 23 = (bw_linear (initSM 24) (initSM 20) (initSM 16)).2 := by
    simpa using (sm23_tid23 initSM)
  -- PM structure
  have hpmSplit := pm23_split initPM
  -- PM tid26..29 via prefix
  have hpm26 : (denoteGraph pm_goal_23 initPM) 26 = chunkPrim pm_goal_23.numRanks 0 (initPM 20) := by
    have hpres : (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 26 =
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 26 := by
      apply foldl_applyNode_preserves_tid (g := pm_goal_23)
        (s := denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)
        (tid := 26) (nodes := pm23_suffix)
      intro n hn
      simp only [pm23_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp
    simpa [hpmSplit] using (by simpa using hpres.trans (pm23_prefix_tid26 initPM).symm)
  have hpm27 : (denoteGraph pm_goal_23 initPM) 27 = chunkPrim pm_goal_23.numRanks 1 (initPM 20) := by
    have hpres : (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 27 =
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 27 := by
      apply foldl_applyNode_preserves_tid (g := pm_goal_23)
        (s := denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)
        (tid := 27) (nodes := pm23_suffix)
      intro n hn
      simp only [pm23_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp
    simpa [hpmSplit] using (by simpa using hpres.trans (pm23_prefix_tid27 initPM).symm)
  have hpm28 : (denoteGraph pm_goal_23 initPM) 28 = chunkPrim pm_goal_23.numRanks 2 (initPM 20) := by
    have hpres : (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 28 =
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 28 := by
      apply foldl_applyNode_preserves_tid (g := pm_goal_23)
        (s := denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)
        (tid := 28) (nodes := pm23_suffix)
      intro n hn
      simp only [pm23_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp
    simpa [hpmSplit] using (by simpa using hpres.trans (pm23_prefix_tid28 initPM).symm)
  have hpm29 : (denoteGraph pm_goal_23 initPM) 29 = chunkPrim pm_goal_23.numRanks 3 (initPM 20) := by
    have hpres : (denoteGraph { pm_goal_23 with nodes := pm23_suffix }
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)) 29 =
        (denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM) 29 := by
      apply foldl_applyNode_preserves_tid (g := pm_goal_23)
        (s := denoteGraph { pm_goal_23 with nodes := pm23_prefix } initPM)
        (tid := 29) (nodes := pm23_suffix)
      intro n hn
      simp only [pm23_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp
    simpa [hpmSplit] using (by simpa using hpres.trans (pm23_prefix_tid29 initPM).symm)
  -- PM tid47,49,51,53 via suffix (dW outputs)
  have hpm47 : (denoteGraph pm_goal_23 initPM) 47 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 26) (initPM 30)).2 := by
    have h := pm23_suffix_tid47 initPM
    have h24 := pm23_prefix_preserves_24 initPM
    have h30 := pm23_prefix_tid30 initPM
    simpa [hpmSplit, h24, pm23_prefix_tid26, h30] using h
  have hpm49 : (denoteGraph pm_goal_23 initPM) 49 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 27) (initPM 31)).2 := by
    have h := pm23_suffix_tid49 initPM
    have h24 := pm23_prefix_preserves_24 initPM
    have h31 := pm23_prefix_tid31 initPM
    simpa [hpmSplit, h24, pm23_prefix_tid27, h31] using h
  have hpm51 : (denoteGraph pm_goal_23 initPM) 51 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 28) (initPM 32)).2 := by
    have h := pm23_suffix_tid51 initPM
    have h24 := pm23_prefix_preserves_24 initPM
    have h32 := pm23_prefix_tid32 initPM
    simpa [hpmSplit, h24, pm23_prefix_tid28, h32] using h
  have hpm53 : (denoteGraph pm_goal_23 initPM) 53 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 29) (initPM 33)).2 := by
    have h := pm23_suffix_tid53 initPM
    have h24 := pm23_prefix_preserves_24 initPM
    have h33 := pm23_prefix_tid33 initPM
    simpa [hpmSplit, h24, pm23_prefix_tid29, h33] using h
  -- Input shape info
  have hx20 : (initPM 20).shape = [128, 128] := by
    have henv : pm_goal_23InitEnv 20 = some [128, 128] := by
      simp [pm_goal_23InitEnv, pm_goal_23InitShapes, shapeEnvOfList]
    exact hPmInit 20 [128, 128] henv
  have h24shape : (initPM 24).shape = [128, 128] := by
    have henv : pm_goal_23InitEnv 24 = some [128, 128] := by
      simp [pm_goal_23InitEnv, pm_goal_23InitShapes, shapeEnvOfList]
    exact hPmInit 24 [128, 128] henv
  -- dW shape is [o, shard] = [128, 32] for each rank
  have hshape47 : (denoteGraph pm_goal_23 initPM 47).shape = [128, 32] := by
    rw [hpm47, hpm26]
    have hchunk := pm_goal_23_chunkPrim_shape (initPM 20) 0 hx20
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 0 (initPM 20)) (initPM 30) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, hchunk⟩ hshape30
  have hnon47 : (denoteGraph pm_goal_23 initPM 47).shape ≠ [1] := by
    intro h; rw [hshape47] at h; cases h
  -- reconstruct is allGather for non-scalar
  have hrec23 : reconstruct pm_goal_23.numRanks 0
      [denoteGraph pm_goal_23 initPM 47,
       denoteGraph pm_goal_23 initPM 49,
       denoteGraph pm_goal_23 initPM 51,
       denoteGraph pm_goal_23 initPM 53] =
      allGatherPrim pm_goal_23.numRanks 0
      [denoteGraph pm_goal_23 initPM 47,
       denoteGraph pm_goal_23 initPM 49,
       denoteGraph pm_goal_23 initPM 51,
       denoteGraph pm_goal_23 initPM 53] := by
    exact reconstruct_cons_cons_nonscalar _ _ _ _ _ hnon47
  -- The key equality: SM dW = allGather of PM dW shards
  -- SM: (bw_linear g x w).2 where w = allGather ws
  -- PM: allGather [(bw_linear g (chunk_i x) w_i).2 for each i]
  -- These are equal because dW = g.T @ x, and both compute the same matrix product
  -- For each output shard, the computation only depends on the corresponding input shard
  -- Additional shapes needed
  have hshape49 : (denoteGraph pm_goal_23 initPM 49).shape = [128, 32] := by
    rw [hpm49, hpm27]
    have hchunk := pm_goal_23_chunkPrim_shape (initPM 20) 1 hx20
    have hshape31 : (initPM 31).shape = [128, 32] := by
      have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
          [[128, 32], [128, 32], [128, 32], [128, 32]] := by
        simpa [initGoal_16] using hInit16.2.1
      simp at hsh; exact hsh.2.1
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 1 (initPM 20)) (initPM 31) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, hchunk⟩ hshape31
  have hshape51 : (denoteGraph pm_goal_23 initPM 51).shape = [128, 32] := by
    rw [hpm51, hpm28]
    have hchunk := pm_goal_23_chunkPrim_shape (initPM 20) 2 hx20
    have hshape32 : (initPM 32).shape = [128, 32] := by
      have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
          [[128, 32], [128, 32], [128, 32], [128, 32]] := by
        simpa [initGoal_16] using hInit16.2.1
      simp at hsh; exact hsh.2.2.1
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 2 (initPM 20)) (initPM 32) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, hchunk⟩ hshape32
  have hshape53 : (denoteGraph pm_goal_23 initPM 53).shape = [128, 32] := by
    rw [hpm53, hpm29]
    have hchunk := pm_goal_23_chunkPrim_shape (initPM 20) 3 hx20
    have hshape33 : (initPM 33).shape = [128, 32] := by
      have hsh : (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
          [[128, 32], [128, 32], [128, 32], [128, 32]] := by
        simpa [initGoal_16] using hInit16.2.1
      simp at hsh; exact hsh.2.2.2
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 3 (initPM 20)) (initPM 33) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, hchunk⟩ hshape33
  -- SM shape
  have hsm23_shape : (denoteGraph sm_goal_23 initSM 23).shape = [128, 128] := by
    rw [hsm23]
    have hsm16 : (initSM 16).shape = [128, 128] := by
      have henv : sm_goal_23InitEnv 16 = some [128, 128] := by
        simp [sm_goal_23InitEnv, sm_goal_23InitShapes, shapeEnvOfList]
      exact hSmInit 16 [128, 128] henv
    have hsm20 : (initSM 20).shape = [128, 128] := by
      have henv : sm_goal_23InitEnv 20 = some [128, 128] := by
        simp [sm_goal_23InitEnv, sm_goal_23InitShapes, shapeEnvOfList]
      exact hSmInit 20 [128, 128] henv
    have hsm24 : (initSM 24).shape = [128, 128] := by
      have henv : sm_goal_23InitEnv 24 = some [128, 128] := by
        simp [sm_goal_23InitEnv, sm_goal_23InitShapes, shapeEnvOfList]
      exact hSmInit 24 [128, 128] henv
    exact bw_linear_snd_shape 128 128 128 (initSM 24) (initSM 20) (initSM 16) hsm24 hsm20 hsm16
  refine ⟨hsm23_shape, ?shapes, ?values⟩
  case shapes =>
    simp only [hshape47, hshape49, hshape51, hshape53]
  case values =>
    -- Rewrite SM side
    rw [hsm23, h24eq, hrec20, hrec16']
    -- Rewrite PM side
    rw [hrec23]
    -- Now both sides involve bw_linear and allGatherPrim
    -- SM: (bw_linear (initPM 24) (initPM 20) (allGatherPrim _ _ [w0,w1,w2,w3])).2
    -- PM: allGatherPrim _ _ [(bw_linear (initPM 24) (chunk_0 (initPM 20)) w0).2, ...]
    -- These are equal by the bw_linear_snd_allGather lemma
    -- Since we don't have that lemma, we prove directly using ext and valAt
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
    -- Use the bw_linear_snd_allGather_eq lemma
    have hbw := bw_linear_snd_allGather_eq_allGather_bw_linear_chunk
      (numParts := pm_goal_23.numRanks) (b := 128) (i := 128) (o := 128) (shard := 32)
      (g := initPM 24) (x := initPM 20)
      (ws := [initPM 30, initPM 31, initPM 32, initPM 33])
      (hg := h24shape)
      (hx := hx20)
      (hi := pm_goal_23_128_eq_4_times_32)
      (hws_len := by simp [pm_goal_23_numRanks_eq])
      (hws_shapes := hws_shapes)
      (hparts := pm_goal_23_numRanks_pos)
      (hshard := by decide)
    -- Connect PM outputs to the RHS of hbw
    have hpm_list :
        [denoteGraph pm_goal_23 initPM 47,
         denoteGraph pm_goal_23 initPM 49,
         denoteGraph pm_goal_23 initPM 51,
         denoteGraph pm_goal_23 initPM 53] =
        (List.ofFn (fun r : Fin pm_goal_23.numRanks =>
          (bw_linear (initPM 24)
            (chunkPrim pm_goal_23.numRanks r.val (initPM 20))
            ([initPM 30, initPM 31, initPM 32, initPM 33].get ⟨r.val, by simp only [List.length_cons, List.length_nil, pm_goal_23_numRanks_eq]; exact r.isLt⟩)).2)) := by
      have h0 : (denoteGraph pm_goal_23 initPM 47) =
          (bw_linear (initPM 24) (chunkPrim pm_goal_23.numRanks 0 (initPM 20)) (initPM 30)).2 := by
        rw [hpm47, hpm26]
      have h1 : (denoteGraph pm_goal_23 initPM 49) =
          (bw_linear (initPM 24) (chunkPrim pm_goal_23.numRanks 1 (initPM 20)) (initPM 31)).2 := by
        rw [hpm49, hpm27]
      have h2 : (denoteGraph pm_goal_23 initPM 51) =
          (bw_linear (initPM 24) (chunkPrim pm_goal_23.numRanks 2 (initPM 20)) (initPM 32)).2 := by
        rw [hpm51, hpm28]
      have h3 : (denoteGraph pm_goal_23 initPM 53) =
          (bw_linear (initPM 24) (chunkPrim pm_goal_23.numRanks 3 (initPM 20)) (initPM 33)).2 := by
        rw [hpm53, hpm29]
      rw [h0, h1, h2, h3]
      rfl
    -- First rewrite PM side using hpm_list, then apply hbw
    rw [hpm_list, ← hbw]

end TrainVerify.Denote.ManualProofs
