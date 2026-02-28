/- Common shared lemmas factored out of Goal_15/21/23 proofs.

Part 1: initGoal extraction (shape / reconstruction proofs).
Part 2: BW_linear suffix and ChunkPrim prefix infrastructure
        shared by Goal_21_Proof and Goal_23_Proof.
-/
import denote.mlp.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.Common

set_option linter.flexible false
set_option linter.style.longLine false
-- set_option linter.unnecessarySimpa false
-- set_option linter.unnecessarySeqFocus false

-- Weight shard shapes as a single map equality (avoids repeating simpa)
lemma initGoal_16_shard_shapes_map (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (List.map (fun t => t.shape) [initPM 30, initPM 31, initPM 32, initPM 33]) =
      [[128, 32], [128, 32], [128, 32], [128, 32]] := by
  simpa [initGoal_16] using hInit16.2.1

-- Individual shard shape lemmas
lemma initGoal_16_shape_30 (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (initPM 30).shape = [128, 32] := by
  simpa using congrArg List.head? (initGoal_16_shard_shapes_map numParts initSM initPM hInit16)

lemma initGoal_16_shape_31 (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (initPM 31).shape = [128, 32] :=
  (List.cons.inj (List.cons.inj (initGoal_16_shard_shapes_map numParts initSM initPM hInit16)).2).1

lemma initGoal_16_shape_32 (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (initPM 32).shape = [128, 32] :=
  (List.cons.inj (List.cons.inj (List.cons.inj
    (initGoal_16_shard_shapes_map numParts initSM initPM hInit16)).2).2).1

lemma initGoal_16_shape_33 (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (initPM 33).shape = [128, 32] :=
  (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj
    (initGoal_16_shard_shapes_map numParts initSM initPM hInit16)).2).2).2).1

-- Non-scalar proof for initPM 30
lemma initGoal_16_non_scalar (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (initPM 30).shape ≠ [1] := by
  intro h; rw [initGoal_16_shape_30 numParts initSM initPM hInit16] at h; cases h

-- Universal quantifier over all 4 weight shards
lemma initGoal_16_ws_shapes (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    ∀ w ∈ ([initPM 30, initPM 31, initPM 32, initPM 33] : List Tensor),
      w.shape = [128, 32] := by
  have h30 := initGoal_16_shape_30 numParts initSM initPM hInit16
  have h31 := initGoal_16_shape_31 numParts initSM initPM hInit16
  have h32 := initGoal_16_shape_32 numParts initSM initPM hInit16
  have h33 := initGoal_16_shape_33 numParts initSM initPM hInit16
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> assumption

-- Reconstruct equality from initGoal_16
lemma initGoal_16_rec (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    initSM 16 = reconstruct numParts 0
      [initPM 30, initPM 31, initPM 32, initPM 33] := by
  simpa [initGoal_16] using hInit16.2.2

-- One-step reconstruct → allGatherPrim conversion
lemma initGoal_16_rec_allGather (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    initSM 16 = allGatherPrim numParts 0
      [initPM 30, initPM 31, initPM 32, initPM 33] := by
  have hnon := initGoal_16_non_scalar numParts initSM initPM hInit16
  have hrec := reconstruct_cons_cons_nonscalar numParts 0
    (initPM 30) (initPM 31) [initPM 32, initPM 33] hnon
  simpa [hrec] using initGoal_16_rec numParts initSM initPM hInit16

-- SM shape from initGoal_16
lemma initGoal_16_sm_shape (numParts : Nat) (initSM initPM : Store)
    (hInit16 : InitGoalHolds numParts initGoal_16 initSM initPM) :
    (initSM 16).shape = [128, 128] := by
  simpa [initGoal_16] using hInit16.1

-- Generic singleton reconstruct: if a LineageGoal has a single shard with the same tid,
-- then SM and PM stores agree at that tid.
lemma initGoalHolds_singleton_eq (numParts : Nat) (initSM initPM : Store)
    (goal : LineageGoal)
    (hgoal : InitGoalHolds numParts goal initSM initPM)
    (htps : goal.tps = [{ rank := 0, tid := goal.ts }]) :
    initSM goal.ts = initPM goal.ts := by
  simpa [htps, reconstruct] using hgoal.2.2

-- Input tid 20 equality (singleton reconstruct → identity)
lemma initGoal_20_eq (numParts : Nat) (initSM initPM : Store)
    (hInit20 : InitGoalHolds numParts initGoal_20 initSM initPM) :
    initSM 20 = initPM 20 :=
  initGoalHolds_singleton_eq numParts initSM initPM initGoal_20 hInit20 rfl

-- SM shape from initGoal_20
lemma initGoal_20_sm_shape (numParts : Nat) (initSM initPM : Store)
    (hInit20 : InitGoalHolds numParts initGoal_20 initSM initPM) :
    (initSM 20).shape = [128, 128] := by
  simpa [initGoal_20] using hInit20.1

-- Scalar gradient tid 25 equality
lemma initGoal_25_eq (numParts : Nat) (initSM initPM : Store)
    (hInit25 : InitGoalHolds numParts initGoal_25 initSM initPM) :
    initSM 25 = initPM 25 :=
  initGoalHolds_singleton_eq numParts initSM initPM initGoal_25 hInit25 rfl

-- Intermediate tid 24 equality
lemma intermediateGoal_24_eq (numParts : Nat) (initSM initPM : Store)
    (hInit24 : InitGoalHolds numParts intermediateGoal_24 initSM initPM) :
    initSM 24 = initPM 24 :=
  initGoalHolds_singleton_eq numParts initSM initPM intermediateGoal_24 hInit24 rfl

/-!
## Shared node declarations

The BW_linear suffix and ChunkPrim prefix are identical in pm_goal_21 and pm_goal_23.
-/

-- ChunkPrim prefix: chunk tid 20 into tids 26..29
abbrev chunk_prefix : List NodeDecl :=
  [ { rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [26] },
    { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [27] },
    { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [28] },
    { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [29] } ]

-- BW_linear suffix: per-rank BW_linear on (tid24, chunk_r, weight_r)
abbrev bw_linear_suffix : List NodeDecl :=
  [ { rank := 0, op := "OpName.BW_linear", ins := [24, 26, 30], outs := [46, 47] },
    { rank := 1, op := "OpName.BW_linear", ins := [24, 27, 31], outs := [48, 49] },
    { rank := 2, op := "OpName.BW_linear", ins := [24, 28, 32], outs := [50, 51] },
    { rank := 3, op := "OpName.BW_linear", ins := [24, 29, 33], outs := [52, 53] } ]

/-!
## BW_linear suffix preservation lemmas

The suffix only writes tids 46..53, so all other tids are preserved.
-/

-- Generic: suffix preserves any tid not in its outputs
lemma bw_linear_suffix_preserves (g : GraphDecl) (s : Store) (tid : Tid)
    (h46 : tid ≠ 46) (h47 : tid ≠ 47) (h48 : tid ≠ 48) (h49 : tid ≠ 49)
    (h50 : tid ≠ 50) (h51 : tid ≠ 51) (h52 : tid ≠ 52) (h53 : tid ≠ 53) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) tid = s tid := by
  apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
    (nodes := bw_linear_suffix) (init := s) (tid := tid)
  intro n hn
  simp only [bw_linear_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] <;>
    exact ⟨‹_›, ‹_›⟩

-- Specific tid preservation lemmas (for convenience)
lemma bw_linear_suffix_preserves_17 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 17 = s 17 :=
  bw_linear_suffix_preserves g s 17
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_24 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 24 = s 24 :=
  bw_linear_suffix_preserves g s 24
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_26 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 26 = s 26 :=
  bw_linear_suffix_preserves g s 26
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_27 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 27 = s 27 :=
  bw_linear_suffix_preserves g s 27
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_28 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 28 = s 28 :=
  bw_linear_suffix_preserves g s 28
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_29 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 29 = s 29 :=
  bw_linear_suffix_preserves g s 29
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-!
## BW_linear suffix output lemmas

Show what tids 46..53 compute (dX = .1, dW = .2 of bw_linear).
-/

lemma bw_linear_suffix_tid46 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 46 =
      (bw_linear (s 24) (s 26) (s 30)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid47 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 47 =
      (bw_linear (s 24) (s 26) (s 30)).2 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid48 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 48 =
      (bw_linear (s 24) (s 27) (s 31)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid49 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 49 =
      (bw_linear (s 24) (s 27) (s 31)).2 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid50 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 50 =
      (bw_linear (s 24) (s 28) (s 32)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid51 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 51 =
      (bw_linear (s 24) (s 28) (s 32)).2 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid52 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 52 =
      (bw_linear (s 24) (s 29) (s 33)).1 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid53 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 53 =
      (bw_linear (s 24) (s 29) (s 33)).2 := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

/-!
## ChunkPrim prefix lemmas

The chunk prefix only writes tids 26..29 and preserves everything else.
-/

-- Chunk prefix preservation: preserves any tid not in {26,27,28,29}
lemma chunk_prefix_preserves (g : GraphDecl) (s : Store) (tid : Tid)
    (h26 : tid ≠ 26) (h27 : tid ≠ 27) (h28 : tid ≠ 28) (h29 : tid ≠ 29) :
    (denoteGraph { g with nodes := chunk_prefix } s) tid = s tid := by
  apply denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
    (nodes := chunk_prefix) (init := s) (tid := tid)
  intro n hn
  simp only [chunk_prefix, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
    assumption

-- Chunk prefix outputs
lemma chunk_prefix_tid26 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 26 =
      chunkPrim g.numRanks 0 (s 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma chunk_prefix_tid27 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 27 =
      chunkPrim g.numRanks 1 (s 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma chunk_prefix_tid28 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 28 =
      chunkPrim g.numRanks 2 (s 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma chunk_prefix_tid29 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 29 =
      chunkPrim g.numRanks 3 (s 20) := by
  simp [denoteGraph, List.foldl, applyNode, evalOp, storeSet]

-- Chunk prefix preserves specific tids needed by Goals 21/23
lemma chunk_prefix_preserves_24 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 24 = s 24 :=
  chunk_prefix_preserves g s 24 (by decide) (by decide) (by decide) (by decide)

lemma chunk_prefix_preserves_30 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 30 = s 30 :=
  chunk_prefix_preserves g s 30 (by decide) (by decide) (by decide) (by decide)

lemma chunk_prefix_preserves_31 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 31 = s 31 :=
  chunk_prefix_preserves g s 31 (by decide) (by decide) (by decide) (by decide)

lemma chunk_prefix_preserves_32 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 32 = s 32 :=
  chunk_prefix_preserves g s 32 (by decide) (by decide) (by decide) (by decide)

lemma chunk_prefix_preserves_33 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := chunk_prefix } s) 33 = s 33 :=
  chunk_prefix_preserves g s 33 (by decide) (by decide) (by decide) (by decide)

/-!
## numRanks=4 helper facts (shared by Goals 21/23)
-/

-- ChunkPrim shape when numRanks=4 and input is [128, 128]
lemma chunkPrim_shape_128_4 (numRanks : Nat) (t : Tensor) (r : Nat)
    (ht : t.shape = [128, 128]) (hn : numRanks = 4) :
    (chunkPrim numRanks r t).shape = [128, 32] := by
  subst hn
  exact chunkPrim_shape' 4 r 128 32 t ht (by decide)

lemma numRanks_4_128_eq_mul_32 (numRanks : Nat) (hn : numRanks = 4) :
    128 = numRanks * 32 := by omega

-- Generic positivity: any numRanks = 4 implies 0 < numRanks
/-!
## Reconstruct non-scalar for BW outputs

Both Goals 21 and 23 need to show that `reconstruct` on 4 non-scalar shards = `allGatherPrim`.
-/

lemma reconstruct_4_nonscalar (numRanks : Nat) (a b c d : Tensor)
    (hnon : a.shape ≠ [1]) :
    reconstruct numRanks 0 [a, b, c, d] = allGatherPrim numRanks 0 [a, b, c, d] :=
  reconstruct_cons_cons_nonscalar numRanks 0 a b [c, d] hnon

/-!
## Generic 4-rank ChunkPrim sequence

A common pattern: 4 ChunkPrim nodes chunking the same input tensor into 4 output tids,
one per rank. This covers both `chunk_prefix` (tid 20 → 26..29) and the chunk-of-tid-17
sequence in Goal 21 (tid 17 → 54..57).
-/

-- Generic 4-rank ChunkPrim node list
abbrev chunkPrim_4_nodes (in_tid o0 o1 o2 o3 : Tid) : List NodeDecl :=
  [ { rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
    { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
    { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] },
    { rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] } ]

-- Existing chunk_prefix is an instance of chunkPrim_4_nodes
lemma chunkPrim_4_nodes_output_0 (g : GraphDecl) (s : Store)
    (in_tid o0 o1 o2 o3 : Tid)
    (h01 : o0 ≠ o1) (h02 : o0 ≠ o2) (h03 : o0 ≠ o3) :
    (denoteGraph { g with nodes := chunkPrim_4_nodes in_tid o0 o1 o2 o3 } s) o0 =
      chunkPrim g.numRanks 0 (s in_tid) := by
  have hsplit := denoteGraph_nodes_append g
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] }]
    [{ rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
     { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] },
     { rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] }] s
  have hpres := denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
    (nodes := [{ rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
               { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] },
               { rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] }])
    (init := denoteGraph { g with nodes :=
      [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] }] } s)
    (tid := o0) (by
      intro n hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simp [h01, h02, h03])
  have hout : (denoteGraph { g with nodes :=
      [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] }] } s) o0 =
      chunkPrim g.numRanks 0 (s in_tid) := by
    simp only [denoteGraph_nodes_cons, denoteGraph_nodes_nil]
    exact applyNode_chunkPrim_out g s 0 in_tid o0
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit, hpres, hout]

-- Generic output lemma for rank 1
lemma chunkPrim_4_nodes_output_1 (g : GraphDecl) (s : Store)
    (in_tid o0 o1 o2 o3 : Tid)
    (h12 : o1 ≠ o2) (h13 : o1 ≠ o3) (hin0 : in_tid ≠ o0) :
    (denoteGraph { g with nodes := chunkPrim_4_nodes in_tid o0 o1 o2 o3 } s) o1 =
      chunkPrim g.numRanks 1 (s in_tid) := by
  have hsplit := denoteGraph_nodes_append g
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
     { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] }]
    [{ rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] },
     { rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] }] s
  have hpres := denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
    (nodes := [{ rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] },
               { rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] }])
    (init := denoteGraph { g with nodes :=
      [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
       { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] }] } s)
    (tid := o1) (by
      intro n hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl <;> simp [h12, h13])
  have hout : (denoteGraph { g with nodes :=
      [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
       { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] }] } s) o1 =
      chunkPrim g.numRanks 1 (s in_tid) := by
    simp only [denoteGraph_nodes_cons, denoteGraph_nodes_nil]
    rw [applyNode_chunkPrim_out g _ 1 in_tid o1]
    congr 1
    exact applyNode_eq_of_not_mem_outs g s _ in_tid (by simp [hin0])
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit, hpres, hout]

-- Generic output lemma for rank 2
lemma chunkPrim_4_nodes_output_2 (g : GraphDecl) (s : Store)
    (in_tid o0 o1 o2 o3 : Tid)
    (h23 : o2 ≠ o3) (hin0 : in_tid ≠ o0) (hin1 : in_tid ≠ o1) :
    (denoteGraph { g with nodes := chunkPrim_4_nodes in_tid o0 o1 o2 o3 } s) o2 =
      chunkPrim g.numRanks 2 (s in_tid) := by
  have hsplit := denoteGraph_nodes_append g
    [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
     { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
     { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] }]
    [{ rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] }] s
  have hpres := denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
    (nodes := [{ rank := 3, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o3] }])
    (init := denoteGraph { g with nodes :=
      [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
       { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
       { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] }] } s)
    (tid := o2) (by
      intro n hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl; simp [h23])
  have hout : (denoteGraph { g with nodes :=
      [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
       { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
       { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] }] } s) o2 =
      chunkPrim g.numRanks 2 (s in_tid) := by
    simp only [denoteGraph_nodes_cons, denoteGraph_nodes_nil]
    rw [applyNode_chunkPrim_out g _ 2 in_tid o2]
    congr 1
    exact denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
      (nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
                 { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] }])
      (init := s) (tid := in_tid) (by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl <;> simp [hin0, hin1])
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit, hpres, hout]

-- Generic output lemma for rank 3
lemma chunkPrim_4_nodes_output_3 (g : GraphDecl) (s : Store)
    (in_tid o0 o1 o2 o3 : Tid)
    (hin0 : in_tid ≠ o0) (hin1 : in_tid ≠ o1) (hin2 : in_tid ≠ o2) :
    (denoteGraph { g with nodes := chunkPrim_4_nodes in_tid o0 o1 o2 o3 } s) o3 =
      chunkPrim g.numRanks 3 (s in_tid) := by
  simp only [chunkPrim_4_nodes, denoteGraph_nodes_cons, denoteGraph_nodes_nil]
  rw [applyNode_chunkPrim_out g _ 3 in_tid o3]
  congr 1
  have hpres := denoteGraph_tid_eq_of_forall_not_mem_outs (g := g)
    (nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o0] },
               { rank := 1, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o1] },
               { rank := 2, op := "OpName.ChunkPrim", ins := [in_tid], outs := [o2] }])
    (init := s) (tid := in_tid) (by
      intro n hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simp [hin0, hin1, hin2])
  simp only [denoteGraph_nodes_cons, denoteGraph_nodes_nil] at hpres
  exact hpres

-- Combined output lemma: all 4 outputs at once
end TrainVerify.Denote.Common
