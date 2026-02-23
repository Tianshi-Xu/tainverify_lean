/- Common shared lemmas factored out of Goal_15/21/23 proofs.

Part 1: initGoal extraction (shape / reconstruction proofs).
Part 2: BW_linear suffix and ChunkPrim prefix infrastructure
        shared by Goal_21_Proof and Goal_23_Proof.
-/
import denote.attn.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.Common

set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

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
    simp only [NodeDecl.mk.injEq, List.mem_cons, List.mem_nil_iff, or_false, not_or] <;>
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

lemma bw_linear_suffix_preserves_30 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 30 = s 30 :=
  bw_linear_suffix_preserves g s 30
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_31 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 31 = s 31 :=
  bw_linear_suffix_preserves g s 31
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_32 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 32 = s 32 :=
  bw_linear_suffix_preserves g s 32
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma bw_linear_suffix_preserves_33 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 33 = s 33 :=
  bw_linear_suffix_preserves g s 33
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-!
## BW_linear suffix output lemmas

Show what tids 46..53 compute (dX = .1, dW = .2 of bw_linear).
-/

lemma bw_linear_suffix_tid46 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 46 =
      (bw_linear (s 24) (s 26) (s 30)).1 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid47 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 47 =
      (bw_linear (s 24) (s 26) (s 30)).2 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid48 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 48 =
      (bw_linear (s 24) (s 27) (s 31)).1 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid49 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 49 =
      (bw_linear (s 24) (s 27) (s 31)).2 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid50 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 50 =
      (bw_linear (s 24) (s 28) (s 32)).1 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid51 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 51 =
      (bw_linear (s 24) (s 28) (s 32)).2 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid52 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 52 =
      (bw_linear (s 24) (s 29) (s 33)).1 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

lemma bw_linear_suffix_tid53 (g : GraphDecl) (s : Store) :
    (denoteGraph { g with nodes := bw_linear_suffix } s) 53 =
      (bw_linear (s 24) (s 29) (s 33)).2 := by
  simp [bw_linear_suffix, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

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
    simp only [NodeDecl.mk.injEq, List.mem_cons, List.mem_nil_iff, or_false, List.mem_singleton] <;>
    assumption

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

/-!
## Part 3: Generic initGoal extraction helpers

These lemmas factor out the repetitive pattern of extracting
shape equalities and reconstruction from `InitGoalHolds`.
-/

/-- Extract element equalities from a 4-element list equation. -/
theorem list_eq_4 {α : Type} {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : α}
    (h : [a₀, a₁, a₂, a₃] = [b₀, b₁, b₂, b₃]) :
    a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  simp only [List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Extract shape and value equality from a replicated (single-piece, same tid) InitGoal.

For initGoals like `initGoal_97 := { ts := 97, tps := [⟨0, 97⟩], ... }`,
this extracts both `(initSM tid).shape = sh` and `initSM tid = initPM tid`.
Pass concrete values for `tid` and `sh` so hypotheses have literal types. -/
theorem initGoalHolds_replicated (numParts : Nat) (goal : LineageGoal)
    (tid : Tid) (sh : Shape) (initSM initPM : Store)
    (h : InitGoalHolds numParts goal initSM initPM)
    (htid : goal.ts = tid) (htps : goal.tps = [⟨0, tid⟩])
    (hsh : goal.tsShape = sh) :
    (initSM tid).shape = sh ∧ initSM tid = initPM tid := by
  subst htid; subst hsh
  obtain ⟨hshape, _, hrec⟩ := h
  simp only [htps, List.map, Piece.tid, reconstructWithDim] at hrec
  exact ⟨hshape, hrec⟩

/-- Extract shapes and reconstruction from a 4-shard InitGoal.

For intermediateGoals like `{ ts := 159, tps := [⟨0,168⟩,⟨1,169⟩,⟨2,170⟩,⟨3,171⟩], ... }`,
this extracts the SM shape, all 4 shard shapes, and the reconstruction equation in one step.
Pass concrete values for `smTid`, `smShape`, shard tids and shape so hypotheses have literal types. -/
theorem initGoalHolds_sharded4 (numParts : Nat) (goal : LineageGoal)
    (smTid t0 t1 t2 t3 : Tid) (smShape shardShape : Shape)
    (initSM initPM : Store)
    (h : InitGoalHolds numParts goal initSM initPM)
    (htid : goal.ts = smTid) (hsh : goal.tsShape = smShape)
    (htps : goal.tps = [⟨0, t0⟩, ⟨1, t1⟩, ⟨2, t2⟩, ⟨3, t3⟩])
    (hshapes : goal.tpShapes = [shardShape, shardShape, shardShape, shardShape]) :
    (initSM smTid).shape = smShape ∧
    (initPM t0).shape = shardShape ∧
    (initPM t1).shape = shardShape ∧
    (initPM t2).shape = shardShape ∧
    (initPM t3).shape = shardShape ∧
    initSM smTid = reconstructWithDim goal.gatherDim numParts 0
      [initPM t0, initPM t1, initPM t2, initPM t3] := by
  subst htid; subst hsh
  obtain ⟨hshape, htpshapes, hrec⟩ := h
  simp only [htps, List.map, Piece.tid] at htpshapes hrec
  rw [hshapes] at htpshapes
  obtain ⟨h0, h1, h2, h3⟩ := list_eq_4 htpshapes
  exact ⟨hshape, h0, h1, h2, h3, hrec⟩

/-!
## Part 4: FW_linear + AllGatherPrimDim0 coarse lineage

This theorem handles the common pattern where:
- SM graph: single `FW_linear(x, w) → out`
- PM graph: 4× `FW_linear(shard_r, w) → out_r` then `AllGatherPrim → out`
- Weight `w` is replicated (same on SM and PM)
- Input `x` is dim-0 sharded into 4 pieces

Used by attn/Goal_2 (tid 98) and attn/Goal_3 (tid 100).
-/

set_option maxHeartbeats 400000 in
theorem fw_linear_allGatherDim0_coarse
    (numRanks b0 s i o : Nat)
    (smStore pmStore : Store) (outTid : Tid)
    (initSM initPM : Store) (xSmTid wTid xPm0 xPm1 xPm2 xPm3 : Tid)
    (hsm : smStore outTid = fw_linear (initSM xSmTid) (initSM wTid))
    (hpm : pmStore outTid = allGatherPrimDim0 numRanks 0
      [fw_linear (initPM xPm0) (initPM wTid),
       fw_linear (initPM xPm1) (initPM wTid),
       fw_linear (initPM xPm2) (initPM wTid),
       fw_linear (initPM xPm3) (initPM wTid)])
    (hx_rec : initSM xSmTid = reconstructWithDim 0 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3])
    (hweq : initSM wTid = initPM wTid)
    (hw_shape : (initSM wTid).shape = [o, i])
    (hxsm_shape : (initSM xSmTid).shape = [b0 * numRanks, s, i])
    (hxpm0_shape : (initPM xPm0).shape = [b0, s, i])
    (hxpm1_shape : (initPM xPm1).shape = [b0, s, i])
    (hxpm2_shape : (initPM xPm2).shape = [b0, s, i])
    (hxpm3_shape : (initPM xPm3).shape = [b0, s, i])
    (hlen : [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3].length = numRanks)
    (hb0 : 0 < b0) (hs : 0 < s) (hi : 0 < i) (ho : 0 < o) (hnr : 0 < numRanks) :
    (smStore outTid).shape = [b0 * numRanks, s, o] ∧
    [(pmStore outTid).shape] = [[b0 * numRanks, s, o]] ∧
    smStore outTid = reconstructWithDim 0 numRanks 0 [pmStore outTid] := by
  have hxpm_shape : ∀ x ∈ [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3],
      x.shape = [b0, s, i] := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h_dimN : initSM xSmTid = allGatherPrimDimN 0 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3] := by
    rw [hx_rec]; simp [reconstructWithDim, hxpm0_shape]
  have hw_pm : (initPM wTid).shape = [o, i] := by rw [← hweq]; exact hw_shape
  have hdistr : fw_linear (initSM xSmTid) (initSM wTid) =
      allGatherPrimDim0 numRanks 0
        [fw_linear (initPM xPm0) (initPM wTid),
         fw_linear (initPM xPm1) (initPM wTid),
         fw_linear (initPM xPm2) (initPM wTid),
         fw_linear (initPM xPm3) (initPM wTid)] := by
    conv_lhs => rw [h_dimN, hweq]
    have := fw_linear_3d_allGatherPrimDimN0_comm
      (numParts := numRanks) (b0 := b0) (s := s) (i := i) (o := o)
      (xs := [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3])
      (w := initPM wTid)
      (hw := hw_pm)
      (hxs_head := by simp [hxpm0_shape])
      (hxs_shape := hxpm_shape)
      (hxs_len := hlen)
      (hparts := hnr) (hb0 := hb0) (hs := hs) (hi := hi) (ho := ho)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]
    exact fw_linear_3d_shape (b0 * numRanks) s i o _ _ hxsm_shape hw_shape
  · rw [hpm]
    have hfw_head : (fw_linear (initPM xPm0) (initPM wTid)).shape = [b0, s, o] :=
      fw_linear_3d_shape b0 s i o _ _ hxpm0_shape hw_pm
    have hag := allGatherPrimDim0_shape_3d numRanks b0 s o
      [fw_linear (initPM xPm0) (initPM wTid),
       fw_linear (initPM xPm1) (initPM wTid),
       fw_linear (initPM xPm2) (initPM wTid),
       fw_linear (initPM xPm3) (initPM wTid)]
      (by simp only [List.head?, Option.map, Option.getD]; exact hfw_head)
    simp [hag]
  · rw [hsm, hdistr, ← hpm]
    simp [reconstructWithDim]

/-!
## Part 5: FW_linear + AllReducePrim coarse lineage (Column-parallel)

This handles the pattern where:
- SM graph: single `FW_linear(x, w) → out`
- PM graph: 4× `FW_linear(x_r, w_r) → out_r` then `AllReducePrim → out`
- Both input x and weight w are sharded along their last (inner/reduction) dimension
- The result is summed via AllReduce (column-parallel matmul)
-/

private theorem allGatherPrimDimN_1_valAt
    (numParts o shard : Nat) (pieces : List Tensor)
    (hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard)
    (p : Nat) (hp : p < o) (r : Nat) (hr : r < numParts)
    (j : Nat) (hj : j < shard) :
    valAt (allGatherPrimDimN 1 numParts 0 pieces)
        (p * (shard * numParts) + r * shard + j) =
      valAt (pieces.getD r (zeroTensor [o, shard])) (p * shard + j) := by
  have hfull_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hrem_lt : r * shard + j < shard * numParts := by
    calc r * shard + j
        < r * shard + shard := Nat.add_lt_add_left hj _
      _ = (r + 1) * shard := by ring
      _ ≤ numParts * shard := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr)
      _ = shard * numParts := Nat.mul_comm ..
  have hlt : p * (shard * numParts) + r * shard + j < o * (shard * numParts) := by
    calc p * (shard * numParts) + r * shard + j
        < p * (shard * numParts) + shard * numParts := by omega
      _ = (p + 1) * (shard * numParts) := by ring
      _ ≤ o * (shard * numParts) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hp)
  have hshape_out : (allGatherPrimDimN 1 numParts 0 pieces).shape =
      [o, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : p * (shard * numParts) + r * shard + j <
      prodShape (allGatherPrimDimN 1 numParts 0 pieces).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]; omega
  have hdiv : (p * (shard * numParts) + r * shard + j) / (shard * numParts) = p := by
    have heq : (r * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.1
  have hmod : (p * (shard * numParts) + r * shard + j) % (shard * numParts) =
      r * shard + j := by
    have heq : (r * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.2
  have hdivS : (r * shard + j) / shard = r := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.1
  have hmodS : (r * shard + j) % shard = j := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.2
  rw [valAt_of_lt _ _ hlt_prod]
  simp [allGatherPrimDimN, Tensor.mkShape, hhead,
    hshard.ne', hfull_pos.ne', (show (1 : Nat) ≠ 0 by omega),
    Nat.div_one, Nat.mod_one, Nat.add_zero, Nat.mul_one,
    hdiv, hmod, hdivS, hmodS]

private theorem allGatherPrimDimN_2_valAt
    (numParts b s shard : Nat) (pieces : List Tensor)
    (hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, s, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard)
    (batch : Nat) (hbatch : batch < b * s) (r : Nat) (hr : r < numParts)
    (j : Nat) (hj : j < shard) :
    valAt (allGatherPrimDimN 2 numParts 0 pieces)
        (batch * (shard * numParts) + r * shard + j) =
      valAt (pieces.getD r (zeroTensor [b, s, shard])) (batch * shard + j) := by
  have hfull_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hrem_lt : r * shard + j < shard * numParts := by
    calc r * shard + j
        < r * shard + shard := Nat.add_lt_add_left hj _
      _ = (r + 1) * shard := by ring
      _ ≤ numParts * shard := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr)
      _ = shard * numParts := Nat.mul_comm ..
  have hlt : batch * (shard * numParts) + r * shard + j <
      b * s * (shard * numParts) := by
    calc batch * (shard * numParts) + r * shard + j
        < batch * (shard * numParts) + shard * numParts := by omega
      _ = (batch + 1) * (shard * numParts) := by ring
      _ ≤ (b * s) * (shard * numParts) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hbatch)
  have hshape_out : (allGatherPrimDimN 2 numParts 0 pieces).shape =
      [b, s, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : batch * (shard * numParts) + r * shard + j <
      prodShape (allGatherPrimDimN 2 numParts 0 pieces).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]
    have : b * s * (shard * numParts) = 1 * b * s * (shard * numParts) := by ring
    omega
  have hdiv : (batch * (shard * numParts) + r * shard + j) /
      (shard * numParts) = batch := by
    have heq : (r * shard + j) + (shard * numParts) * batch =
        batch * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.1
  have hmod : (batch * (shard * numParts) + r * shard + j) %
      (shard * numParts) = r * shard + j := by
    have heq : (r * shard + j) + (shard * numParts) * batch =
        batch * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.2
  have hdivS : (r * shard + j) / shard = r := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.1
  have hmodS : (r * shard + j) % shard = j := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.2
  rw [valAt_of_lt _ _ hlt_prod]
  simp [allGatherPrimDimN, Tensor.mkShape, hhead,
    hshard.ne', hfull_pos.ne', (show (1 : Nat) ≠ 0 by omega),
    Nat.div_one, Nat.mod_one, Nat.add_zero, Nat.mul_one,
    hdiv, hmod, hdivS, hmodS]

set_option maxHeartbeats 1600000 in
theorem fw_linear_3d_column_parallel
    (numParts b s shard o : Nat)
    (xs : List Tensor) (ws : List Tensor)
    (hxs_shapes : ∀ x ∈ xs, x.shape = [b, s, shard])
    (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hxs_len : xs.length = numParts)
    (hws_len : ws.length = numParts)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, shard])
    (hws_head : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hparts : 0 < numParts) (hb : 0 < b) (hs : 0 < s)
    (hshard : 0 < shard) (ho : 0 < o) :
    fw_linear (allGatherPrimDimN 2 numParts 0 xs) (allGatherPrimDimN 1 numParts 0 ws) =
      allReducePrim numParts 0 (List.zipWith (fun x w => fw_linear x w) xs ws) := by
  have hsN_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hso_ne : s * o ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hs ho)
  have ho_ne : o ≠ 0 := Nat.ne_of_gt ho
  have hbs_pos : 0 < b * s := Nat.mul_pos hb hs
  -- Gathered tensor shapes
  have hgX_shape : (allGatherPrimDimN 2 numParts 0 xs).shape =
      [b, s, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hxs_head]
  have hgW_shape : (allGatherPrimDimN 1 numParts 0 ws).shape =
      [o, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hws_head]
  have hLHS_shape : (fw_linear (allGatherPrimDimN 2 numParts 0 xs)
      (allGatherPrimDimN 1 numParts 0 ws)).shape = [b, s, o] :=
    fw_linear_3d_shape b s (shard * numParts) o _ _ hgX_shape hgW_shape
  -- zipWith properties
  have hzw_len : (List.zipWith (fun x w => fw_linear x w) xs ws).length =
      numParts := by simp [List.length_zipWith, hxs_len, hws_len]
  have hzw_ne : List.zipWith (fun x w => fw_linear x w) xs ws ≠ [] := by
    intro h; simp [h] at hzw_len; omega
  have hzw_head_shape : ((List.zipWith (fun x w => fw_linear x w) xs ws).head?.map
      (fun t => t.shape)).getD [] = [b, s, o] := by
    rw [List.head?_eq_some_head hzw_ne]
    simp only [Option.map_some, Option.getD_some]
    match xs, ws, hxs_len, hws_len with
    | x0 :: _, w0 :: _, _, _ =>
      simp only [List.zipWith, List.head]
      exact fw_linear_3d_shape b s shard o x0 w0
        (hxs_shapes x0 (by simp)) (hws_shapes w0 (by simp))
  have hRHS_shape : (allReducePrim numParts 0
      (List.zipWith (fun x w => fw_linear x w) xs ws)).shape = [b, s, o] := by
    simp [allReducePrim, Tensor.mkShape, hzw_head_shape]
  -- Apply Tensor.ext
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx_bso : idx < b * s * o := by
    simp only [hLHS_shape, prodShape, List.foldl, Nat.one_mul] at hidx
    have : 1 * b * s * o = b * s * o := by ring
    omega
  have hcol_lt : idx % o < o := Nat.mod_lt _ ho
  have hbatch_lt : idx / o < b * s :=
    Nat.div_lt_iff_lt_mul ho |>.mpr hidx_bso
  -- LHS: resolve fw_linear match using known shapes
  conv_lhs => simp only [fw_linear, hgX_shape, hgW_shape]
  -- RHS: rewrite allReducePrim to Tensor.mkShape with known shape
  have allReduce_eq : allReducePrim numParts 0
      (List.zipWith (fun x w => fw_linear x w) xs ws) =
    Tensor.mkShape [b, s, o] (fun idx =>
      List.foldl (fun acc t => acc + valAt t idx) 0
        (List.zipWith (fun x w => fw_linear x w) xs ws)) := by
    unfold allReducePrim; rw [hzw_head_shape]
  rw [allReduce_eq]
  -- Unfold valAt on both sides (both are now Tensor.mkShape [b,s,o])
  have hprod : idx < prodShape [b, s, o] := by
    rw [hLHS_shape] at hidx; exact hidx
  rw [valAt_of_lt _ _ hprod, valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte]
  -- Normalize the batch index and column index
  have hrow : idx / (s * o) * s + idx % (s * o) / o = idx / o := by
    rw [show idx / (s * o) * s = idx / o / s * s from by
      rw [Nat.div_div_eq_div_mul]; ring_nf]
    rw [show s * o = o * s from Nat.mul_comm s o, Nat.mod_mul_right_div_self,
        Nat.mul_comm (idx / o / s) s, Nat.div_add_mod]
  have hcol : idx % (s * o) % o = idx % o :=
    Nat.mod_mod_of_dvd _ ⟨s, (Nat.mul_comm o s).symm⟩
  simp only [hrow, hcol]
  -- Convert RHS foldl to Finset.sum
  rw [List.foldl_add_eq_sum (f := fun t => valAt t idx)]
  -- Split LHS sum: range(N*shard) → ∑ r ∑ l
  conv_lhs =>
    rw [Nat.mul_comm shard numParts,
        Finset.sum_range_mul_eq_sum_sum (n := numParts) (m := shard)]
  -- Substitute allGatherPrimDimN valAt in LHS
  have hval_eq : ∀ r ∈ Finset.range numParts, ∀ l ∈ Finset.range shard,
      valAt (allGatherPrimDimN 2 numParts 0 xs)
        (idx / o * (shard * numParts) + (r * shard + l)) *
      valAt (allGatherPrimDimN 1 numParts 0 ws)
        (idx % o * (shard * numParts) + (r * shard + l)) =
      valAt (xs.getD r (zeroTensor [b, s, shard])) (idx / o * shard + l) *
      valAt (ws.getD r (zeroTensor [o, shard])) (idx % o * shard + l) := by
    intro r hr l hl
    have hr' := Finset.mem_range.mp hr
    have hl' := Finset.mem_range.mp hl
    have hassocX : idx / o * (shard * numParts) + (r * shard + l) =
        (idx / o) * (shard * numParts) + r * shard + l := by ring
    have hassocW : idx % o * (shard * numParts) + (r * shard + l) =
        (idx % o) * (shard * numParts) + r * shard + l := by ring
    rw [hassocX, hassocW,
        allGatherPrimDimN_2_valAt numParts b s shard xs hxs_head hparts hshard
          (idx / o) hbatch_lt r hr' l hl',
        allGatherPrimDimN_1_valAt numParts o shard ws hws_head hparts hshard
          (idx % o) hcol_lt r hr' l hl']
  conv_lhs =>
    arg 2; ext r
    arg 2; ext l
    rw [show r * shard + l = r * shard + l from rfl]
  -- Apply the valAt substitution
  have hlhs_rw :
    ∑ r ∈ Finset.range numParts, ∑ l ∈ Finset.range shard,
      valAt (allGatherPrimDimN 2 numParts 0 xs)
        (idx / o * (shard * numParts) + (r * shard + l)) *
      valAt (allGatherPrimDimN 1 numParts 0 ws)
        (idx % o * (shard * numParts) + (r * shard + l)) =
    ∑ r ∈ Finset.range numParts, ∑ l ∈ Finset.range shard,
      valAt (xs.getD r (zeroTensor [b, s, shard])) (idx / o * shard + l) *
      valAt (ws.getD r (zeroTensor [o, shard])) (idx % o * shard + l) := by
    exact Finset.sum_congr rfl fun r hr =>
      Finset.sum_congr rfl fun l hl => hval_eq r hr l hl
  simp only [show numParts * shard = shard * numParts from Nat.mul_comm numParts shard]
  rw [hlhs_rw]
  -- Convert LHS Finset.sum to List.sum via Fin.sum_ofFn
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_ofFn]
  -- Now both sides are List.sum; show the lists are equal
  congr 1
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_map, List.length_zipWith, hxs_len, hws_len, hzw_len]
  · intro n hn1 hn2
    simp only [List.length_ofFn] at hn1
    simp only [List.getElem_ofFn, List.getElem_map]
    have hn_xs : n < xs.length := by omega
    have hn_ws : n < ws.length := by omega
    simp only [List.getElem_zipWith]
    have hxn : xs[n].shape = [b, s, shard] := hxs_shapes _ (List.getElem_mem hn_xs)
    have hwn : ws[n].shape = [o, shard] := hws_shapes _ (List.getElem_mem hn_ws)
    conv_rhs => simp only [fw_linear, hxn, hwn]
    rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, prodShape, List.foldl]; exact hidx_bso)]
    simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte, hrow, hcol]
    apply Finset.sum_congr rfl; intro l _
    simp only [List.getD, List.getElem?_eq_getElem hn_xs, List.getElem?_eq_getElem hn_ws,
      Option.getD_some]

set_option maxHeartbeats 800000 in
theorem fw_linear_allReduce_coarse
    (numRanks b s shard o : Nat)
    (smStore pmStore : Store) (outTid : Tid)
    (initSM initPM : Store)
    (xSmTid wSmTid xPm0 xPm1 xPm2 xPm3 wPm0 wPm1 wPm2 wPm3 : Tid)
    (hsm : smStore outTid = fw_linear (initSM xSmTid) (initSM wSmTid))
    (hpm : pmStore outTid = allReducePrim numRanks 0
      [fw_linear (initPM xPm0) (initPM wPm0),
       fw_linear (initPM xPm1) (initPM wPm1),
       fw_linear (initPM xPm2) (initPM wPm2),
       fw_linear (initPM xPm3) (initPM wPm3)])
    (hx_rec : initSM xSmTid = reconstructWithDim 2 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3])
    (hw_rec : initSM wSmTid = reconstructWithDim 1 numRanks 0
      [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3])
    (hxsm_shape : (initSM xSmTid).shape = [b, s, shard * numRanks])
    (hwsm_shape : (initSM wSmTid).shape = [o, shard * numRanks])
    (hxpm0 : (initPM xPm0).shape = [b, s, shard])
    (hxpm1 : (initPM xPm1).shape = [b, s, shard])
    (hxpm2 : (initPM xPm2).shape = [b, s, shard])
    (hxpm3 : (initPM xPm3).shape = [b, s, shard])
    (hwpm0 : (initPM wPm0).shape = [o, shard])
    (hwpm1 : (initPM wPm1).shape = [o, shard])
    (hwpm2 : (initPM wPm2).shape = [o, shard])
    (hwpm3 : (initPM wPm3).shape = [o, shard])
    (hxlen : [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3].length = numRanks)
    (hwlen : [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3].length = numRanks)
    (hb : 0 < b) (hs : 0 < s) (hshard : 0 < shard) (ho : 0 < o)
    (hnr : 0 < numRanks) :
    (smStore outTid).shape = [b, s, o] ∧
    [(pmStore outTid).shape] = [[b, s, o]] ∧
    smStore outTid = reconstructWithDim 0 numRanks 0 [pmStore outTid] := by
  have hxpm_shapes : ∀ x ∈ [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3],
      x.shape = [b, s, shard] := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hwpm_shapes : ∀ w ∈ [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3],
      w.shape = [o, shard] := by
    intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hx_dimN : initSM xSmTid = allGatherPrimDimN 2 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3] := by
    rw [hx_rec]; simp [reconstructWithDim, hxpm0]
  have hw_dimN : initSM wSmTid = allGatherPrimDimN 1 numRanks 0
      [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3] := by
    rw [hw_rec]; simp [reconstructWithDim, hwpm0]
  have hdistr : fw_linear (initSM xSmTid) (initSM wSmTid) =
      allReducePrim numRanks 0
        [fw_linear (initPM xPm0) (initPM wPm0),
         fw_linear (initPM xPm1) (initPM wPm1),
         fw_linear (initPM xPm2) (initPM wPm2),
         fw_linear (initPM xPm3) (initPM wPm3)] := by
    rw [hx_dimN, hw_dimN]
    have := fw_linear_3d_column_parallel numRanks b s shard o
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3]
      [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3]
      hxpm_shapes hwpm_shapes
      (by simp [hxlen]) (by simp [hwlen])
      (by simp [hxpm0]) (by simp [hwpm0])
      hnr hb hs hshard ho
    simpa [List.zipWith] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]
    exact fw_linear_3d_shape b s (shard * numRanks) o _ _ hxsm_shape hwsm_shape
  · rw [hpm]
    have hfw0_shape : (fw_linear (initPM xPm0) (initPM wPm0)).shape = [b, s, o] :=
      fw_linear_3d_shape b s shard o _ _ hxpm0 hwpm0
    have hhead : [fw_linear (initPM xPm0) (initPM wPm0),
        fw_linear (initPM xPm1) (initPM wPm1),
        fw_linear (initPM xPm2) (initPM wPm2),
        fw_linear (initPM xPm3) (initPM wPm3)].head? =
        some (fw_linear (initPM xPm0) (initPM wPm0)) := rfl
    have hsh := allReducePrim_shape numRanks 0 _ _ hhead
    simp [hsh, hfw0_shape]
  · rw [hsm, hdistr, ← hpm]
    simp [reconstructWithDim]


set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
theorem transposeAxes_12_chunkPrim_gather3
    (x : Tensor) (hshape : x.shape = [16, 64, 8, 16]) :
    transposeAxes 1 2 x = allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrim 4 0 x),
       transposeAxes 1 2 (chunkPrim 4 1 x),
       transposeAxes 1 2 (chunkPrim 4 2 x),
       transposeAxes 1 2 (chunkPrim 4 3 x)] := by
  have hpiece_shape : ∀ r, (transposeAxes 1 2 (chunkPrim 4 r x)).shape = [16, 8, 64, 4] := by
    intro r; simp [transposeAxes, chunkPrim, Tensor.mkShape, listSwapAt, hshape,
                    appendLast, dropLast, divNat, lastD]
  have hLHS_shape : (transposeAxes 1 2 x).shape = [16, 8, 64, 16] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hhead : (([transposeAxes 1 2 (chunkPrim 4 0 x),
       transposeAxes 1 2 (chunkPrim 4 1 x),
       transposeAxes 1 2 (chunkPrim 4 2 x),
       transposeAxes 1 2 (chunkPrim 4 3 x)].head?.map (fun t => t.shape)).getD []) =
       [16, 8, 64, 4] := by
    simp [List.head?, Option.map, hpiece_shape]
  have hRHS_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrim 4 0 x),
       transposeAxes 1 2 (chunkPrim 4 1 x),
       transposeAxes 1 2 (chunkPrim 4 2 x),
       transposeAxes 1 2 (chunkPrim 4 3 x)]).shape = [16, 8, 64, 16] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead, hpiece_shape]
  -- Concrete list computation facts (avoid List.getLast stuck-ness in simp only)
  have h_dl : dropLast [16, 64, 8, 16] = [16, 64, 8] := by simp [dropLast]
  have h_ld : lastD [16, 64, 8, 16] = 16 := by simp [lastD]
  have h_dv : divNat 16 4 = 4 := by simp [divNat]
  have h_al : appendLast [16, 64, 8] 4 = [16, 64, 8, 4] := by simp [appendLast]
  have h_ls12 : listSwapAt [16, 64, 8, 4] 1 2 = [16, 8, 64, 4] := by simp [listSwapAt]
  have h_ls_x : listSwapAt [16, 64, 8, 16] 1 2 = [16, 8, 64, 16] := by simp [listSwapAt]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 131072 := by simpa [prodShape] using hidx
  -- Concrete getLast reductions
  have h_getLast_16_64_8_16 : ∀ h, ([16, 64, 8, 16] : List Nat).getLast h = 16 := fun _ => rfl
  have h_getLast_16_64_8_4 : ∀ h, ([16, 64, 8, 4] : List Nat).getLast h = 4 := fun _ => rfl
  have h_getLast_16_8_64_4 : ∀ h, ([16, 8, 64, 4] : List Nat).getLast h = 4 := fun _ => rfl
  have h_getLast_16_8_64_16 : ∀ h, ([16, 8, 64, 16] : List Nat).getLast h = 16 := fun _ => rfl
  -- Simp lemmas for if-elimination and list operations
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_1024 : (1024 : Nat) ≠ 0 := by omega
  have hne_128 : (128 : Nat) ≠ 0 := by omega
  have hne_16 : (16 : Nat) ≠ 0 := by omega
  have hne_1 : (1 : Nat) ≠ 0 := by omega
  have hne_2048 : (2048 : Nat) ≠ 0 := by omega
  have hne_256 : (256 : Nat) ≠ 0 := by omega
  have hne_32 : (32 : Nat) ≠ 0 := by omega
  have hne_4 : (4 : Nat) ≠ 0 := by omega
  have hne_32768 : (32768 : Nat) ≠ 0 := by omega
  have hne_131072 : (131072 : Nat) ≠ 0 := by omega
  rw [valAt_of_lt _ _ (by simp [hLHS_shape, prodShape]; exact hidx'),
      valAt_of_lt _ _ (by simp [hRHS_shape, prodShape]; exact hidx')]
  -- Case-split on which piece is selected: (idx % 16) / 4 ∈ {0,1,2,3}
  have hr_cases : (idx % 16) / 4 = 0 ∨ (idx % 16) / 4 = 1 ∨ (idx % 16) / 4 = 2 ∨ (idx % 16) / 4 = 3 := by omega
  -- Pre-compute chunkPrim shape reduction
  have hchunk_shape : ∀ r, (chunkPrim 4 r x).shape = [16, 64, 8, 4] := by
    intro r; simp [chunkPrim, Tensor.mkShape, hshape, appendLast, dropLast, divNat, lastD]
  have htchunk_shape : ∀ r, (transposeAxes 1 2 (chunkPrim 4 r x)).shape = [16, 8, 64, 4] := by
    intro r; simp [transposeAxes, Tensor.mkShape, hchunk_shape, listSwapAt]
  -- Arithmetic facts that simp only cannot compute (Nat.mul is @[extern])
  have h_44 : (4 : Nat) * 4 = 16 := by norm_num
  rcases hr_cases with h | h | h | h <;>
  · -- Inline concrete piece shape for valAt bound checks
    -- Common simp lemmas
    have ps1 := show prodShape [8, 64, 16] = 8192 from by simp [prodShape]
    have ps2 := show prodShape [64, 16] = 1024 from by simp [prodShape]
    have ps3 := show prodShape [16] = 16 from by simp [prodShape]
    have ps4 := show prodShape ([] : List Nat) = 1 from by simp [prodShape]
    have ps5 := show prodShape [8, 64, 4] = 2048 from by simp [prodShape]
    have ps6 := show prodShape [64, 4] = 256 from by simp [prodShape]
    have ps7 := show prodShape [4] = 4 from by simp [prodShape]
    have ps8 := show prodShape [64, 8, 16] = 8192 from by simp [prodShape]
    have ps9 := show prodShape [8, 16] = 128 from by simp [prodShape]
    have ps10 := show prodShape [64, 8, 4] = 2048 from by simp [prodShape]
    have ps11 := show prodShape [8, 4] = 32 from by simp [prodShape]
    have ps12 := show prodShape [16, 8, 64, 16] = 131072 from by simp [prodShape]
    have ps13 := show prodShape [16, 64, 8, 16] = 131072 from by simp [prodShape]
    have ps14 := show prodShape [16, 8, 64, 4] = 32768 from by simp [prodShape]
    have ps15 := show prodShape [16, 64, 8, 4] = 32768 from by simp [prodShape]
    -- Simplify LHS
    conv_lhs =>
      simp (config := { maxSteps := 2000000 }) only [
        transposeAxes, Tensor.mkShape, hshape, listSwapAt, h_ls_x,
        flatToMulti, multiToFlat, valAt,
        ps1, ps2, ps3, ps4, ps8, ps9, ps12, ps13,
        List.getD, List.set, List.length, Nat.sub_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Option.getD_some, Option.getD_none,
        hne_8192, hne_1024, hne_128, hne_16, hne_1,
        Nat.mul_one, Nat.add_zero, Nat.div_one, Nat.mod_one,
        if_neg, if_pos, ite_false, ite_true, dite_true, dite_false]
    -- First unfold outer allGatherPrimDimN + select piece
    simp only [h, allGatherPrimDimN, Tensor.mkShape, hhead, hpiece_shape,
      List.getD, List.set, List.drop, List.foldl, List.length, List.head?,
      Option.map, Option.getD, Nat.sub_zero,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none,
      hne_4, hne_16, hne_1, if_neg, if_pos, ite_false, ite_true,
      ps14, ps15,
      Nat.mul_one, Nat.add_zero, Nat.div_one, Nat.mod_one, h_44]
    -- Single simp pass with hshape, unfolding all definitions
    simp (config := { maxSteps := 8000000 }) only [hshape,
      transposeAxes, chunkPrim, Tensor.mkShape,
      listSwapAt, h_ls12, h_ls_x,
      appendLast, dropLast, divNat, lastD,
      h_getLast_16_64_8_16, h_getLast_16_64_8_4, h_getLast_16_8_64_4, h_getLast_16_8_64_16,
      List.dropLast, List.getLast?, List.getLastD,
      List.getLast_cons, List.getLast_singleton, List.cons_ne_nil,
      List.cons_append, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none,
      List.getD, List.set, List.length, Nat.sub_zero,
      flatToMulti, multiToFlat, valAt,
      ps1, ps2, ps3, ps4, ps5, ps6, ps7, ps8, ps9, ps10, ps11, ps12, ps13, ps14, ps15,
      hne_8192, hne_1024, hne_128, hne_16, hne_1,
      hne_2048, hne_256, hne_32, hne_4, hne_32768, hne_131072,
      Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.div_one, Nat.mod_one,
      if_neg, if_pos, ite_false, ite_true, dite_true, dite_false]
    -- Normalize mod-of-mod chains (omega proves these individually)
    have hmm1 : ∀ n, n % 8192 % 1024 = n % 1024 := fun n => by omega
    have hmm2 : ∀ n, n % 1024 % 16 = n % 16 := fun n => by omega
    have hmm3 : ∀ n, n % 16 % 4 = n % 4 := fun n => by omega
    have hmm4 : ∀ n, n % 2048 % 256 = n % 256 := fun n => by omega
    have hmm5 : ∀ n, n % 256 % 4 = n % 4 := fun n => by omega
    -- Key lemmas: div/mod of (n * 4 + r) where r < 4
    have hdm1 : ∀ n, (n * 4 + idx % 4) / 4 = n := fun n => by omega
    have hdm2 : ∀ n, (n * 4 + idx % 4) % 4 = idx % 4 := fun n => by omega
    -- Concrete arithmetic that simp only cannot compute
    have h_16d4 : (16 : Nat) / 4 = 4 := by norm_num
    have h_0m4 : (0 : Nat) % 4 = 0 := by norm_num
    have h_1m4 : (1 : Nat) % 4 = 1 := by norm_num
    have h_2m4 : (2 : Nat) % 4 = 2 := by norm_num
    have h_3m4 : (3 : Nat) % 4 = 3 := by norm_num
    simp only [hmm1, hmm2, hmm3, hmm4, hmm5, hdm1, hdm2,
               h_16d4, h_0m4, h_1m4, h_2m4, h_3m4,
               Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
               Nat.mul_one, Nat.one_mul]
    split_ifs <;> first | rfl | (congr 1; ext; omega) | omega

end TrainVerify.Denote.Common
