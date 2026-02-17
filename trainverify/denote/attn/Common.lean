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


end TrainVerify.Denote.Common
