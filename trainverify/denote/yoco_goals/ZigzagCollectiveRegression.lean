/-
Regression witnesses for the value-faithful, cross-rank zigzag collective model.
These are deliberately separate from the local evaluator model.
-/
import denote.ZigzagCollective

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.ZigzagCollectiveRegression
noncomputable section

def observe (n : Nat) (x : Tensor) : List Scalar :=
  (List.range n).map (valAt x)

def shard (start len : Nat) : Tensor :=
  Tensor.mkShape [len, 1] (fun i => ((start + i.val : Nat) : Scalar))

def cu1 : List Nat := [0, 8]
def linear2 : List Tensor := [shard 0 4, shard 4 4]
def shuf20 := fw_maybe_shuffle_collective linear2 cu1 2 0
def shuf21 := fw_maybe_shuffle_collective linear2 cu1 2 1
def rest20 := fw_maybe_unshuffle_collective [shuf20, shuf21] cu1 2 0
def rest21 := fw_maybe_unshuffle_collective [shuf20, shuf21] cu1 2 1

def cuPacked : List Nat := [0, 8, 16]
def linearPacked : List Tensor := [shard 0 8, shard 8 8]
def packed0 := fw_maybe_shuffle_collective linearPacked cuPacked 2 0
def packed1 := fw_maybe_shuffle_collective linearPacked cuPacked 2 1
def packedRest0 := fw_maybe_unshuffle_collective [packed0, packed1] cuPacked 2 0
def packedRest1 := fw_maybe_unshuffle_collective [packed0, packed1] cuPacked 2 1

def single := shard 0 8
def cp1shuf := fw_maybe_shuffle_collective [single] cu1 1 0
def cp1rest := fw_maybe_unshuffle_collective [cp1shuf] cu1 1 0

@[simp] theorem linear2_get0 : linear2.getD 0 (zeroTensor []) = shard 0 4 := rfl
@[simp] theorem linear2_get1 : linear2.getD 1 (zeroTensor []) = shard 4 4 := rfl
@[simp] theorem packed_get0 : linearPacked.getD 0 (zeroTensor []) = shard 0 8 := rfl
@[simp] theorem packed_get1 : linearPacked.getD 1 (zeroTensor []) = shard 8 8 := rfl
@[simp] theorem shufs_get0 : [shuf20, shuf21].getD 0 (zeroTensor []) = shuf20 := rfl
@[simp] theorem shufs_get1 : [shuf20, shuf21].getD 1 (zeroTensor []) = shuf21 := rfl
@[simp] theorem packedShufs_get0 : [packed0, packed1].getD 0 (zeroTensor []) = packed0 := rfl
@[simp] theorem packedShufs_get1 : [packed0, packed1].getD 1 (zeroTensor []) = packed1 := rfl
@[simp] theorem singleton_get0 : [single].getD 0 (zeroTensor []) = single := rfl

/-- Executable hidden-stride-one projection of the Tensor shuffle index semantics. -/
def shuffleNat (xs : List (List Nat)) (cu : List Nat)
    (cpSize cpRank : Nat) : List Nat :=
  let chunk := (xs.getD cpRank []).length
  let flat := xs.flatten
  (List.range chunk).map (fun k => flat.getD (zigzagPos cu cpSize cpRank k) 0)

/-- Executable hidden-stride-one projection of the Tensor inverse index semantics. -/
def unshuffleNat (xs : List (List Nat)) (cu : List Nat)
    (cpSize cpRank : Nat) : List Nat :=
  let chunk := (xs.getD cpRank []).length
  (List.range chunk).map (fun k =>
    let g := cpRank * chunk + k
    let r := destRank cu cpSize g
    let off := zigzagInvOffset cu cpSize r g
    (xs.getD r []).getD off 0)

def natLinear2 := [[0, 1, 2, 3], [4, 5, 6, 7]]
def natShuf20 := shuffleNat natLinear2 cu1 2 0
def natShuf21 := shuffleNat natLinear2 cu1 2 1
def natPacked :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14, 15]]
def natPacked0 := shuffleNat natPacked cuPacked 2 0
def natPacked1 := shuffleNat natPacked cuPacked 2 1

macro "zigzag_regression" : tactic =>
  `(tactic|
    norm_num [List.getD, List.range_succ, List.map_append, List.foldl, observe,
      shuf20, shuf21, rest20, rest21, packed0, packed1, packedRest0,
      packedRest1, cp1shuf, cp1rest, single, cu1, cuPacked, linear2,
      linearPacked, shard, fw_maybe_shuffle_collective,
      fw_maybe_unshuffle_collective, gatherFromRank, zigzagPos, zigzagPosAux,
      sliceSizeAt, destRank, destRankAux, zigzagInvOffset,
      zigzagInvOffsetAux, valAt, zeroTensor, Tensor.mkShape, prodShape,
      listLast!])

-- cpSize=1 is extensionally the identity on an actual Tensor.
example : cp1shuf = single := by
  apply fw_maybe_shuffle_collective_cpSize_one
  rfl

example : cp1rest = single := by
  apply fw_maybe_unshuffle_collective_cpSize_one
  rfl

-- NNScaler 0.9 one-sequence CP2 authority mapping.
example : natShuf20 = [0, 1, 6, 7] := by
  norm_num [natShuf20, shuffleNat, natLinear2, cu1, List.range_succ,
    zigzagPos, zigzagPosAux, sliceSizeAt]
example : natShuf21 = [2, 3, 4, 5] := by
  norm_num [natShuf21, shuffleNat, natLinear2, cu1, List.range_succ,
    zigzagPos, zigzagPosAux, sliceSizeAt]

-- This is not ordinary concatenation followed by contiguous re-sharding.
example : natShuf20 ≠ natLinear2.flatten.take 4 := by
  norm_num [natShuf20, shuffleNat, natLinear2, cu1, List.range_succ,
    zigzagPos, zigzagPosAux, sliceSizeAt]

-- The inverse collective restores the original ordinary shards.
example : unshuffleNat [natShuf20, natShuf21] cu1 2 0 = [0, 1, 2, 3] := by
  norm_num [unshuffleNat, natShuf20, natShuf21, shuffleNat, natLinear2, cu1,
    List.range_succ, zigzagPos, zigzagPosAux, sliceSizeAt, destRank, destRankAux,
    zigzagInvOffset, zigzagInvOffsetAux]
example : unshuffleNat [natShuf20, natShuf21] cu1 2 1 = [4, 5, 6, 7] := by
  norm_num [unshuffleNat, natShuf20, natShuf21, shuffleNat, natLinear2, cu1,
    List.range_succ, zigzagPos, zigzagPosAux, sliceSizeAt, destRank, destRankAux,
    zigzagInvOffset, zigzagInvOffsetAux]

-- Shape preservation is general; these instantiate both directions concretely.
example : shuf20.shape = (linear2.getD 0 (zeroTensor [])).shape :=
  fw_maybe_shuffle_collective_shape _ _ _ _
example : rest20.shape = ([shuf20, shuf21].getD 0 (zeroTensor [])).shape :=
  fw_maybe_unshuffle_collective_shape _ _ _ _
example : shuf20.shape = [4, 1] ∧ shuf21.shape = [4, 1] ∧
    rest20.shape = [4, 1] ∧ rest21.shape = [4, 1] := by
  zigzag_regression

-- Packed sequences are traversed independently, front then back per sequence.
example : natPacked0 = [0, 1, 6, 7, 8, 9, 14, 15] := by
  norm_num [natPacked0, shuffleNat, natPacked, cuPacked, List.range_succ,
    zigzagPos, zigzagPosAux, sliceSizeAt]
example : natPacked1 = [2, 3, 4, 5, 10, 11, 12, 13] := by
  norm_num [natPacked1, shuffleNat, natPacked, cuPacked, List.range_succ,
    zigzagPos, zigzagPosAux, sliceSizeAt]
example : unshuffleNat [natPacked0, natPacked1] cuPacked 2 0 ++
    unshuffleNat [natPacked0, natPacked1] cuPacked 2 1 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by
  norm_num [unshuffleNat, natPacked0, natPacked1, shuffleNat, natPacked, cuPacked,
    List.range_succ, zigzagPos, zigzagPosAux, sliceSizeAt, destRank, destRankAux,
    zigzagInvOffset, zigzagInvOffsetAux]
example : packed0.shape = [8, 1] ∧ packed1.shape = [8, 1] ∧
    packedRest0.shape = [8, 1] ∧ packedRest1.shape = [8, 1] := by
  zigzag_regression

-- The concrete CP2 fixture makes the refined metadata invariant non-vacuous.
example : ZigzagCuWF cu1 linear2 2 := by
  refine ⟨by norm_num, by norm_num [linear2], by norm_num [cu1],
    by norm_num [cu1], ?_, ?_, ?_, ?_,
    by norm_num [linear2, shard, cu1, listLast!, Tensor.mkShape]⟩
  · intro s hs
    have hs0 : s = 0 := by simpa [cu1] using hs
    subst s
    norm_num [cu1]
  · intro s hs
    have hs0 : s = 0 := by simpa [cu1] using hs
    subst s
    norm_num [cu1]
  · intro x hx
    simp [linear2] at hx
    rcases hx with rfl | rfl <;> decide
  · intro x hx
    simp [linear2] at hx
    rcases hx with rfl | rfl <;>
      norm_num [linear2, shard, Tensor.mkShape, zeroTensor]

end
end TrainVerify.Denote.ZigzagCollectiveRegression
