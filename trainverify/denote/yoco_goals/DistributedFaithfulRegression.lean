/-
Regression witnesses for the graph-aware faithful distributed evaluator.  The node
indices below are concrete declarations from the generated YOCO-MoE SM/PM graphs.
-/
import denote.DenoteDistributedFaithful
import denote.GeneratedYOCOMoE

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.DistributedFaithfulRegression
noncomputable section

set_option maxRecDepth 100000
set_option linter.style.nativeDecide false

private def dummyNode : NodeDecl := { rank := 0, op := "", ins := [], outs := [] }

def smShuffle : NodeDecl := sm.nodes.getD 472 dummyNode
def pmShuffle0 : NodeDecl := pm.nodes.getD 1003 dummyNode
def pmShuffle1 : NodeDecl := pm.nodes.getD 1005 dummyNode

def pmUnshuffle0 : NodeDecl := pm.nodes.getD 1912 dummyNode
def pmUnshuffle1 : NodeDecl := pm.nodes.getD 1913 dummyNode

def shard (start : Nat) : Tensor :=
  Tensor.mkShape [4, 1] (fun i => ((start + i.val : Nat) : Scalar))

@[simp] theorem shard_shape (start : Nat) : (shard start).shape = [4, 1] := rfl

@[simp] theorem valAt_shard_of_lt (start i : Nat) (hi : i < 4) :
    valAt (shard start) i = ((start + i : Nat) : Scalar) := by
  rw [valAt_of_lt]
  · rfl
  · simpa [shard, Tensor.mkShape, prodShape] using hi

def cuTensor : Tensor :=
  Tensor.mkShape [2] (fun i => if i.val = 0 then 0 else 8)

def shuffleStore : Store := fun tid =>
  if tid = 8011 then shard 0
  else if tid = 13257 then shard 0
  else if tid = 13258 then shard 4
  else if tid = 5337 then cuTensor
  else zeroTensor []

def observe4 (x : Tensor) : List Scalar :=
  (List.range 4).map (valAt x)

@[simp] theorem decode_cuTensor : decodeCuSeqlens cuTensor = [0, 8] := by
  unfold decodeCuSeqlens cuTensor
  have hp : prodShape (Tensor.mkShape [2]
      (fun i => if i.val = 0 then (0 : Scalar) else 8)).shape = 2 := by
    simp [Tensor.mkShape, prodShape]
  rw [hp]
  change (List.range 2).map _ = _
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append]
  simp only [valAt, Tensor.mkShape, prodShape]
  norm_num [scalarToNat]

-- These facts pin the regression to actual generated declarations, not hand-made
-- lookalikes. Node 472 is the SM cp=1 shuffle; PM 1003/1005 are its cp=2 replicas.
theorem smShuffle_generated : smShuffle =
    { rank := 0, op := "OpName.FW_maybe_shuffle",
      ins := [8011, 5337], outs := [5338], params := [1, 0] } := by
  native_decide

theorem pmShuffle0_generated : pmShuffle0 =
    { rank := 0, op := "OpName.FW_maybe_shuffle",
      ins := [13257, 5337], outs := [9655], params := [2, 0] } := by
  native_decide

theorem pmShuffle1_generated : pmShuffle1 =
    { rank := 1, op := "OpName.FW_maybe_shuffle",
      ins := [13258, 5337], outs := [9656], params := [2, 1] } := by
  native_decide

theorem pmShuffle_buddies :
    pm.replicaBuddies pmShuffle0 = [pmShuffle0, pmShuffle1] ∧
    pm.replicaBuddies pmShuffle1 = [pmShuffle0, pmShuffle1] := by
  native_decide

-- The graph evaluator reaches the collective-free authority branch at cp=1.
theorem sm_cp1_identity :
    applyNodeDistributedFaithful sm shuffleStore smShuffle 5338 = shard 0 := by
  rw [smShuffle_generated, applyNodeDistributedFaithful_shuffle_out]
  apply applyNodeFaithfulShuffleValue_cpSize_one
  · native_decide
  · rfl
  · rfl

-- The generated PM replica pair observes both data shards, in declared buddy order.
theorem pm_rank0_values :
    observe4 (applyNodeDistributedFaithful pm shuffleStore pmShuffle0 9655) =
      [0, 1, 6, 7] := by
  rw [pmShuffle0_generated, applyNodeDistributedFaithful_shuffle_out]
  rw [← pmShuffle0_generated]
  unfold applyNodeFaithfulShuffleValue
  rw [pmShuffle_buddies.1]
  simp only [List.map]
  rw [pmShuffle0_generated, pmShuffle1_generated]
  change observe4 (fw_maybe_shuffle_collective [shard 0, shard 4]
    (decodeCuSeqlens cuTensor) 2 0) = [0, 1, 6, 7]
  rw [decode_cuTensor]
  have h0 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 0) 0 = 0 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  have h1 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 0) 1 = 1 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  have h2 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 0) 2 = 6 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  have h3 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 0) 3 = 7 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  unfold observe4
  norm_num [List.range_succ, h0, h1, h2, h3]

theorem pm_rank1_values :
    observe4 (applyNodeDistributedFaithful pm shuffleStore pmShuffle1 9656) =
      [2, 3, 4, 5] := by
  rw [pmShuffle1_generated, applyNodeDistributedFaithful_shuffle_out]
  rw [← pmShuffle1_generated]
  unfold applyNodeFaithfulShuffleValue
  rw [pmShuffle_buddies.2]
  simp only [List.map]
  rw [pmShuffle0_generated, pmShuffle1_generated]
  change observe4 (fw_maybe_shuffle_collective [shard 0, shard 4]
    (decodeCuSeqlens cuTensor) 2 1) = [2, 3, 4, 5]
  rw [decode_cuTensor]
  have h0 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 1) 0 = 2 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  have h1 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 1) 1 = 3 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  have h2 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 1) 2 = 4 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  have h3 : valAt (fw_maybe_shuffle_collective [shard 0, shard 4] [0, 8] 2 1) 3 = 5 := by
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt, List.getD,
        prodShape, shard, Tensor.mkShape]
  unfold observe4
  norm_num [List.range_succ, h0, h1, h2, h3]

theorem generated_shapes :
    (applyNodeDistributedFaithful sm shuffleStore smShuffle 5338).shape = [4, 1] ∧
    (applyNodeDistributedFaithful pm shuffleStore pmShuffle0 9655).shape = [4, 1] ∧
    (applyNodeDistributedFaithful pm shuffleStore pmShuffle1 9656).shape = [4, 1] := by
  rw [sm_cp1_identity]
  constructor
  · rfl
  constructor
  · rw [pmShuffle0_generated, applyNodeDistributedFaithful_shuffle_out]
    rw [← pmShuffle0_generated]
    unfold applyNodeFaithfulShuffleValue
    rw [pmShuffle_buddies.1]
    simp [pmShuffle0_generated, pmShuffle1_generated, shuffleStore, shard,
      Tensor.mkShape]
  · rw [pmShuffle1_generated, applyNodeDistributedFaithful_shuffle_out]
    rw [← pmShuffle1_generated]
    unfold applyNodeFaithfulShuffleValue
    rw [pmShuffle_buddies.2]
    simp [pmShuffle0_generated, pmShuffle1_generated, shuffleStore, shard,
      Tensor.mkShape]

-- Real generated inverse nodes are intercepted as well (backward forms remain delegated).
theorem pmUnshuffle0_generated : pmUnshuffle0 =
    { rank := 0, op := "OpName.FW_maybe_unshuffle",
      ins := [11721, 5927], outs := [11727], params := [2, 0] } := by
  native_decide

theorem pmUnshuffle1_generated : pmUnshuffle1 =
    { rank := 1, op := "OpName.FW_maybe_unshuffle",
      ins := [11722, 5927], outs := [11728], params := [2, 1] } := by
  native_decide

theorem generated_unshuffle_intercepted :
    applyNodeDistributedFaithful pm shuffleStore pmUnshuffle0 11727 =
      applyNodeFaithfulUnshuffleValue pm shuffleStore pmUnshuffle0 := by
  rw [pmUnshuffle0_generated]
  exact applyNodeDistributedFaithful_unshuffle_out _ _ _ _ _ _ _

-- A representative real non-collective generated node delegates byte-for-byte to
-- the pre-existing distributed evaluator, retaining its MoE/attention behavior.
theorem generated_nonshuffle_delegates :
    applyNodeDistributedFaithful sm shuffleStore (sm.nodes.getD 0 dummyNode) =
      applyNodeDistributed sm shuffleStore (sm.nodes.getD 0 dummyNode) := by
  apply applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
  · native_decide
  · native_decide
  · native_decide

/-! ## Arbitrary-store pre-shuffle compatibility

These are denotation theorems rather than tests of `shuffleStore`: they hold for every
initial store.  SM's first collective is node 472 and PM's is node 1003.  In
particular, PM node 1004 may be an `AllGather`; choosing prefix 1003 is sound because
none of the source tids below is rewritten by the remaining graph. -/

private theorem smPreShuffleFacts :
    (∀ n ∈ sm.nodes.take 472,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag") ∧
    (∀ n ∈ sm.nodes.drop 472, n.outs ≠ []) ∧
    (∀ n ∈ sm.nodes.drop 472,
      5330 ∉ n.outs ∧ 8011 ∉ n.outs ∧ 5337 ∉ n.outs) := by
  native_decide

private theorem pmPreShuffleFacts :
    (∀ n ∈ pm.nodes.take 1003,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag") ∧
    (∀ n ∈ pm.nodes.drop 1003, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1003,
      9625 ∉ n.outs ∧ 9626 ∉ n.outs ∧
      13257 ∉ n.outs ∧ 13258 ∉ n.outs ∧ 5337 ∉ n.outs) := by
  native_decide

/-- SM's pre-shuffle producer and both inputs read by its first shuffle retain the
old distributed denotation for arbitrary initialization. -/
theorem sm_pre_shuffle_distributed_bridges (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5330 =
        denoteGraphDistributed sm initSM 5330 ∧
    denoteGraphDistributedFaithful sm initSM 8011 =
        denoteGraphDistributed sm initSM 8011 ∧
    denoteGraphDistributedFaithful sm initSM 5337 =
        denoteGraphDistributed sm initSM 5337 := by
  have hf := smPreShuffleFacts
  refine ⟨?_, ?_, ?_⟩
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      sm initSM 5330 472 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      sm initSM 8011 472 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      sm initSM 5337 472 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).2.2)

/-- PM's two early products, the two mref sources consumed at the first shuffle,
and their metadata retain the old denotation for arbitrary initialization. -/
theorem pm_pre_shuffle_distributed_bridges (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9625 =
        denoteGraphDistributed pm initPM 9625 ∧
    denoteGraphDistributedFaithful pm initPM 9626 =
        denoteGraphDistributed pm initPM 9626 ∧
    denoteGraphDistributedFaithful pm initPM 13257 =
        denoteGraphDistributed pm initPM 13257 ∧
    denoteGraphDistributedFaithful pm initPM 13258 =
        denoteGraphDistributed pm initPM 13258 ∧
    denoteGraphDistributedFaithful pm initPM 5337 =
        denoteGraphDistributed pm initPM 5337 := by
  have hf := pmPreShuffleFacts
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      pm initPM 9625 1003 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      pm initPM 9626 1003 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      pm initPM 13257 1003 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).2.2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      pm initPM 13258 1003 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).2.2.2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix
      pm initPM 5337 1003 hf.1 hf.2.1 (fun n hn => (hf.2.2 n hn).2.2.2.2)

end
end TrainVerify.Denote.DistributedFaithfulRegression
