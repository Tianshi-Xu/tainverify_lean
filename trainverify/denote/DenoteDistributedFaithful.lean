/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ZigzagCollective

/-!
# Graph-aware faithful distributed denotation

This evaluator composes the existing distributed evaluator (including its faithful
full-expert MoE and graph-aware ring-attention branches) with the value-faithful
cross-rank semantics for forward `maybe_shuffle` and `maybe_unshuffle`.

Replica order is exactly `GraphDecl.replicaBuddies`; it is never inferred or sorted.
Generated inputs have order `[data, cu_seqlens]`, and generated parameters have order
`[cpSize, cpRank]`. Missing metadata therefore inherits the existing fail-closed
singleton behavior of `replicaBuddies`.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote
noncomputable section

/-- Cross-rank value of a generated forward maybe-shuffle node. -/
noncomputable def applyNodeFaithfulShuffleValue
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Tensor :=
  let buddies := g.replicaBuddies n
  let dataShards := buddies.map (fun m => s (m.ins.getD 0 0))
  let cu := decodeCuSeqlens (s (n.ins.getD 1 0))
  fw_maybe_shuffle_collective dataShards cu
    (n.params.getD 0 1) (n.params.getD 1 0)

/-- Cross-rank value of a generated forward maybe-unshuffle node. -/
noncomputable def applyNodeFaithfulUnshuffleValue
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Tensor :=
  let buddies := g.replicaBuddies n
  let dataShards := buddies.map (fun m => s (m.ins.getD 0 0))
  let cu := decodeCuSeqlens (s (n.ins.getD 1 0))
  fw_maybe_unshuffle_collective dataShards cu
    (n.params.getD 0 1) (n.params.getD 1 0)

/-- Store one collective value at every output declared by the node. -/
noncomputable def storeCollectiveOutputs
    (s : Store) (n : NodeDecl) (value : Tensor) : Store :=
  storeSet s (n.outs.map fun tid => (tid, value))

/-- Faithful distributed apply step. Forward shuffle/unshuffle are intercepted;
all other operators delegate *exactly* to `applyNodeDistributed`. -/
noncomputable def applyNodeDistributedFaithful
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Store :=
  if n.op = "OpName.FW_maybe_shuffle" then
    storeCollectiveOutputs s n (applyNodeFaithfulShuffleValue g s n)
  else if n.op = "OpName.FW_maybe_unshuffle" then
    storeCollectiveOutputs s n (applyNodeFaithfulUnshuffleValue g s n)
  else
    applyNodeDistributed g s n

/-- Production graph fold using the faithful distributed node evaluator. -/
noncomputable def denoteGraphDistributedFaithful
    (g : GraphDecl) (init : Store) : Store :=
  g.nodes.foldl (applyNodeDistributedFaithful g) init

/-- A generated singleton-output shuffle writes its collective result. -/
theorem applyNodeDistributedFaithful_shuffle_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (dataTid cuTid outTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_maybe_shuffle",
        ins := [dataTid, cuTid], outs := [outTid], params := params } outTid =
      applyNodeFaithfulShuffleValue g s
        { rank := rank, op := "OpName.FW_maybe_shuffle",
          ins := [dataTid, cuTid], outs := [outTid], params := params } := by
  unfold applyNodeDistributedFaithful storeCollectiveOutputs
  simp [storeSet]

/-- A generated singleton-output unshuffle writes its collective result. -/
theorem applyNodeDistributedFaithful_unshuffle_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (dataTid cuTid outTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_maybe_unshuffle",
        ins := [dataTid, cuTid], outs := [outTid], params := params } outTid =
      applyNodeFaithfulUnshuffleValue g s
        { rank := rank, op := "OpName.FW_maybe_unshuffle",
          ins := [dataTid, cuTid], outs := [outTid], params := params } := by
  unfold applyNodeDistributedFaithful storeCollectiveOutputs
  simp [storeSet]

/-- The extension is conservative away from the two forward collectives. -/
theorem applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (g : GraphDecl) (s : Store) (n : NodeDecl)
    (hshuffle : n.op ≠ "OpName.FW_maybe_shuffle")
    (hunshuffle : n.op ≠ "OpName.FW_maybe_unshuffle") :
    applyNodeDistributedFaithful g s n = applyNodeDistributed g s n := by
  unfold applyNodeDistributedFaithful
  rw [if_neg hshuffle, if_neg hunshuffle]

/-- With a singleton replica group and generated `[1, 0]` parameters, shuffle
collapses extensionally to the node's data input. -/
theorem applyNodeFaithfulShuffleValue_cpSize_one
    (g : GraphDecl) (s : Store) (n : NodeDecl)
    (hbuddy : g.replicaBuddies n = [n])
    (hcp : n.params.getD 0 1 = 1)
    (hrank : n.params.getD 1 0 = 0) :
    applyNodeFaithfulShuffleValue g s n = s (n.ins.getD 0 0) := by
  unfold applyNodeFaithfulShuffleValue
  rw [hbuddy]
  simp only [List.map]
  rw [hcp, hrank]
  exact fw_maybe_shuffle_collective_cpSize_one _ _ _ rfl

end
end TrainVerify.Denote
