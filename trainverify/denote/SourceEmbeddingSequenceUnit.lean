import denote.SourceEmbeddingBatch
import denote.EmbeddingSequenceShard

/-!
# Source embedding: one DP batch unit, ordered TP sequence shards

This module composes existing value theorems without new index proofs or
changes to source primitives. Kernel acceptance is recorded by the parent
serial build campaign.

`idsShards` contains the ordered TP sequence pieces of ONE DP unit. Its list
positions determine gather order; never concatenate different DP copies here.
The same full weight is used by every local embedding. The result is before any
AllToAll: no AllToAll axis convention or subsequent activation relation is used.

The premises concern only input shapes, positive partition/active dimensions,
the selected DP chunk and its ordered TP ID reconstruction. Vocabulary size `V`
may be zero, as in the batch theorem; no label-domain premise is needed because
`scalarToNat` and default reads retain the existing embedding semantics. Source
use is ordinary embedding (start = 0, stop = vocab), not offset/vocab sharding.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

/-- A global embedding batch chunk equals the ordered sequence gather of local
embeddings with one shared weight, within the selected DP unit only. -/
theorem fw_embedding_dp_tp_sequence_unit
    (D u T B S V H : Nat)
    (fullIDs unitIDs weight : Tensor) (idsShards : List Tensor)
    (hD : 0 < D) (hu : u < D) (hT : 0 < T)
    (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hids : fullIDs.shape = [B * D, S * T])
    (hweight : weight.shape = [V, H])
    (hunitIDs : unitIDs = chunkPrimDimN 0 D u fullIDs)
    (hlen : idsShards.length = T)
    (hshards : ∀ ids ∈ idsShards, ids.shape = [B, S])
    (hunitGather : unitIDs = allGatherPrimDimN 1 T 0 idsShards) :
    chunkPrimDimN 0 D u (fw_embedding fullIDs weight) =
      allGatherPrimDimN 1 T 0
        (idsShards.map (fun ids => fw_embedding ids weight)) := by
  have hlast : lastD weight.shape = H := by rw [hweight]; rfl
  calc
    chunkPrimDimN 0 D u (fw_embedding fullIDs weight) =
        fw_embedding unitIDs weight :=
      (fw_embedding_batch_chunk_dim0 D u B (S * T) V H
        fullIDs unitIDs weight hD hu (Nat.mul_pos hS hT) hH
        hids hweight hunitIDs).symm
    _ = fw_embedding (allGatherPrimDimN 1 T 0 idsShards) weight :=
      congrArg (fun ids => fw_embedding ids weight) hunitGather
    _ = allGatherPrimDimN 1 T 0
        (idsShards.map (fun ids => fw_embedding ids weight)) :=
      fw_embedding_allGatherPrimDimN_dim1_shared_weight T B S H
        idsShards weight hT hB hS hH hlen hshards hlast

/-- Transport to named source outputs using individual embedding producer
 equations, not an assumed final activation reconstruction. `List.Forall₂`
 preserves the input/output TP order. Tensor arguments may be final-store reads;
 operand liveness and whole-graph equality remain separate obligations. -/
theorem fw_embedding_dp_tp_sequence_unit_of_source_eqs
    (D u T B S V H : Nat)
    (fullIDs unitIDs weight : Tensor) (idsShards : List Tensor)
    (globalOut : Tensor) (unitOuts : List Tensor)
    (hD : 0 < D) (hu : u < D) (hT : 0 < T)
    (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hids : fullIDs.shape = [B * D, S * T])
    (hweight : weight.shape = [V, H])
    (hunitIDs : unitIDs = chunkPrimDimN 0 D u fullIDs)
    (hlen : idsShards.length = T)
    (hshards : ∀ ids ∈ idsShards, ids.shape = [B, S])
    (hunitGather : unitIDs = allGatherPrimDimN 1 T 0 idsShards)
    (hglobal : globalOut = fw_embedding fullIDs weight)
    (hlocal : List.Forall₂ (fun out ids => out = fw_embedding ids weight)
      unitOuts idsShards) :
    chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 1 T 0 unitOuts := by
  have transport : ∀ {os xs : List Tensor},
      List.Forall₂ (fun out ids => out = fw_embedding ids weight) os xs →
      os = xs.map (fun ids => fw_embedding ids weight) := by
    intro os xs h
    induction h with
    | nil => rfl
    | cons heq hrest ih => exact congrArg₂ List.cons heq ih
  have houtputs : unitOuts = idsShards.map (fun ids => fw_embedding ids weight) :=
    transport hlocal
  rw [hglobal, houtputs]
  exact fw_embedding_dp_tp_sequence_unit D u T B S V H
    fullIDs unitIDs weight idsShards hD hu hT hB hS hH
    hids hweight hunitIDs hlen hshards hunitGather

#print axioms fw_embedding_dp_tp_sequence_unit
#print axioms fw_embedding_dp_tp_sequence_unit_of_source_eqs
end
end TrainVerify.Denote
