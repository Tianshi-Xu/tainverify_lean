import denote.SourceEmbeddingBatch
import denote.SourceEmbeddingExchange

/-!
# Source embedding: DP batch unit, TP sequence-to-hidden exchange

This module composes existing operator value theorems, without new index proofs
or changes to source primitives. `idsShards` lists the ordered TP sequence pieces
of ONE DP unit; every sender uses the same full weight. Faithful AllToAll splits
hidden (axis 2), then gathers sequence (axis 1), before the final hidden gather.

The source adapter consumes individual producer equations, not an assumed final
activation equality. Concrete source applicability, operand liveness and initial
parameter/input frames remain obligations of its caller. Ordinary embedding
(start = 0, stop = vocab) is intended, not offset/vocab-sharded embedding.

UNCOMPILED CANDIDATE: compilation and axiom audit belong to the parent serial
builder. The declarations below include audit commands, not audit receipts.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

/-- The selected DP batch chunk of the global embedding is reconstructed by
hidden-gathering faithful sequence-to-hidden exchanges within that DP unit. -/
theorem fw_embedding_dp_tp_position_unit
    (D u T B S V H : Nat)
    (fullIDs unitIDs W : Tensor) (idsShards : List Tensor)
    (hD : 0 < D) (hu : u < D) (hT : 0 < T)
    (hB : 0 < B) (hS : 0 < S) (hV : 0 < V) (hH : 0 < H)
    (hids : fullIDs.shape = [B * D, S * T])
    (hW : W.shape = [V, H * T])
    (hunitIDs : unitIDs = chunkPrimDimN 0 D u fullIDs)
    (hlen : idsShards.length = T)
    (hshards : ∀ ids ∈ idsShards, ids.shape = [B, S])
    (hunitGather : unitIDs = allGatherPrimDimN 1 T 0 idsShards) :
    chunkPrimDimN 0 D u (fw_embedding fullIDs W) =
      allGatherPrimDimN 2 T 0
        (List.ofFn fun dst : Fin T =>
          AllToAllSourceFaithful.tensor T dst.val 1 2
            (idsShards.map (fun ids => fw_embedding ids W))) := by
  calc
    chunkPrimDimN 0 D u (fw_embedding fullIDs W) =
        fw_embedding unitIDs W :=
      (fw_embedding_batch_chunk_dim0 D u B (S * T) V (H * T)
        fullIDs unitIDs W hD hu (Nat.mul_pos hS hT) (Nat.mul_pos hH hT)
        hids hW hunitIDs).symm
    _ = fw_embedding (allGatherPrimDimN 1 T 0 idsShards) W :=
      congrArg (fun ids => fw_embedding ids W) hunitGather
    _ = allGatherPrimDimN 2 T 0
        (List.ofFn fun dst : Fin T =>
          AllToAllSourceFaithful.tensor T dst.val 1 2
            (idsShards.map (fun ids => fw_embedding ids W))) :=
      (SourceEmbeddingExchange.embedding_sequence_to_hidden_exchange
        T B S V H idsShards W hT hB hS hV hH hlen hshards hW).symm

/-- Transport the operator theorem to named source outputs. `hlocal` preserves
sender order; `hAA` specifies each destination's faithful producer output in
`Fin T` order on that same sender list. Neither premise assumes the desired
activation reconstruction. -/
theorem fw_embedding_dp_tp_position_unit_of_source_eqs
    (D u T B S V H : Nat)
    (fullIDs unitIDs W : Tensor) (idsShards : List Tensor)
    (globalOut : Tensor) (localOuts AAoutputs : List Tensor)
    (hD : 0 < D) (hu : u < D) (hT : 0 < T)
    (hB : 0 < B) (hS : 0 < S) (hV : 0 < V) (hH : 0 < H)
    (hids : fullIDs.shape = [B * D, S * T])
    (hW : W.shape = [V, H * T])
    (hunitIDs : unitIDs = chunkPrimDimN 0 D u fullIDs)
    (hlen : idsShards.length = T)
    (hshards : ∀ ids ∈ idsShards, ids.shape = [B, S])
    (hunitGather : unitIDs = allGatherPrimDimN 1 T 0 idsShards)
    (hglobal : globalOut = fw_embedding fullIDs W)
    (hlocal : List.Forall₂ (fun out ids => out = fw_embedding ids W)
      localOuts idsShards)
    (hAA : AAoutputs = List.ofFn (fun dst : Fin T =>
      AllToAllSourceFaithful.tensor T dst.val 1 2 localOuts)) :
    chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 2 T 0 AAoutputs := by
  have transport : ∀ {os xs : List Tensor},
      List.Forall₂ (fun out ids => out = fw_embedding ids W) os xs →
      os = xs.map (fun ids => fw_embedding ids W) := by
    intro os xs h
    induction h with
    | nil => rfl
    | cons heq hrest ih => exact congrArg₂ List.cons heq ih
  have houtputs : localOuts = idsShards.map (fun ids => fw_embedding ids W) :=
    transport hlocal
  rw [hglobal, hAA, houtputs]
  exact fw_embedding_dp_tp_position_unit D u T B S V H
    fullIDs unitIDs W idsShards hD hu hT hB hS hV hH
    hids hW hunitIDs hlen hshards hunitGather

#print axioms fw_embedding_dp_tp_position_unit
#print axioms fw_embedding_dp_tp_position_unit_of_source_eqs
end
end TrainVerify.Denote
