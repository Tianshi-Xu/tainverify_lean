import denote.SourceEmbeddingBatch
import denote.EmbeddingHiddenShard

/-!
# Source embedding: one DP batch unit, ordered TP hidden shards

UNCOMPILED CANDIDATE: compilation and kernel/axiom audit belong to the parent
serial builder. This module only composes the existing batch-chunk and
hidden-shard embedding theorems; it does not change source primitives.

`Ws` is the ordered TP weight list for ONE DP unit. Its positions determine
gather order; physical rank labels may be arbitrary. Never concatenate the TP
lists of distinct DP units into this gather. For the current source instance,
use D = 2, T = 2, B = 1, S = 16, H = 32 (and the source vocabulary size V).

The input contract consists only of positive dimensions, unit bounds, the full
IDs shape, the unit IDs chunk equation, and the ordered weight reconstruction
with shard length/shapes. Local IDs and full weight shapes are derived, not
additional premises. There is no label-domain or desired-output premise:
`scalarToNat` and out-of-range/default reads retain their existing semantics.
Source use is ordinary embedding (start = 0, stop = vocab), not offset or
vocabulary-sharded embedding.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

/-- Constructor-friendly unit value coupling: chunk the global batch output,
then reconstruct exactly one unit's ordered TP hidden outputs. -/
theorem fw_embedding_dp_tp_unit
    (D unit T B S V H : Nat)
    (fullIDs unitIDs fullWeight : Tensor) (Ws : List Tensor)
    (hD : 0 < D) (hu : unit < D) (hT : 0 < T)
    (hB : 0 < B) (hS : 0 < S) (hV : 0 < V) (hH : 0 < H)
    (hids : fullIDs.shape = [B * D, S])
    (hunitIDs : unitIDs = chunkPrimDimN 0 D unit fullIDs)
    (hlen : Ws.length = T)
    (hWs : ∀ W ∈ Ws, W.shape = [V, H])
    (hfullWeight : fullWeight = allGatherPrimDimN 1 T 0 Ws) :
    chunkPrimDimN 0 D unit (fw_embedding fullIDs fullWeight) =
      allGatherPrimDimN 2 T 0 (Ws.map (fun W => fw_embedding unitIDs W)) := by
  have hunitShape : unitIDs.shape = [B, S] := by
    rw [hunitIDs, chunkPrimDimN_shape 0 D unit fullIDs _ hids hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [V, H] := by
    cases Ws with
    | nil => exact (hT.ne' hlen.symm).elim
    | cons W rest => exact hWs W (List.mem_cons_self ..)
  have hweightShape : fullWeight.shape = [V, H * T] := by
    rw [hfullWeight, allGatherPrimDimN_shape 1 T Ws [V, H] hhead]
    rfl
  calc
    chunkPrimDimN 0 D unit (fw_embedding fullIDs fullWeight) =
        fw_embedding unitIDs fullWeight :=
      (fw_embedding_batch_chunk_dim0 D unit B S V (H * T)
        fullIDs unitIDs fullWeight hD hu hS (Nat.mul_pos hH hT)
        hids hweightShape hunitIDs).symm
    _ = fw_embedding unitIDs (allGatherPrimDimN 1 T 0 Ws) :=
      congrArg (fw_embedding unitIDs) hfullWeight
    _ = allGatherPrimDimN 2 T 0 (Ws.map (fun W => fw_embedding unitIDs W)) :=
      fw_embedding_hidden_shards_k_rank T B S V H unitIDs Ws
        hT hB hS hV hH hlen hunitShape hWs

/-- Transport unit coupling to named source output tensors. `hglobal` and each
constructor of `hlocal` are individual SOURCE embedding producer equations,
not an assumed global/local output reconstruction. For a generated finite TP
list, discharge `hlocal` with `List.Forall₂.cons` per producer and `.nil`.
Tensor arguments may be final-store reads; this adapter does not assume or
supply operand liveness or a whole-graph SM/PM equality. -/
theorem fw_embedding_dp_tp_unit_of_source_eqs
    (D unit T B S V H : Nat)
    (fullIDs unitIDs fullWeight : Tensor) (Ws : List Tensor)
    (globalOut : Tensor) (unitOuts : List Tensor)
    (hD : 0 < D) (hu : unit < D) (hT : 0 < T)
    (hB : 0 < B) (hS : 0 < S) (hV : 0 < V) (hH : 0 < H)
    (hids : fullIDs.shape = [B * D, S])
    (hunitIDs : unitIDs = chunkPrimDimN 0 D unit fullIDs)
    (hlen : Ws.length = T)
    (hWs : ∀ W ∈ Ws, W.shape = [V, H])
    (hfullWeight : fullWeight = allGatherPrimDimN 1 T 0 Ws)
    (hglobal : globalOut = fw_embedding fullIDs fullWeight)
    (hlocal : List.Forall₂ (fun out W => out = fw_embedding unitIDs W)
      unitOuts Ws) :
    chunkPrimDimN 0 D unit globalOut = allGatherPrimDimN 2 T 0 unitOuts := by
  have transport : ∀ {os ws : List Tensor},
      List.Forall₂ (fun out W => out = fw_embedding unitIDs W) os ws →
      os = ws.map (fun W => fw_embedding unitIDs W) := by
    intro os ws h
    induction h with
    | nil => rfl
    | cons heq hrest ih => exact congrArg₂ List.cons heq ih
  have houtputs : unitOuts = Ws.map (fun W => fw_embedding unitIDs W) := transport hlocal
  rw [hglobal, houtputs]
  exact fw_embedding_dp_tp_unit D unit T B S V H fullIDs unitIDs fullWeight Ws
    hD hu hT hB hS hV hH hids hunitIDs hlen hWs hfullWeight

#print axioms fw_embedding_dp_tp_unit
#print axioms fw_embedding_dp_tp_unit_of_source_eqs
end
end TrainVerify.Denote
