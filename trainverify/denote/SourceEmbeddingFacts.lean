import denote.SourceEmbeddingUnit
import denote.SourceEmbeddingPositionUnit

/-!
# Shared source embedding output facts

Additive adapters with exactly the existing source-equality contracts. Shapes
come from original IDs, weights and producer equations; the final component
reuses the existing value theorem. Consumers can project these facts instead of
replaying source-read and shape derivations. UNCOMPILED: parent kernel audit
required; no source-indexed constants or legacy exchange semantics are used.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem embeddingFacts_transport (f : Tensor → Tensor)
    {os xs : List Tensor} (h : List.Forall₂ (fun out x => out = f x) os xs) :
    os = xs.map f := by
  induction h with
  | nil => rfl
  | cons heq hrest ih => exact congrArg₂ List.cons heq ih

/-- Direct hidden-shard embedding: full shape, local shapes, then unit value. -/
theorem fw_embedding_dp_tp_unit_facts_of_source_eqs
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
    globalOut.shape = [B * D, S, H * T] ∧
    (∀ x ∈ unitOuts, x.shape = [B, S, H]) ∧
    chunkPrimDimN 0 D unit globalOut = allGatherPrimDimN 2 T 0 unitOuts := by
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
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal, fw_embedding_shape, hids, hweightShape]
    rfl
  · have houtputs := embeddingFacts_transport (fun W => fw_embedding unitIDs W) hlocal
    rw [houtputs]
    intro x hx
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
    rw [fw_embedding_shape, hunitShape, hWs W hW]
    rfl
  · exact fw_embedding_dp_tp_unit_of_source_eqs D unit T B S V H
      fullIDs unitIDs fullWeight Ws globalOut unitOuts
      hD hu hT hB hS hV hH hids hunitIDs hlen hWs hfullWeight hglobal hlocal

/-- Position embedding: shapes of faithful AA destinations, not sender outputs. -/
theorem fw_embedding_dp_tp_position_unit_facts_of_source_eqs
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
    globalOut.shape = [B * D, S * T, H * T] ∧
    (∀ x ∈ AAoutputs, x.shape = [B, S * T, H]) ∧
    chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 2 T 0 AAoutputs := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal, fw_embedding_shape, hids, hW]
    rfl
  · have houtputs := embeddingFacts_transport (fun ids => fw_embedding ids W) hlocal
    rw [hAA]
    intro x hx
    obtain ⟨dst, rfl⟩ := List.mem_ofFn.mp hx
    rw [houtputs]
    cases idsShards with
    | nil => exact (hT.ne' hlen.symm).elim
    | cons ids rest =>
      rw [List.map_cons,
        AllToAllSourceFaithful.tensor_shape T dst.val 1 2 (fw_embedding ids W)
          (rest.map (fun ids => fw_embedding ids W)) hT.ne',
        fw_embedding_shape, hshards ids (List.mem_cons_self ..), hW]
      change [B, S * T, H * T / T] = [B, S * T, H]
      rw [Nat.mul_div_cancel H hT]
  · exact fw_embedding_dp_tp_position_unit_of_source_eqs D u T B S V H
      fullIDs unitIDs W idsShards globalOut localOuts AAoutputs
      hD hu hT hB hS hV hH hids hW hunitIDs hlen hshards hunitGather hglobal hlocal hAA

#print axioms fw_embedding_dp_tp_unit_facts_of_source_eqs
#print axioms fw_embedding_dp_tp_position_unit_facts_of_source_eqs
end
end TrainVerify.Denote
