import denote.AllToAllSourceFaithful
import denote.EmbeddingSequenceShard
import denote.KRankAllToAll
import denote.KRankLinearReduction

namespace TrainVerify.Denote.SourceEmbeddingExchange

noncomputable section
set_option maxHeartbeats 500000

/-- On a three-dimensional tensor, axis two is exactly the last axis.
This proves the primitive equivalence rather than silently replacing the
source split by the last-axis primitive used by the cancellation theorem. -/
theorem chunkPrimDimN_two_eq_chunkPrim
    (T rank b s d : Nat) (x : Tensor)
    (hT : 0 < T) (hx : x.shape = [b, s, d]) :
    chunkPrimDimN 2 T rank x = chunkPrim T rank x := by
  rcases x with ⟨sh, values⟩
  change sh = [b, s, d] at hx
  subst sh
  simp [chunkPrimDimN, chunkPrim, dropLast, lastD, appendLast,
    divNat, List.getLastD, Nat.ne_of_gt hT, Nat.add_assoc]
  rw [if_neg (Nat.ne_of_gt hT)]
  apply congrArg (Tensor.mkShape [b, s, d / T])
  funext idx
  simp only [Nat.mod_one, Nat.add_zero]

/-- The ordered hidden weight chunks have their actual source-derived shapes. -/
theorem weight_chunk_shape
    (T V H rank : Nat) (W : Tensor)
    (hT : 0 < T) (hW : W.shape = [V, H * T]) :
    (chunkPrimDimN 1 T rank W).shape = [V, H] := by
  rw [chunkPrimDimN_shape 1 T rank W [V, H * T] hW (Nat.ne_of_gt hT)]
  simp [List.set, List.getD, Nat.ne_of_gt hT]

/-- Reconstruct the full shared weight from its ordered hidden chunks. -/
theorem gather_weight_chunks
    (T V H : Nat) (W : Tensor)
    (hT : 0 < T) (hW : W.shape = [V, H * T]) :
    allGatherPrimDimN 1 T 0
      (List.ofFn fun r : Fin T => chunkPrimDimN 1 T r.val W) = W := by
  apply allGatherPrimDimN_chunks_ofFn 1 T W hT
  · rw [hW]
    change 1 < 2
    decide
  · simp [hW, List.getD]

/-- Hidden-axis splitting commutes with embedding.  The proof factors through
existing hidden-shard reconstruction and three-dimensional chunk/gather
cancellation; no new embedding index proof or value-sharding premise is used. -/
theorem chunk_embedding_hidden
    (T B S V H : Nat) (ids W : Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S)
    (hV : 0 < V) (hH : 0 < H)
    (hids : ids.shape = [B, S]) (hW : W.shape = [V, H * T]) :
    chunkPrimDimN 2 T dst.val (fw_embedding ids W) =
      fw_embedding ids (chunkPrimDimN 1 T dst.val W) := by
  let Ws := List.ofFn fun r : Fin T => chunkPrimDimN 1 T r.val W
  have hlen : Ws.length = T := by simp only [Ws, List.length_ofFn]
  have hWs : ∀ w ∈ Ws, w.shape = [V, H] := by
    intro w hw
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hw
    exact weight_chunk_shape T V H r.val W hT hW
  have hrec : allGatherPrimDimN 1 T 0 Ws = W :=
    gather_weight_chunks T V H W hT hW
  have hemb := fw_embedding_hidden_shards_k_rank T B S V H ids Ws
    hT hB hS hV hH hlen hids hWs
  rw [hrec] at hemb
  have hfull : (fw_embedding ids W).shape = [B, S, H * T] := by
    rw [fw_embedding_shape, hids, hW]
    rfl
  have hmapLen : (Ws.map (fun w => fw_embedding ids w)).length = T := by
    rw [List.length_map, hlen]
  have hmapShape : ∀ x ∈ Ws.map (fun w => fw_embedding ids w),
      x.shape = [B, S, H] := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    rw [fw_embedding_shape, hids, hWs w hw]
    rfl
  have hcancel := chunkPrim_allGatherPrimDimN_cancel_3d T dst.val B S H
    (Ws.map (fun w => fw_embedding ids w)) hmapLen hmapShape
    hT hB hS hH dst.isLt
  calc
    chunkPrimDimN 2 T dst.val (fw_embedding ids W) =
        chunkPrim T dst.val (fw_embedding ids W) :=
      chunkPrimDimN_two_eq_chunkPrim T dst.val B S (H * T)
        (fw_embedding ids W) hT hfull
    _ = (Ws.map (fun w => fw_embedding ids w)).get
        ⟨dst.val, by rw [hmapLen]; exact dst.isLt⟩ := by
      rw [hemb]
      exact hcancel
    _ = fw_embedding ids (chunkPrimDimN 1 T dst.val W) := by
      simp [Ws]

/-- Each faithful destination receives the full ordered sequence, embedded
with its own hidden weight chunk.  AllToAll is split-then-gather here. -/
theorem destination_embedding
    (T B S V H : Nat) (idsShards : List Tensor) (W : Tensor) (dst : Fin T)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S)
    (hV : 0 < V) (hH : 0 < H)
    (hlen : idsShards.length = T)
    (hids : ∀ ids ∈ idsShards, ids.shape = [B, S])
    (hW : W.shape = [V, H * T]) :
    AllToAllSourceFaithful.tensor T dst.val 1 2
        (idsShards.map (fun ids => fw_embedding ids W)) =
      fw_embedding (allGatherPrimDimN 1 T 0 idsShards)
        (chunkPrimDimN 1 T dst.val W) := by
  have hmap :
      (idsShards.map (fun ids => fw_embedding ids W)).map
          (chunkPrimDimN 2 T dst.val) =
        idsShards.map (fun ids =>
          fw_embedding ids (chunkPrimDimN 1 T dst.val W)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro ids hmem
    exact chunk_embedding_hidden T B S V H ids W dst
      hT hB hS hV hH (hids ids hmem) hW
  unfold AllToAllSourceFaithful.tensor
  rw [hmap]
  apply (fw_embedding_allGatherPrimDimN_dim1_shared_weight
    T B S H idsShards (chunkPrimDimN 1 T dst.val W)
    hT hB hS hH hlen hids ?_).symm
  rw [weight_chunk_shape T V H dst.val W hT hW]
  rfl

/-- Generic sequence-to-hidden embedding exchange for one ordered DP unit:
each sender embeds its [B,S] IDs using the full shared [V,H*T] weight,
faithful AllToAll splits hidden then gathers sequence, and the ordered
hidden gather reconstructs the embedding of the gathered IDs. -/
theorem embedding_sequence_to_hidden_exchange
    (T B S V H : Nat) (idsShards : List Tensor) (W : Tensor)
    (hT : 0 < T) (hB : 0 < B) (hS : 0 < S)
    (hV : 0 < V) (hH : 0 < H)
    (hlen : idsShards.length = T)
    (hids : ∀ ids ∈ idsShards, ids.shape = [B, S])
    (hW : W.shape = [V, H * T]) :
    allGatherPrimDimN 2 T 0
        (List.ofFn fun dst : Fin T =>
          AllToAllSourceFaithful.tensor T dst.val 1 2
            (idsShards.map (fun ids => fw_embedding ids W))) =
      fw_embedding (allGatherPrimDimN 1 T 0 idsShards) W := by
  let Ws := List.ofFn fun r : Fin T => chunkPrimDimN 1 T r.val W
  have hWlen : Ws.length = T := by simp only [Ws, List.length_ofFn]
  have hWs : ∀ w ∈ Ws, w.shape = [V, H] := by
    intro w hw
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hw
    exact weight_chunk_shape T V H r.val W hT hW
  have hhead : (idsShards.head?.map (fun t => t.shape)).getD [] = [B, S] := by
    cases heq : idsShards with
    | nil => simp only [heq, List.length_nil] at hlen; omega
    | cons ids rest =>
      simp only [List.head?, Option.map, Option.getD]
      exact hids ids (heq ▸ List.mem_cons_self ..)
  have hfullIds : (allGatherPrimDimN 1 T 0 idsShards).shape = [B, S * T] := by
    rw [allGatherPrimDimN_shape 1 T idsShards [B, S] hhead]
    simp [List.set, List.getD]
  have hrec : allGatherPrimDimN 1 T 0 Ws = W :=
    gather_weight_chunks T V H W hT hW
  have hemb := fw_embedding_hidden_shards_k_rank T B (S * T) V H
    (allGatherPrimDimN 1 T 0 idsShards) Ws
    hT hB (Nat.mul_pos hS hT) hV hH hWlen hfullIds hWs
  rw [hrec] at hemb
  have hdest :
      (List.ofFn fun dst : Fin T =>
        AllToAllSourceFaithful.tensor T dst.val 1 2
          (idsShards.map (fun ids => fw_embedding ids W))) =
      Ws.map (fun w => fw_embedding (allGatherPrimDimN 1 T 0 idsShards) w) := by
    dsimp only [Ws]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext dst
    exact destination_embedding T B S V H idsShards W dst
      hT hB hS hV hH hlen hids hW
  rw [hdest]
  exact hemb.symm

#print axioms chunkPrimDimN_two_eq_chunkPrim
#print axioms chunk_embedding_hidden
#print axioms destination_embedding
#print axioms embedding_sequence_to_hidden_exchange

end
end TrainVerify.Denote.SourceEmbeddingExchange
