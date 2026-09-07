import denote.Denote

/-!
# Backward embedding over an arbitrary number of vocabulary shards

The weight list supplies the actual shard shapes. No restrictions on gradient
or id tensors (and no assumptions on weight values) are needed: both sides
accumulate the same id-indexed gradient sum at each global vocabulary row.
-/

namespace TrainVerify.Denote

/-- Vocabulary-parallel backward embedding, for any positive number of equally
shaped shards. Rank `r` accumulates the global vocabulary row `r * shard + i`
at its local row `i`; gathering the local gradients reconstructs the full one. -/
theorem bw_embedding_eq_allGather_offset_k
    (K shard hidden : Nat)
    (hK : 0 < K) (hshard : 0 < shard) (hhid : 0 < hidden)
    (g ids : Tensor) (ws : List Tensor)
    (hlen : ws.length = K)
    (hshapes : ∀ w ∈ ws, w.shape = [shard, hidden]) :
    bw_embedding g ids (allGatherPrimDimN 0 K 0 ws) =
      allGatherPrimDimN 0 K 0
        ((List.range K).map (fun r =>
          bw_embedding_offset (r * shard) g ids
            (ws.getD r (zeroTensor [shard, hidden])))) := by
  have hws_shape (r : Nat) (hr : r < K) :
      (ws.getD r (zeroTensor [shard, hidden])).shape = [shard, hidden] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hshapes _ (List.getElem_mem ..)
  have hws_head : (ws.head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    cases ws with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons w rest =>
      change w.shape = [shard, hidden]
      exact hshapes w (List.mem_cons_self ..)
  let pieces : List Tensor := (List.range K).map (fun r =>
    bw_embedding_offset (r * shard) g ids
      (ws.getD r (zeroTensor [shard, hidden])))
  have hpieces_len : pieces.length = K := by
    simp only [pieces, List.length_map, List.length_range]
  have hpieces_getD (r : Nat) (hr : r < K) :
      pieces.getD r (zeroTensor [shard, hidden]) =
        bw_embedding_offset (r * shard) g ids
          (ws.getD r (zeroTensor [shard, hidden])) := by
    change (((List.range K).map (fun s =>
      bw_embedding_offset (s * shard) g ids
        (ws.getD s (zeroTensor [shard, hidden])))).getD r
          (zeroTensor [shard, hidden])) = _
    have hrange : (List.range K)[r]? = some r := by
      rw [List.getElem?_eq_getElem (by simpa only [List.length_range] using hr),
        List.getElem_range]
    unfold List.getD
    rw [List.getElem?_map, hrange]
    rfl
  have hpieces_shape (r : Nat) (hr : r < K) :
      (pieces.getD r (zeroTensor [shard, hidden])).shape = [shard, hidden] := by
    rw [hpieces_getD r hr, bw_embedding_offset_shape]
    exact hws_shape r hr
  have hpieces_head :
      (pieces.head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    cases hp : pieces with
    | nil =>
      have hz : K = 0 := by
        simpa only [hp, List.length_nil] using hpieces_len.symm
      omega
    | cons p ps =>
      change p.shape = [shard, hidden]
      have hs := hpieces_shape 0 hK
      simpa only [hp, List.getD_cons_zero] using hs
  set fullW : Tensor := allGatherPrimDimN 0 K 0 ws
  have hfullW_shape : fullW.shape = [shard * K, hidden] := by
    have hs := allGatherPrimDimN_shape 0 K ws [shard, hidden] hws_head
    simpa using hs
  have hlastD_full : lastD fullW.shape = hidden := by
    rw [hfullW_shape]
    rfl
  have hlhs_shape : (bw_embedding g ids fullW).shape = [shard * K, hidden] := by
    rw [bw_embedding_shape]
    exact hfullW_shape
  have hrhs_shape : (allGatherPrimDimN 0 K 0 pieces).shape = [shard * K, hidden] := by
    have hs := allGatherPrimDimN_shape 0 K pieces [shard, hidden] hpieces_head
    simpa using hs
  change bw_embedding g ids fullW = allGatherPrimDimN 0 K 0 pieces
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  intro idx hout
  have hbound : idx < shard * K * hidden := by
    rw [hlhs_shape] at hout
    simpa only [prodShape, List.foldl, Nat.one_mul] using hout
  have hsh_pos : 0 < shard * hidden := Nat.mul_pos hshard hhid
  set r := idx / (shard * hidden)
  set rem := idx % (shard * hidden)
  set i := rem / hidden
  set j := rem % hidden
  have hr_lt : r < K := by
    have h : idx < (shard * hidden) * K := by
      have heq : shard * K * hidden = (shard * hidden) * K := by ring
      omega
    exact Nat.div_lt_of_lt_mul h
  have hrem_lt : rem < shard * hidden := Nat.mod_lt _ hsh_pos
  have hi_lt : i < shard := by
    have h : rem < hidden * shard := by
      have heq : shard * hidden = hidden * shard := by ring
      omega
    exact Nat.div_lt_of_lt_mul h
  have hj_lt : j < hidden := Nat.mod_lt _ hhid
  have hidx_eq : idx = (r * shard + i) * hidden + j := by
    have h1 : (shard * hidden) * r + rem = idx := Nat.div_add_mod idx (shard * hidden)
    have h2 : hidden * i + j = rem := Nat.div_add_mod rem hidden
    have h3 : (r * shard + i) * hidden + j =
        (shard * hidden) * r + (hidden * i + j) := by ring
    omega
  have hidx_prod : idx < prodShape fullW.shape := by
    rw [hfullW_shape]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  rw [bw_embedding_valAt g ids fullW idx hidx_prod]
  simp only [hlastD_full]
  have hag := allGatherPrimDimN0_valAt K shard hidden pieces
    hK hshard hhid hpieces_head hpieces_shape r hr_lt i hi_lt j hj_lt
  rw [hidx_eq, hag, hpieces_getD r hr_lt]
  have hi_hidden_bound : i * hidden + j < prodShape [shard, hidden] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    calc
      i * hidden + j < i * hidden + hidden := by omega
      _ = (i + 1) * hidden := by ring
      _ ≤ shard * hidden := Nat.mul_le_mul_right _ hi_lt
  have hWr_shape := hws_shape r hr_lt
  have hlastD_Wr : lastD (ws.getD r (zeroTensor [shard, hidden])).shape = hidden := by
    rw [hWr_shape]
    rfl
  rw [bw_embedding_offset_valAt (r * shard) g ids
    (ws.getD r (zeroTensor [shard, hidden])) (i * hidden + j)
    (by rw [hWr_shape]; exact hi_hidden_bound)]
  simp only [hlastD_Wr]
  have hlhs_div : ((r * shard + i) * hidden + j) / hidden = r * shard + i := by
    rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) by ring,
      Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
  have hrhs_div : (i * hidden + j) / hidden = i := by
    rw [show i * hidden + j = j + hidden * i by ring,
      Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
  have hlhs_mod : ((r * shard + i) * hidden + j) % hidden = j := by
    rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
  have hrhs_mod : (i * hidden + j) % hidden = j := by
    rw [show i * hidden + j = j + hidden * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
  simp only [hlhs_div, hrhs_div, hlhs_mod, hrhs_mod]

end TrainVerify.Denote
