import denote.EmbeddingHiddenShard
import denote.KRankLayernormGather

namespace TrainVerify.Denote

noncomputable section

/-- Embedding with one shared weight commutes with an ordered dynamic-rank
sequence-axis gather.  The theorem is independent of model dimensions, graph
node IDs, and rank count. -/
theorem fw_embedding_allGatherPrimDimN_dim1_shared_weight
    (K b s hidden : Nat) (idsShards : List Tensor) (weight : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hhidden : 0 < hidden)
    (hlen : idsShards.length = K)
    (hids : ∀ ids ∈ idsShards, ids.shape = [b, s])
    (hweight : lastD weight.shape = hidden) :
    fw_embedding (allGatherPrimDimN 1 K 0 idsShards) weight =
      allGatherPrimDimN 1 K 0
        (idsShards.map (fun ids => fw_embedding ids weight)) := by
  obtain ⟨ids0, rest, hlist⟩ := List.exists_cons_of_ne_nil
    (by intro hempty; rw [hempty] at hlen; simp at hlen; omega : idsShards ≠ [])
  subst idsShards
  have hhead :
      ((((ids0 :: rest).head?).map (fun t => t.shape)).getD []) = [b, s] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hids ids0 (by simp)
  have hfullIds :
      (allGatherPrimDimN 1 K 0 (ids0 :: rest)).shape = [b, s * K] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, s] hhead]
    simp [List.set, List.getD]
  have hmapHead :
      (((((ids0 :: rest).map (fun x => fw_embedding x weight)).head?).map
        (fun t => t.shape)).getD []) = [b, s, hidden] := by
    simp only [List.map, List.head?, Option.map, Option.getD]
    rw [fw_embedding_shape, hids ids0 (by simp), hweight]
    rfl
  have hlhsShape :
      (fw_embedding (allGatherPrimDimN 1 K 0 (ids0 :: rest)) weight).shape =
        [b, s * K, hidden] := by
    rw [fw_embedding_shape, hfullIds, hweight]
    rfl
  have hrhsShape :
      (allGatherPrimDimN 1 K 0
        ((ids0 :: rest).map (fun x => fw_embedding x weight))).shape =
        [b, s * K, hidden] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, s, hidden] hmapHead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hlhsShape, hrhsShape]
  · intro idx hidx
    have hidxBound : idx < b * (s * K) * hidden := by
      rw [hlhsShape] at hidx
      simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hidx
    set j := idx % hidden with hjDef
    set row := idx / hidden with hrowDef
    have hj : j < hidden := by rw [hjDef]; exact Nat.mod_lt _ hhidden
    have hrow : row < b * (s * K) := by
      rw [hrowDef, Nat.div_lt_iff_lt_mul hhidden]
      simpa [Nat.mul_assoc] using hidxBound
    set q := row / (s * K) with hqDef
    set g := row % (s * K) with hgDef
    have hSK : 0 < s * K := Nat.mul_pos hs hK
    have hq : q < b := by
      rw [hqDef, Nat.div_lt_iff_lt_mul hSK]
      exact hrow
    have hg : g < s * K := by rw [hgDef]; exact Nat.mod_lt _ hSK
    set r := g / s with hrDef
    set p := g % s with hpDef
    have hr : r < K := by
      rw [hrDef, Nat.div_lt_iff_lt_mul hs]
      simpa only [Nat.mul_comm] using hg
    have hp : p < s := by rw [hpDef]; exact Nat.mod_lt _ hs
    have hrowEq : row = q * (s * K) + (r * s + p) := by
      have h1 := (Nat.div_add_mod row (s * K)).symm
      have h2 := (Nat.div_add_mod g s).symm
      rw [← hqDef, ← hgDef] at h1
      rw [← hrDef, ← hpDef] at h2
      calc
        row = s * K * q + g := h1
        _ = q * (s * K) + g := by ring
        _ = q * (s * K) + (r * s + p) := by rw [h2]; ring
    have hidxEq : idx = (q * (s * K) + (r * s + p)) * hidden + j := by
      have h := (Nat.div_add_mod idx hidden).symm
      rw [← hrowDef, ← hjDef] at h
      calc
        idx = hidden * row + j := h
        _ = row * hidden + j := by ring
        _ = (q * (s * K) + (r * s + p)) * hidden + j := by rw [hrowEq]
    rw [hidxEq] at hidxBound
    rw [hidxEq]
    have hfullBound :
        (q * (s * K) + (r * s + p)) * hidden + j <
          prodShape ((allGatherPrimDimN 1 K 0 (ids0 :: rest)).shape ++
            [lastD weight.shape]) := by
      rw [hfullIds, hweight]
      simpa [prodShape, Nat.mul_assoc] using hidxBound
    rw [fw_embedding_valAt, dif_pos hfullBound]
    have hdivFull :
        ((q * (s * K) + (r * s + p)) * hidden + j) / hidden =
          q * (s * K) + (r * s + p) := by
      rw [show (q * (s * K) + (r * s + p)) * hidden + j =
          j + hidden * (q * (s * K) + (r * s + p)) by ring,
        Nat.add_mul_div_left _ _ hhidden, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmodFull :
        ((q * (s * K) + (r * s + p)) * hidden + j) % hidden = j := by
      rw [show (q * (s * K) + (r * s + p)) * hidden + j =
          j + hidden * (q * (s * K) + (r * s + p)) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [hweight, hdivFull, hmodFull]
    rw [allGatherPrimDimN_dim1_3d_valAt
      ((ids0 :: rest).map (fun x => fw_embedding x weight)) K b s hidden
      q r p j hK hs hhidden hq hr hp hj hmapHead]
    have hrLen : r < (ids0 :: rest).length := by omega
    have hidsGet : ((ids0 :: rest).getD r (zeroTensor [b, s])).shape = [b, s] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrLen]
      simp only [Option.getD_some]
      exact hids ((ids0 :: rest)[r]) (List.getElem_mem hrLen)
    have hmapGet :
        ((ids0 :: rest).map (fun x => fw_embedding x weight)).getD r
            (zeroTensor [b, s, hidden]) =
          fw_embedding ((ids0 :: rest).getD r (zeroTensor [b, s])) weight := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hrLen, Option.map_some, Option.getD_some]
    rw [hmapGet, fw_embedding_valAt]
    have hlocalBound :
        (q * s + p) * hidden + j <
          prodShape (((ids0 :: rest).getD r (zeroTensor [b, s])).shape ++
            [lastD weight.shape]) := by
      rw [hidsGet, hweight]
      have hqp : q * s + p < b * s := by
        have hq1 : q + 1 ≤ b := Nat.succ_le_iff.mpr hq
        calc
          q * s + p < (q + 1) * s := by rw [Nat.add_mul]; omega
          _ ≤ b * s := Nat.mul_le_mul_right s hq1
      simpa [prodShape, Nat.mul_assoc] using show
        (q * s + p) * hidden + j < b * s * hidden by
          calc
            (q * s + p) * hidden + j < (q * s + p) * hidden + hidden :=
              Nat.add_lt_add_left hj _
            _ = (q * s + p + 1) * hidden := by ring
            _ ≤ (b * s) * hidden :=
              Nat.mul_le_mul_right hidden (Nat.succ_le_iff.mpr hqp)
    rw [dif_pos hlocalBound, hweight]
    have hdivLocal : ((q * s + p) * hidden + j) / hidden = q * s + p := by
      rw [show (q * s + p) * hidden + j = j + hidden * (q * s + p) by ring,
        Nat.add_mul_div_left _ _ hhidden, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmodLocal : ((q * s + p) * hidden + j) % hidden = j := by
      rw [show (q * s + p) * hidden + j = j + hidden * (q * s + p) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [hdivLocal, hmodLocal]
    rw [allGatherPrimDimN1_k_valAt K b s (ids0 :: rest)
      hK hb hs hhead q hq r hr p hp]

end

end TrainVerify.Denote
