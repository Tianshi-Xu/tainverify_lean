/- Generic last-dimension shard extraction for row-parallel linear reductions. -/
import denote.Denote

open TrainVerify.Denote

namespace TrainVerify.Denote

set_option maxHeartbeats 500000 in
theorem chunkPrim_allGatherPrimDimN_cancel_2d
    (numParts rank b shard : Nat) (xs : List Tensor)
    (hlen : xs.length = numParts)
    (hshapes : ∀ x ∈ xs, x.shape = [b, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard) (hrank : rank < numParts) :
    chunkPrim numParts rank (allGatherPrimDimN 1 numParts 0 xs) =
      xs.get ⟨rank, by omega⟩ := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, shard] := by
    match xs with
    | [] => simp at hlen; omega
    | x0 :: rest =>
      simpa using hshapes x0 (by simp)
  have hgatherEq := allGatherPrimDimN_1_eq_allGatherPrim_2d
    numParts xs b shard hhead hshard hparts
  rw [hgatherEq]
  have hgatherShape : (allGatherPrim numParts 0 xs).shape = [b, numParts * shard] := by
    simpa [Nat.mul_comm] using allGatherPrim_shape numParts b shard xs hhead
  have hchunkShape : (chunkPrim numParts rank (allGatherPrim numParts 0 xs)).shape =
      [b, shard] :=
    chunkPrim_shape' numParts rank b shard _ hgatherShape hparts
  have hresultShape : (xs.get ⟨rank, by omega⟩).shape = [b, shard] :=
    hshapes _ (List.get_mem xs ⟨rank, by omega⟩)
  apply Tensor.ext (by rw [hchunkShape, hresultShape])
  intro idx hidx
  rw [hchunkShape] at hidx
  have hidxBound : idx < b * shard := by simpa [prodShape] using hidx
  let p := idx / shard
  let j := idx % shard
  have hp : p < b := by
    dsimp [p]
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hidxBound)
  have hj : j < shard := by
    dsimp [j]
    exact Nat.mod_lt _ hshard
  have hidxEq : idx = p * shard + j := by
    dsimp [p, j]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod idx shard).symm
  rw [hidxEq]
  rw [chunkPrim_valAt_mul_add numParts rank b shard _ hgatherShape hparts hrank p hp j hj]
  have hGather := allGatherPrim_valAt_mul_add numParts rank b shard xs hhead
    hparts hrank p hp j hj
  rw [show p * (numParts * shard) + rank * shard + j =
    p * (shard * numParts) + rank * shard + j by ring]
  rw [hGather]
  have hrankLen : rank < xs.length := by omega
  simp [List.getD, List.getElem?_eq_getElem hrankLen]

set_option maxHeartbeats 500000 in
theorem allGatherPrimDimN_2_eq_allGatherPrim_3d
    (numParts b s shard : Nat) (xs : List Tensor)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, shard])
    (hb : 0 < b) (hs : 0 < s) (hshard : 0 < shard) (hparts : 0 < numParts) :
    allGatherPrimDimN 2 numParts 0 xs = allGatherPrim numParts 0 xs := by
  have hshapeL : (allGatherPrimDimN 2 numParts 0 xs).shape =
      [b, s, shard * numParts] := by
    rw [allGatherPrimDimN_shape 2 numParts xs [b, s, shard] hhead]
    simp [List.set, List.getD]
  have hshapeR : (allGatherPrim numParts 0 xs).shape =
      [b, s, shard * numParts] := by
    simp [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast]
  apply Tensor.ext (by rw [hshapeL, hshapeR])
  intro idx hidx
  have hfull : 0 < shard * numParts := Nat.mul_pos hshard hparts
  rw [hshapeL] at hidx
  have hltL : idx < prodShape (allGatherPrimDimN 2 numParts 0 xs).shape := by
    rw [hshapeL]
    simpa using hidx
  have hltR : idx < prodShape (allGatherPrim numParts 0 xs).shape := by
    rw [hshapeR]
    simpa using hidx
  rw [valAt_of_lt _ _ hltL, valAt_of_lt _ _ hltR]
  simp only [allGatherPrimDimN, allGatherPrim, Tensor.mkShape, hhead,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set, dropLast, lastD, appendLast,
    Nat.mul_one, Nat.add_zero, Nat.div_one, Nat.mod_one,
    show shard ≠ 0 from Nat.ne_of_gt hshard,
    show shard * numParts ≠ 0 from Nat.ne_of_gt hfull,
    show s ≠ 0 from Nat.ne_of_gt hs,
    show b ≠ 0 from Nat.ne_of_gt hb,
    show (1 : Nat) ≠ 0 from by omega, ite_false,
    show ([b, s, shard] : List Nat).getLastD 0 = shard from by simp [List.getLastD],
    show ([b, s, shard] : List Nat).dropLast = [b, s] from by simp [List.dropLast]]
  simp only [List.cons_append, List.nil_append]

set_option maxHeartbeats 500000 in
theorem allGatherPrim_valAt_mul_add_3d
    (numParts rank b s shard : Nat) (pieces : List Tensor)
    (hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, s, shard])
    (hparts : 0 < numParts) (hrank : rank < numParts)
    (p : Nat) (hp : p < b * s) (j : Nat) (hj : j < shard) :
    valAt (allGatherPrim numParts 0 pieces)
        (p * (shard * numParts) + rank * shard + j) =
      valAt (pieces.getD rank (zeroTensor [b, s, shard])) (p * shard + j) := by
  have hshardPos : 0 < shard := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hfullPos : 0 < shard * numParts := Nat.mul_pos hshardPos hparts
  have hrem : rank * shard + j < shard * numParts := by
    have h1 : rank * shard + j < rank * shard + shard :=
      Nat.add_lt_add_left hj _
    have h2 : rank * shard + shard = (rank + 1) * shard := by ring
    have h3 : (rank + 1) * shard ≤ numParts * shard :=
      Nat.mul_le_mul_right shard (Nat.succ_le_of_lt hrank)
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (by simpa [Nat.mul_comm] using h3)
  have hflat : p * (shard * numParts) + rank * shard + j <
      b * s * (shard * numParts) := by
    have h1 : p * (shard * numParts) + rank * shard + j <
        p * (shard * numParts) + shard * numParts :=
      by simpa [Nat.add_assoc] using Nat.add_lt_add_left hrem (p * (shard * numParts))
    have h2 : p * (shard * numParts) + shard * numParts =
        (p + 1) * (shard * numParts) := by ring
    have h3 : (p + 1) * (shard * numParts) ≤
        (b * s) * (shard * numParts) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hp)
    rw [h2] at h1
    exact lt_of_lt_of_le h1 h3
  have hshape : (allGatherPrim numParts 0 pieces).shape =
      [b, s, shard * numParts] := by
    simp [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast]
  have hout : p * (shard * numParts) + rank * shard + j <
      prodShape (allGatherPrim numParts 0 pieces).shape := by
    rw [hshape]
    simpa [prodShape, Nat.mul_assoc] using hflat
  rw [valAt_of_lt _ _ hout]
  have hdivFull : (p * (shard * numParts) + rank * shard + j) /
      (shard * numParts) = p := by
    have heq : (rank * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + rank * shard + j := by ring
    exact (Nat.div_mod_unique hfullPos).2 ⟨heq, hrem⟩ |>.1
  have hmodFull : (p * (shard * numParts) + rank * shard + j) %
      (shard * numParts) = rank * shard + j := by
    rw [show p * (shard * numParts) + rank * shard + j =
      (rank * shard + j) + p * (shard * numParts) by ring]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
  have hdivShard : (rank * shard + j) / shard = rank := by
    rw [show rank * shard + j = j + rank * shard by omega]
    rw [Nat.add_mul_div_right _ _ hshardPos, Nat.div_eq_of_lt hj,
      Nat.zero_add]
  have hmodShard : (rank * shard + j) % shard = j := by
    rw [show rank * shard + j = j + rank * shard by omega]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast,
    show ([b, s, shard] : List Nat).getLastD 0 = shard by simp [List.getLastD],
    show ([b, s, shard] : List Nat).dropLast = [b, s] by simp [List.dropLast],
    Nat.ne_of_gt hshardPos, Nat.ne_of_gt hfullPos, ite_false,
    hdivFull, hmodFull, hdivShard, hmodShard]
  congr 1

set_option maxHeartbeats 500000 in
theorem chunkPrim_allGatherPrimDimN_cancel_3d
    (numParts rank b s shard : Nat) (xs : List Tensor)
    (hlen : xs.length = numParts)
    (hshapes : ∀ x ∈ xs, x.shape = [b, s, shard])
    (hparts : 0 < numParts) (hb : 0 < b) (hs : 0 < s)
    (hshard : 0 < shard) (hrank : rank < numParts) :
    chunkPrim numParts rank (allGatherPrimDimN 2 numParts 0 xs) =
      xs.get ⟨rank, by omega⟩ := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, shard] := by
    match xs with
    | [] => simp at hlen; omega
    | x0 :: rest => simpa using hshapes x0 (by simp)
  rw [allGatherPrimDimN_2_eq_allGatherPrim_3d numParts b s shard xs
    hhead hb hs hshard hparts]
  have hgatherShape : (allGatherPrim numParts 0 xs).shape =
      [b, s, numParts * shard] := by
    simp only [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast,
      show ([b, s, shard] : List Nat).getLastD 0 = shard by simp [List.getLastD],
      show ([b, s, shard] : List Nat).dropLast = [b, s] by simp [List.dropLast]]
    simp only [List.cons_append, List.nil_append]
    rw [Nat.mul_comm]
  have hchunkShape : (chunkPrim numParts rank (allGatherPrim numParts 0 xs)).shape =
      [b, s, shard] := by
    simp [chunkPrim, Tensor.mkShape, hgatherShape, dropLast, lastD, appendLast,
      divNat, Nat.ne_of_gt hparts]
  have hresultShape : (xs.get ⟨rank, by omega⟩).shape = [b, s, shard] :=
    hshapes _ (List.get_mem xs ⟨rank, by omega⟩)
  apply Tensor.ext (by rw [hchunkShape, hresultShape])
  intro idx hidx
  rw [hchunkShape] at hidx
  have hidxBound : idx < b * s * shard := by simpa [prodShape] using hidx
  let p := idx / shard
  let j := idx % shard
  have hp : p < b * s := by
    dsimp [p]
    apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hidxBound
  have hj : j < shard := by
    dsimp [j]
    exact Nat.mod_lt _ hshard
  have hidxEq : idx = p * shard + j := by
    dsimp [p, j]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod idx shard).symm
  rw [hidxEq]
  rw [chunkPrim_valAt_mul_add_3d numParts rank b s shard _ hgatherShape
    hparts hrank p hp j hj]
  have hGatherVal := allGatherPrim_valAt_mul_add_3d numParts rank b s shard xs
    hhead hparts hrank p hp j hj
  rw [show p * (numParts * shard) + rank * shard + j =
    p * (shard * numParts) + rank * shard + j by ring]
  rw [hGatherVal]
  have hrankLen : rank < xs.length := by omega
  simp [List.getD, List.getElem?_eq_getElem hrankLen]

end TrainVerify.Denote
