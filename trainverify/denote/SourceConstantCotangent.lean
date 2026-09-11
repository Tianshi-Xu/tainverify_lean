import denote.AllToAllSourceFaithful
import denote.KRankLinearGather
import denote.EmbeddingHiddenShard

/-!
Constant cotangents through the actual chunk / ordered gather / faithful
split-then-gather kernels. The scalar is arbitrary, not a unit-loss seed.
These are mathematical components, not a whole-model backward theorem.
-/
namespace TrainVerify.Denote
noncomputable section

/-- A constant tensor, including its exact shape. -/
abbrev sourceConstantCotangent (sh : Shape) (c : Scalar) : Tensor :=
  Tensor.mkShape sh (fun _ => c)

theorem source_constant_valAt (sh : Shape) (c : Scalar) (i : Nat)
    (hi : i < prodShape sh) : valAt (sourceConstantCotangent sh c) i = c :=
  valAt_of_lt _ _ hi

/-- BW_sum broadcasts the actual seed value; no normalization or unit seed. -/
theorem source_constant_bw_sum (seed saved : Tensor) :
    bw_sum seed saved = sourceConstantCotangent saved.shape (valAt seed 0) := rfl

private theorem constant_flat_lt {a A b B : Nat} (ha : a < A) (hb : b < B) :
    a * B + b < A * B := by
  calc
    a * B + b < a * B + B := Nat.add_lt_add_left hb _
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B ha

private theorem constant_split_index (i A L : Nat) (hL : 0 < L)
    (hi : i < A * L) :
    ∃ a j : Nat, a < A ∧ j < L ∧ i = a * L + j := by
  refine ⟨i / L, i % L, ?_, Nat.mod_lt _ hL, ?_⟩
  · apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hi
  · simpa only [Nat.mul_comm] using (Nat.div_add_mod i L).symm

private theorem constant_head (K : Nat) (sh : Shape) (c : Scalar) (hK : 0 < K) :
    ((List.replicate K (sourceConstantCotangent sh c)).head?.map Tensor.shape).getD [] = sh := by
  cases K with
  | zero => omega
  | succ k => rfl

private theorem constant_getD (K r : Nat) (x fallback : Tensor) (hr : r < K) :
    (List.replicate K x).getD r fallback = x := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa only [List.length_replicate] using hr)]
  simp only [List.getElem_replicate, Option.getD_some]

/-- DP batch chunking preserves any constant cotangent. -/
theorem source_constant_chunk0_rank3
    (D B S O u : Nat) (c : Scalar)
    (hD : 0 < D) (hB : 0 < B) (hS : 0 < S) (hO : 0 < O) (hu : u < D) :
    chunkPrimDimN 0 D u (sourceConstantCotangent [B * D, S, O] c) =
      sourceConstantCotangent [B, S, O] c := by
  have hshape : (chunkPrimDimN 0 D u
      (sourceConstantCotangent [B * D, S, O] c)).shape = [B, S, O] := by
    rw [chunkPrimDimN_shape 0 D u _ [B * D, S, O] rfl hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  apply Tensor.ext
    (t1 := chunkPrimDimN 0 D u (sourceConstantCotangent [B * D, S, O] c))
    (t2 := sourceConstantCotangent [B, S, O] c) hshape
  intro i hi
  have hi' : i < B * (S * O) := by
    rw [hshape] at hi
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hi
  have hSO := Nat.mul_pos hS hO
  have hBSO := Nat.mul_pos hB hSO
  have hj : i / (S * O) < B := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hi'
  have hsrc : (u * B + i / (S * O)) * (S * O) + i % (S * O) <
      prodShape [B * D, S, O] := by
    have huj : u * B + i / (S * O) < B * D := by
      simpa only [Nat.mul_comm] using constant_flat_lt hu hj
    have h := constant_flat_lt huj (Nat.mod_lt i hSO)
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using h
  rw [source_constant_valAt [B, S, O] c i (by
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hi')]
  rw [valAt_of_lt _ _ hi]
  simp only [chunkPrimDimN, sourceConstantCotangent, Tensor.mkShape,
    List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hD.ne', ite_false, Nat.mul_div_cancel B hD, hSO.ne', hBSO.ne',
    Nat.mod_eq_of_lt hu, Nat.div_eq_of_lt hi', Nat.mod_eq_of_lt hi',
    Nat.zero_mul, Nat.zero_add]
  exact source_constant_valAt _ c _ hsrc

/-- Last-axis all-gather repeats the same arbitrary scalar in every TP shard. -/
theorem source_constant_gather2_rank3
    (K B S O : Nat) (c : Scalar)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hO : 0 < O) :
    allGatherPrimDimN 2 K 0 (List.replicate K (sourceConstantCotangent [B, S, O] c)) =
      sourceConstantCotangent [B, S, O * K] c := by
  have hh := constant_head K [B, S, O] c hK
  have hshape : (allGatherPrimDimN 2 K 0
      (List.replicate K (sourceConstantCotangent [B, S, O] c))).shape = [B, S, O * K] := by
    rw [allGatherPrimDimN_shape 2 K _ _ hh]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
  apply Tensor.ext
    (t1 := allGatherPrimDimN 2 K 0 (List.replicate K (sourceConstantCotangent [B, S, O] c)))
    (t2 := sourceConstantCotangent [B, S, O * K] c) hshape
  intro i hi
  have hi' : i < B * S * (O * K) := by
    rw [hshape] at hi
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  rw [source_constant_valAt [B, S, O * K] c i (by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi')]
  obtain ⟨row, q, hrow, hq, heq⟩ :=
    constant_split_index i (B * S) (O * K) (Nat.mul_pos hO hK) hi'
  obtain ⟨r, j, hr, hj, hqeq⟩ := constant_split_index q K O hO
    (by simpa only [Nat.mul_comm] using hq)
  rw [heq, hqeq, allGatherPrimDimN2_k_valAt K B S O _ hK hB hS hO hh
    row hrow r hr j hj, constant_getD K r _ _ hr]
  exact source_constant_valAt _ c _ (by
    simpa only [prodShape, List.foldl, Nat.one_mul] using constant_flat_lt hrow hj)

private theorem constant_chunk2_rank3
    (K B S O r : Nat) (c : Scalar)
    (hK : 0 < K) (hO : 0 < O) (hr : r < K) :
    chunkPrimDimN 2 K r (sourceConstantCotangent [B, S, O * K] c) =
      sourceConstantCotangent [B, S, O] c := by
  have hshape : (chunkPrimDimN 2 K r
      (sourceConstantCotangent [B, S, O * K] c)).shape = [B, S, O] := by
    rw [chunkPrimDimN_shape 2 K r _ [B, S, O * K] rfl hK.ne']
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero,
      Nat.mul_div_cancel O hK]
  apply Tensor.ext
    (t1 := chunkPrimDimN 2 K r (sourceConstantCotangent [B, S, O * K] c))
    (t2 := sourceConstantCotangent [B, S, O] c) hshape
  intro i hi
  have hi' : i < B * S * O := by
    rw [hshape] at hi
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  have hrow : i / O < B * S := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hi'
  have hj : r * O + i % O < O * K := by
    simpa only [Nat.mul_comm] using constant_flat_lt hr (Nat.mod_lt i hO)
  have hsrc : i / O * (O * K) + (r * O + i % O) < prodShape [B, S, O * K] := by
    simpa only [prodShape, List.foldl, Nat.one_mul] using constant_flat_lt hrow hj
  rw [source_constant_valAt [B, S, O] c i (by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi')]
  rw [valAt_of_lt _ _ hi]
  simp only [chunkPrimDimN, sourceConstantCotangent, Tensor.mkShape,
    List.getD_cons_succ, List.getD_cons_zero, List.drop, List.foldl,
    hK.ne', ite_false, Nat.mul_div_cancel O hK, Nat.mul_one, hO.ne',
    Nat.one_ne_zero, Nat.mod_eq_of_lt hr, Nat.div_one, Nat.mod_one, Nat.add_zero]
  exact source_constant_valAt _ c _ hsrc

private theorem constant_gather1_rank3
    (K B S O : Nat) (c : Scalar)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hO : 0 < O) :
    allGatherPrimDimN 1 K 0 (List.replicate K (sourceConstantCotangent [B, S, O] c)) =
      sourceConstantCotangent [B, S * K, O] c := by
  have hh := constant_head K [B, S, O] c hK
  have hshape : (allGatherPrimDimN 1 K 0
      (List.replicate K (sourceConstantCotangent [B, S, O] c))).shape = [B, S * K, O] := by
    rw [allGatherPrimDimN_shape 1 K _ _ hh]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
  apply Tensor.ext
    (t1 := allGatherPrimDimN 1 K 0 (List.replicate K (sourceConstantCotangent [B, S, O] c)))
    (t2 := sourceConstantCotangent [B, S * K, O] c) hshape
  intro i hi
  have hi' : i < B * (S * K) * O := by
    rw [hshape] at hi
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  rw [source_constant_valAt [B, S * K, O] c i (by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi')]
  obtain ⟨row, j, hrow, hj, heq⟩ := constant_split_index i (B * (S * K)) O hO hi'
  obtain ⟨b, q, hb, hq, hroweq⟩ :=
    constant_split_index row B (S * K) (Nat.mul_pos hS hK) hrow
  obtain ⟨r, s, hr, hs, hqeq⟩ := constant_split_index q K S hS
    (by simpa only [Nat.mul_comm] using hq)
  rw [heq, hroweq, hqeq, allGatherPrimDimN1_3d_valAt K B S O _ hK hB hS hO hh
    b hb r hr s hs j hj, constant_getD K r _ _ hr]
  exact source_constant_valAt _ c _ (by
    simpa only [prodShape, List.foldl, Nat.one_mul] using
      constant_flat_lt (constant_flat_lt hb hs) hj)

/-- Faithful AA(1,2): each sender splits hidden first, then the destination
concatenates the received pieces along sequence. No legacy AA is used. -/
theorem source_constant_alltoall12_rank3
    (K B S O r : Nat) (c : Scalar)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hO : 0 < O) (hr : r < K) :
    AllToAllSourceFaithful.tensor K r 1 2
        (List.replicate K (sourceConstantCotangent [B, S, O * K] c)) =
      sourceConstantCotangent [B, S * K, O] c := by
  unfold AllToAllSourceFaithful.tensor
  rw [List.map_replicate, constant_chunk2_rank3 K B S O r c hK hO hr]
  exact constant_gather1_rank3 K B S O c hK hB hS hO

#print axioms source_constant_valAt
#print axioms source_constant_bw_sum
#print axioms source_constant_chunk0_rank3
#print axioms source_constant_gather2_rank3
#print axioms source_constant_alltoall12_rank3

end
end TrainVerify.Denote
