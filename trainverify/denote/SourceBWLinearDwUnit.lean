import denote.KRankBWLinearDwSequenceGeneral

/-!
# Batch-DP dW adapter

Contiguous dimension-0 shards are viewed as `[1,B*S,H]` and passed to the
existing arbitrary-K sequence reduction. No new summation interchange is
proved here. Both G and saved X are reconstructed as actual tensors; unlike
dX, saved-X values cannot be replaced by a shape-only witness. W is shared
with shape `[O,I]`; its values do not enter dW. TP output-O row sharding is
orthogonal and may be composed by the caller using KRankBWLinearDwRow.

Edit-only candidate: parent owns compilation and kernel auditing.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem dw_view_read (sh : Shape) (x : Tensor)
    (hp : prodShape sh = prodShape x.shape) (j : Nat) :
    valAt (fw_view sh x) j = valAt x j := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  split <;> split <;> simp_all

/-- dW depends only on the flattened rows of G and saved X, with the same
row count and output layout. These premises preserve values, not just shapes. -/
theorem source_bw_linear_dw_flat_rows
    (B S B' S' O I : Nat) (g x g' x' w : Tensor)
    (hg : g.shape = [B,S,O]) (hx : x.shape = [B,S,I])
    (hg' : g'.shape = [B',S',O]) (hx' : x'.shape = [B',S',I])
    (hw : w.shape = [O,I]) (hrows : B*S = B'*S')
    (hgradient : ∀ j, valAt g j = valAt g' j)
    (hsaved : ∀ j, valAt x j = valAt x' j) :
    (bw_linear g x w).2 = (bw_linear g' x' w).2 := by
  rw [bw_linear_dw_eq3d g x w B S O I hg hx hw,
    bw_linear_dw_eq3d g' x' w B' S' O I hg' hx' hw, hrows]
  refine Tensor.ext (t1 := _) (t2 := _) ?_ ?_
  · rfl
  · intro j hj
    rw [valAt_of_lt (Tensor.mkShape [O,I] (k_matmul_transpose (B'*S') O I g x)) j hj,
      valAt_of_lt (Tensor.mkShape [O,I] (k_matmul_transpose (B'*S') O I g' x')) j hj]
    simp only [Tensor.mkShape, k_matmul_transpose]
    apply Finset.sum_congr rfl
    intro r _
    rw [hgradient, hsaved]

private theorem dw_view_rows (B S O I : Nat) (g x w : Tensor)
    (hg : g.shape = [B,S,O]) (hx : x.shape = [B,S,I])
    (hw : w.shape = [O,I]) :
    (bw_linear g x w).2 =
      (bw_linear (fw_view [1,B*S,O] g) (fw_view [1,B*S,I] x) w).2 := by
  apply source_bw_linear_dw_flat_rows B S 1 (B*S) O I g x _ _ w
    hg hx rfl rfl hw (Nat.one_mul _).symm
  · intro j
    symm
    apply dw_view_read
    rw [hg]
    simp only [prodShape, List.foldl, Nat.one_mul]
  · intro j
    symm
    apply dw_view_read
    rw [hx]
    simp only [prodShape, List.foldl, Nat.one_mul]

private theorem dw_map_read (B S H : Nat) (ts : List Tensor) (r j : Nat)
    (hsh : ∀ t ∈ ts, t.shape = [B,S,H]) :
    valAt ((ts.map (fw_view [1,B*S,H])).getD r (zeroTensor [1,B*S,H])) j =
      valAt (ts.getD r (zeroTensor [B,S,H])) j := by
  induction ts generalizing r with
  | nil => simp [List.getD, valAt, zeroTensor, Tensor.mkShape]
  | cons t ts ih =>
    cases r with
    | zero =>
      simp only [List.map, List.getD, List.getElem?_cons_zero, Option.getD_some]
      apply dw_view_read
      rw [hsh t (List.mem_cons_self ..)]
      simp only [prodShape, List.foldl, Nat.one_mul]
    | succ r =>
      simpa only [List.map, List.getD, List.getElem?_cons_succ] using
        ih r (fun t ht => hsh t (List.mem_cons_of_mem _ ht))

-- Batch gather is flat concatenation; sequence gather with batch=1 is the
-- same concatenation after viewing each shard. Only quotient/remainder
-- identities are needed, not a second reduction proof.
private theorem dw_batch_view_gather (K B S H : Nat) (ts : List Tensor)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : ts.length = K) (hsh : ∀ t ∈ ts, t.shape = [B,S,H]) :
    fw_view [1,(B*S)*K,H] (allGatherPrimDimN 0 K 0 ts) =
      allGatherPrimDimN 1 K 0 (ts.map (fw_view [1,B*S,H])) := by
  have hne : ts ≠ [] := by intro he; simp [he] at hlen; omega
  obtain ⟨t, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hh : ((t :: rest).head?.map (fun t => t.shape)).getD [] = [B,S,H] :=
    hsh t (List.mem_cons_self ..)
  have hm : (((t :: rest).map (fw_view [1,B*S,H])).head?.map
      (fun t => t.shape)).getD [] = [1,B*S,H] := rfl
  have hl : (allGatherPrimDimN 0 K 0 (t :: rest)).shape = [B*K,S,H] := by
    rw [allGatherPrimDimN_shape 0 K _ _ hh]; rfl
  have hr : (allGatherPrimDimN 1 K 0
      ((t :: rest).map (fw_view [1,B*S,H]))).shape = [1,(B*S)*K,H] := by
    rw [allGatherPrimDimN_shape 1 K _ _ hm]; rfl
  have hp : prodShape [1,(B*S)*K,H] = prodShape [B*K,S,H] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    ring
  apply Tensor.ext hr.symm
  intro j hj
  change j < prodShape [1,(B*S)*K,H] at hj
  rw [dw_view_read _ _ (by rw [hl]; exact hp) j]
  have hjl : j < prodShape (allGatherPrimDimN 0 K 0 (t :: rest)).shape := by
    rw [hl, ← hp]; exact hj
  have hjr : j < prodShape (allGatherPrimDimN 1 K 0
      ((t :: rest).map (fw_view [1,B*S,H]))).shape := by rw [hr]; exact hj
  have hj0 : j < (B*K)*(S*H) := by
    rw [hp] at hj
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hj
  have hj1 : j < ((B*S)*K)*H := by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hj
  have hSH : S*H ≠ 0 := (Nat.mul_pos hS hH).ne'
  have hBS : B*S ≠ 0 := (Nat.mul_pos hB hS).ne'
  have hfull0 : (B*K)*(S*H) ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos hB hK) (Nat.mul_pos hS hH)).ne'
  have hfull1 : ((B*S)*K)*H ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB hS) hK) hH).ne'
  rw [valAt_of_lt (allGatherPrimDimN 0 K 0 (t :: rest)) j hjl,
    valAt_of_lt (allGatherPrimDimN 1 K 0
      ((t :: rest).map (fw_view [1,B*S,H]))) j hjr]
  unfold allGatherPrimDimN
  simp only [hh, hm, Tensor.mkShape, List.getD_cons_zero, List.getD_cons_succ,
    List.drop, List.foldl, Nat.one_mul, hB.ne', hH.ne', hSH, hBS,
    hfull0, hfull1, ite_false, Nat.div_eq_of_lt hj0, Nat.mod_eq_of_lt hj0,
    Nat.div_eq_of_lt hj1, Nat.mod_eq_of_lt hj1, Nat.zero_mul, Nat.zero_add]
  rw [dw_map_read B S H (t :: rest) _ _ hsh]
  have hq : j / (S*H) / B = j / H / (B*S) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    congr 1 <;> ring
  have hm0 : (j / (S*H) % B) * (S*H) + j % (S*H) = j % (B*(S*H)) := by
    rw [Nat.mul_comm B (S*H), Nat.mod_mul (x := j) (a := S*H) (b := B)]
    ring
  have hm1 : (j / H % (B*S)) * H + j % H = j % ((B*S)*H) := by
    rw [Nat.mul_comm (B*S) H, Nat.mod_mul (x := j) (a := H) (b := B*S)]
    ring
  rw [hq, hm0, hm1, Nat.mul_assoc]

private theorem dw_zip_views (B S O I : Nat) (gs xs : List Tensor) (w : Tensor)
    (hgsh : ∀ g ∈ gs, g.shape = [B,S,O])
    (hxsh : ∀ x ∈ xs, x.shape = [B,S,I]) (hw : w.shape = [O,I]) :
    List.zipWith (fun g x => (bw_linear g x w).2)
      (gs.map (fw_view [1,B*S,O])) (xs.map (fw_view [1,B*S,I])) =
      List.zipWith (fun g x => (bw_linear g x w).2) gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.map, List.zipWith]
      apply congrArg₂ List.cons
      · exact (dw_view_rows B S O I g x w
          (hgsh g (List.mem_cons_self ..)) (hxsh x (List.mem_cons_self ..)) hw).symm
      · exact ih xs (fun g hg => hgsh g (List.mem_cons_of_mem _ hg))
          (fun x hx => hxsh x (List.mem_cons_of_mem _ hx))

/-- Batch-axis DP reduction of dW, retaining real saved-X reconstruction.
All dimensions are positive and both ordered shard lists have exactly K entries.
No output-value or output-shape equality is assumed. -/
theorem source_bw_linear_dw_batch_unit
    (K B S O I : Nat) (g x w : Tensor) (gs xs : List Tensor)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hO : 0 < O) (hI : 0 < I)
    (hg : g.shape = [B*K,S,O]) (hx : x.shape = [B*K,S,I])
    (hw : w.shape = [O,I]) (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [B,S,O])
    (hxsh : ∀ x ∈ xs, x.shape = [B,S,I])
    (hgradient : g = allGatherPrimDimN 0 K 0 gs)
    (hsaved : x = allGatherPrimDimN 0 K 0 xs) :
    (bw_linear g x w).2 =
      tensorSum (List.zipWith (fun g x => (bw_linear g x w).2) gs xs) := by
  have hrows : (B*K)*S = (B*S)*K := by ring
  rw [dw_view_rows (B*K) S O I g x w hg hx hw, hrows, hgradient, hsaved,
    dw_batch_view_gather K B S O gs hK hB hS hO hglen hgsh,
    dw_batch_view_gather K B S I xs hK hB hS hI hxlen hxsh]
  rw [bw_linear_dw_sequence_reduction_rank3 K 1 (B*S) O I
    (gs.map (fw_view [1,B*S,O])) (xs.map (fw_view [1,B*S,I])) w
    hK (by decide) (Nat.mul_pos hB hS) hO hI
    (by rw [List.length_map, hglen]) (by rw [List.length_map, hxlen])
    (by intro t ht; obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht; rfl)
    (by intro t ht; obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht; rfl) hw]
  exact congrArg tensorSum (dw_zip_views B S O I gs xs w hgsh hxsh hw)

#print axioms source_bw_linear_dw_flat_rows
#print axioms source_bw_linear_dw_batch_unit

end
end TrainVerify.Denote
