/- Common shared lemmas factored out of Goal_15/21/23 proofs.

Part 1: initGoal extraction (shape / reconstruction proofs).
Part 2: BW_linear suffix and ChunkPrim prefix infrastructure
        shared by Goal_21_Proof and Goal_23_Proof.
-/
import denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.Common

set_option linter.flexible false

/-!
## Part 3: Generic initGoal extraction helpers

These lemmas factor out the repetitive pattern of extracting
shape equalities and reconstruction from `InitGoalHolds`.
-/

/-- Extract element equalities from a 4-element list equation. -/
theorem list_eq_4 {α : Type} {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : α}
    (h : [a₀, a₁, a₂, a₃] = [b₀, b₁, b₂, b₃]) :
    a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  simp only [List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Extract shape and value equality from a replicated (single-piece, same tid) InitGoal.

For initGoals like `initGoal_97 := { ts := 97, tps := [⟨0, 97⟩], ... }`,
this extracts both `(initSM tid).shape = sh` and `initSM tid = initPM tid`.
Pass concrete values for `tid` and `sh` so hypotheses have literal types. -/
theorem initGoalHolds_replicated (numParts : Nat) (goal : LineageGoal)
    (tid : Tid) (sh : Shape) (initSM initPM : Store)
    (h : InitGoalHolds numParts goal initSM initPM)
    (htid : goal.ts = tid) (htps : goal.tps = [⟨0, tid⟩])
    (hsh : goal.tsShape = sh) :
    (initSM tid).shape = sh ∧ initSM tid = initPM tid := by
  subst htid; subst hsh
  obtain ⟨hshape, _, hrec⟩ := h
  simp only [htps, List.map, reconstructWithDim] at hrec
  exact ⟨hshape, hrec⟩

/-- Extract shapes and reconstruction from a 4-shard InitGoal.

For intermediateGoals like `{ ts := 159, tps := [⟨0,168⟩,⟨1,169⟩,⟨2,170⟩,⟨3,171⟩], ... }`,
this extracts the SM shape, all 4 shard shapes, and the reconstruction equation in one step.
Pass concrete values for `smTid`, `smShape`, shard tids and shape so hypotheses have literal types. -/
theorem initGoalHolds_sharded4 (numParts : Nat) (goal : LineageGoal)
    (smTid t0 t1 t2 t3 : Tid) (smShape shardShape : Shape)
    (initSM initPM : Store)
    (h : InitGoalHolds numParts goal initSM initPM)
    (htid : goal.ts = smTid) (hsh : goal.tsShape = smShape)
    (htps : goal.tps = [⟨0, t0⟩, ⟨1, t1⟩, ⟨2, t2⟩, ⟨3, t3⟩])
    (hshapes : goal.tpShapes = [shardShape, shardShape, shardShape, shardShape]) :
    (initSM smTid).shape = smShape ∧
    (initPM t0).shape = shardShape ∧
    (initPM t1).shape = shardShape ∧
    (initPM t2).shape = shardShape ∧
    (initPM t3).shape = shardShape ∧
    initSM smTid = reconstructWithDim goal.gatherDim numParts 0
      [initPM t0, initPM t1, initPM t2, initPM t3] := by
  subst htid; subst hsh
  obtain ⟨hshape, htpshapes, hrec⟩ := h
  simp only [htps, List.map] at htpshapes hrec
  rw [hshapes] at htpshapes
  obtain ⟨h0, h1, h2, h3⟩ := list_eq_4 htpshapes
  exact ⟨hshape, h0, h1, h2, h3, hrec⟩

/-!
## Part 4: FW_linear + AllGatherPrimDim0 coarse lineage

This theorem handles the common pattern where:
- SM graph: single `FW_linear(x, w) → out`
- PM graph: 4× `FW_linear(shard_r, w) → out_r` then `AllGatherPrim → out`
- Weight `w` is replicated (same on SM and PM)
- Input `x` is dim-0 sharded into 4 pieces

Used by attn/Goal_2 (tid 98) and attn/Goal_3 (tid 100).
-/

theorem fw_linear_allGatherDim0_coarse
    (numRanks b0 s i o : Nat)
    (smStore pmStore : Store) (outTid : Tid)
    (initSM initPM : Store) (xSmTid wTid xPm0 xPm1 xPm2 xPm3 : Tid)
    (hsm : smStore outTid = fw_linear (initSM xSmTid) (initSM wTid))
    (hpm : pmStore outTid = allGatherPrimDim0 numRanks 0
      [fw_linear (initPM xPm0) (initPM wTid),
       fw_linear (initPM xPm1) (initPM wTid),
       fw_linear (initPM xPm2) (initPM wTid),
       fw_linear (initPM xPm3) (initPM wTid)])
    (hx_rec : initSM xSmTid = reconstructWithDim 0 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3])
    (hweq : initSM wTid = initPM wTid)
    (hw_shape : (initSM wTid).shape = [o, i])
    (hxsm_shape : (initSM xSmTid).shape = [b0 * numRanks, s, i])
    (hxpm0_shape : (initPM xPm0).shape = [b0, s, i])
    (hxpm1_shape : (initPM xPm1).shape = [b0, s, i])
    (hxpm2_shape : (initPM xPm2).shape = [b0, s, i])
    (hxpm3_shape : (initPM xPm3).shape = [b0, s, i])
    (hlen : [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3].length = numRanks)
    (hb0 : 0 < b0) (hs : 0 < s) (hi : 0 < i) (ho : 0 < o) (hnr : 0 < numRanks) :
    (smStore outTid).shape = [b0 * numRanks, s, o] ∧
    [(pmStore outTid).shape] = [[b0 * numRanks, s, o]] ∧
    smStore outTid = reconstructWithDim 0 numRanks 0 [pmStore outTid] := by
  have hxpm_shape : ∀ x ∈ [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3],
      x.shape = [b0, s, i] := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h_dimN : initSM xSmTid = allGatherPrimDimN 0 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3] := by
    rw [hx_rec]; simp [reconstructWithDim, hxpm0_shape]
  have hw_pm : (initPM wTid).shape = [o, i] := by rw [← hweq]; exact hw_shape
  have hdistr : fw_linear (initSM xSmTid) (initSM wTid) =
      allGatherPrimDim0 numRanks 0
        [fw_linear (initPM xPm0) (initPM wTid),
         fw_linear (initPM xPm1) (initPM wTid),
         fw_linear (initPM xPm2) (initPM wTid),
         fw_linear (initPM xPm3) (initPM wTid)] := by
    conv_lhs => rw [h_dimN, hweq]
    have := fw_linear_3d_allGatherPrimDimN0_comm
      (numParts := numRanks) (b0 := b0) (s := s) (i := i) (o := o)
      (xs := [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3])
      (w := initPM wTid)
      (hw := hw_pm)
      (hxs_head := by simp [hxpm0_shape])
      (hxs_shape := hxpm_shape)
      (hxs_len := hlen)
      (hparts := hnr) (hb0 := hb0) (hs := hs) (hi := hi) (ho := ho)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]
    exact fw_linear_3d_shape (b0 * numRanks) s i o _ _ hxsm_shape hw_shape
  · rw [hpm]
    have hfw_head : (fw_linear (initPM xPm0) (initPM wTid)).shape = [b0, s, o] :=
      fw_linear_3d_shape b0 s i o _ _ hxpm0_shape hw_pm
    have hag := allGatherPrimDim0_shape_3d numRanks b0 s o
      [fw_linear (initPM xPm0) (initPM wTid),
       fw_linear (initPM xPm1) (initPM wTid),
       fw_linear (initPM xPm2) (initPM wTid),
       fw_linear (initPM xPm3) (initPM wTid)]
      (by simp only [List.head?, Option.map, Option.getD]; exact hfw_head)
    simp [hag]
  · rw [hsm, hdistr, ← hpm]
    simp [reconstructWithDim]

/-!
## Part 5: FW_linear + AllReducePrim coarse lineage (Column-parallel)

This handles the pattern where:
- SM graph: single `FW_linear(x, w) → out`
- PM graph: 4× `FW_linear(x_r, w_r) → out_r` then `AllReducePrim → out`
- Both input x and weight w are sharded along their last (inner/reduction) dimension
- The result is summed via AllReduce (column-parallel matmul)
-/

private theorem allGatherPrimDimN_1_valAt
    (numParts o shard : Nat) (pieces : List Tensor)
    (hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard)
    (p : Nat) (hp : p < o) (r : Nat) (hr : r < numParts)
    (j : Nat) (hj : j < shard) :
    valAt (allGatherPrimDimN 1 numParts 0 pieces)
        (p * (shard * numParts) + r * shard + j) =
      valAt (pieces.getD r (zeroTensor [o, shard])) (p * shard + j) := by
  have hfull_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hrem_lt : r * shard + j < shard * numParts := by
    calc r * shard + j
        < r * shard + shard := Nat.add_lt_add_left hj _
      _ = (r + 1) * shard := by ring
      _ ≤ numParts * shard := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr)
      _ = shard * numParts := Nat.mul_comm ..
  have hlt : p * (shard * numParts) + r * shard + j < o * (shard * numParts) := by
    calc p * (shard * numParts) + r * shard + j
        < p * (shard * numParts) + shard * numParts := by omega
      _ = (p + 1) * (shard * numParts) := by ring
      _ ≤ o * (shard * numParts) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hp)
  have hshape_out : (allGatherPrimDimN 1 numParts 0 pieces).shape =
      [o, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : p * (shard * numParts) + r * shard + j <
      prodShape (allGatherPrimDimN 1 numParts 0 pieces).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]; omega
  have hdiv : (p * (shard * numParts) + r * shard + j) / (shard * numParts) = p := by
    have heq : (r * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.1
  have hmod : (p * (shard * numParts) + r * shard + j) % (shard * numParts) =
      r * shard + j := by
    have heq : (r * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.2
  have hdivS : (r * shard + j) / shard = r := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.1
  have hmodS : (r * shard + j) % shard = j := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.2
  rw [valAt_of_lt _ _ hlt_prod]
  simp [allGatherPrimDimN, Tensor.mkShape, hhead,
    hshard.ne', hfull_pos.ne', (show (1 : Nat) ≠ 0 by omega),
    Nat.div_one, Nat.mod_one, hdiv, hmod, hdivS, hmodS]

private theorem allGatherPrimDimN_2_valAt
    (numParts b s shard : Nat) (pieces : List Tensor)
    (hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, s, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard)
    (batch : Nat) (hbatch : batch < b * s) (r : Nat) (hr : r < numParts)
    (j : Nat) (hj : j < shard) :
    valAt (allGatherPrimDimN 2 numParts 0 pieces)
        (batch * (shard * numParts) + r * shard + j) =
      valAt (pieces.getD r (zeroTensor [b, s, shard])) (batch * shard + j) := by
  have hfull_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hrem_lt : r * shard + j < shard * numParts := by
    calc r * shard + j
        < r * shard + shard := Nat.add_lt_add_left hj _
      _ = (r + 1) * shard := by ring
      _ ≤ numParts * shard := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr)
      _ = shard * numParts := Nat.mul_comm ..
  have hlt : batch * (shard * numParts) + r * shard + j <
      b * s * (shard * numParts) := by
    calc batch * (shard * numParts) + r * shard + j
        < batch * (shard * numParts) + shard * numParts := by omega
      _ = (batch + 1) * (shard * numParts) := by ring
      _ ≤ (b * s) * (shard * numParts) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hbatch)
  have hshape_out : (allGatherPrimDimN 2 numParts 0 pieces).shape =
      [b, s, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : batch * (shard * numParts) + r * shard + j <
      prodShape (allGatherPrimDimN 2 numParts 0 pieces).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]
    have : b * s * (shard * numParts) = 1 * b * s * (shard * numParts) := by ring
    omega
  have hdiv : (batch * (shard * numParts) + r * shard + j) /
      (shard * numParts) = batch := by
    have heq : (r * shard + j) + (shard * numParts) * batch =
        batch * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.1
  have hmod : (batch * (shard * numParts) + r * shard + j) %
      (shard * numParts) = r * shard + j := by
    have heq : (r * shard + j) + (shard * numParts) * batch =
        batch * (shard * numParts) + r * shard + j := by ring
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, hrem_lt⟩ |>.2
  have hdivS : (r * shard + j) / shard = r := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.1
  have hmodS : (r * shard + j) % shard = j := by
    have heq : j + shard * r = r * shard + j := by ring
    exact (Nat.div_mod_unique hshard).2 ⟨heq, hj⟩ |>.2
  rw [valAt_of_lt _ _ hlt_prod]
  simp [allGatherPrimDimN, Tensor.mkShape, hhead,
    hshard.ne', hfull_pos.ne', (show (1 : Nat) ≠ 0 by omega),
    Nat.div_one, Nat.mod_one, hdiv, hmod, hdivS, hmodS]

theorem fw_linear_3d_column_parallel
    (numParts b s shard o : Nat)
    (xs : List Tensor) (ws : List Tensor)
    (hxs_shapes : ∀ x ∈ xs, x.shape = [b, s, shard])
    (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hxs_len : xs.length = numParts)
    (hws_len : ws.length = numParts)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, shard])
    (hws_head : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hparts : 0 < numParts) (hb : 0 < b) (hs : 0 < s)
    (hshard : 0 < shard) (ho : 0 < o) :
    fw_linear (allGatherPrimDimN 2 numParts 0 xs) (allGatherPrimDimN 1 numParts 0 ws) =
      allReducePrim numParts 0 (List.zipWith (fun x w => fw_linear x w) xs ws) := by
  have hsN_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hso_ne : s * o ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hs ho)
  have ho_ne : o ≠ 0 := Nat.ne_of_gt ho
  have hbs_pos : 0 < b * s := Nat.mul_pos hb hs
  -- Gathered tensor shapes
  have hgX_shape : (allGatherPrimDimN 2 numParts 0 xs).shape =
      [b, s, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hxs_head]
  have hgW_shape : (allGatherPrimDimN 1 numParts 0 ws).shape =
      [o, shard * numParts] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hws_head]
  have hLHS_shape : (fw_linear (allGatherPrimDimN 2 numParts 0 xs)
      (allGatherPrimDimN 1 numParts 0 ws)).shape = [b, s, o] :=
    fw_linear_3d_shape b s (shard * numParts) o _ _ hgX_shape hgW_shape
  -- zipWith properties
  have hzw_len : (List.zipWith (fun x w => fw_linear x w) xs ws).length =
      numParts := by simp [List.length_zipWith, hxs_len, hws_len]
  have hzw_ne : List.zipWith (fun x w => fw_linear x w) xs ws ≠ [] := by
    intro h; simp [h] at hzw_len; omega
  have hzw_head_shape : ((List.zipWith (fun x w => fw_linear x w) xs ws).head?.map
      (fun t => t.shape)).getD [] = [b, s, o] := by
    rw [List.head?_eq_some_head hzw_ne]
    simp only [Option.map_some, Option.getD_some]
    match xs, ws, hxs_len, hws_len with
    | x0 :: _, w0 :: _, _, _ =>
      simp only [List.zipWith, List.head]
      exact fw_linear_3d_shape b s shard o x0 w0
        (hxs_shapes x0 (by simp)) (hws_shapes w0 (by simp))
  have hRHS_shape : (allReducePrim numParts 0
      (List.zipWith (fun x w => fw_linear x w) xs ws)).shape = [b, s, o] := by
    simp [allReducePrim, Tensor.mkShape, hzw_head_shape]
  -- Apply Tensor.ext
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx_bso : idx < b * s * o := by
    simp only [hLHS_shape, prodShape, List.foldl, Nat.one_mul] at hidx
    have : 1 * b * s * o = b * s * o := by ring
    omega
  have hcol_lt : idx % o < o := Nat.mod_lt _ ho
  have hbatch_lt : idx / o < b * s :=
    Nat.div_lt_iff_lt_mul ho |>.mpr hidx_bso
  -- LHS: resolve fw_linear match using known shapes
  conv_lhs => simp only [fw_linear, hgX_shape, hgW_shape]
  -- RHS: rewrite allReducePrim to Tensor.mkShape with known shape
  have allReduce_eq : allReducePrim numParts 0
      (List.zipWith (fun x w => fw_linear x w) xs ws) =
    Tensor.mkShape [b, s, o] (fun idx =>
      List.foldl (fun acc t => acc + valAt t idx) 0
        (List.zipWith (fun x w => fw_linear x w) xs ws)) := by
    unfold allReducePrim; rw [hzw_head_shape]
  rw [allReduce_eq]
  -- Unfold valAt on both sides (both are now Tensor.mkShape [b,s,o])
  have hprod : idx < prodShape [b, s, o] := by
    rw [hLHS_shape] at hidx; exact hidx
  rw [valAt_of_lt _ _ hprod, valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte]
  -- Normalize the batch index and column index
  have hrow : idx / (s * o) * s + idx % (s * o) / o = idx / o := by
    rw [show idx / (s * o) * s = idx / o / s * s from by
      rw [Nat.div_div_eq_div_mul]; ring_nf]
    rw [show s * o = o * s from Nat.mul_comm s o, Nat.mod_mul_right_div_self,
        Nat.mul_comm (idx / o / s) s, Nat.div_add_mod]
  have hcol : idx % (s * o) % o = idx % o :=
    Nat.mod_mod_of_dvd _ ⟨s, (Nat.mul_comm o s).symm⟩
  simp only [hrow, hcol]
  -- Convert RHS foldl to Finset.sum
  rw [List.foldl_add_eq_sum (f := fun t => valAt t idx)]
  -- Split LHS sum: range(N*shard) → ∑ r ∑ l
  conv_lhs =>
    rw [Nat.mul_comm shard numParts,
        Finset.sum_range_mul_eq_sum_sum (n := numParts) (m := shard)]
  -- Substitute allGatherPrimDimN valAt in LHS
  have hval_eq : ∀ r ∈ Finset.range numParts, ∀ l ∈ Finset.range shard,
      valAt (allGatherPrimDimN 2 numParts 0 xs)
        (idx / o * (shard * numParts) + (r * shard + l)) *
      valAt (allGatherPrimDimN 1 numParts 0 ws)
        (idx % o * (shard * numParts) + (r * shard + l)) =
      valAt (xs.getD r (zeroTensor [b, s, shard])) (idx / o * shard + l) *
      valAt (ws.getD r (zeroTensor [o, shard])) (idx % o * shard + l) := by
    intro r hr l hl
    have hr' := Finset.mem_range.mp hr
    have hl' := Finset.mem_range.mp hl
    have hassocX : idx / o * (shard * numParts) + (r * shard + l) =
        (idx / o) * (shard * numParts) + r * shard + l := by ring
    have hassocW : idx % o * (shard * numParts) + (r * shard + l) =
        (idx % o) * (shard * numParts) + r * shard + l := by ring
    rw [hassocX, hassocW,
        allGatherPrimDimN_2_valAt numParts b s shard xs hxs_head hparts hshard
          (idx / o) hbatch_lt r hr' l hl',
        allGatherPrimDimN_1_valAt numParts o shard ws hws_head hparts hshard
          (idx % o) hcol_lt r hr' l hl']
  conv_lhs =>
    arg 2; ext r
    arg 2; ext l
    rw [show r * shard + l = r * shard + l from rfl]
  -- Apply the valAt substitution
  have hlhs_rw :
    ∑ r ∈ Finset.range numParts, ∑ l ∈ Finset.range shard,
      valAt (allGatherPrimDimN 2 numParts 0 xs)
        (idx / o * (shard * numParts) + (r * shard + l)) *
      valAt (allGatherPrimDimN 1 numParts 0 ws)
        (idx % o * (shard * numParts) + (r * shard + l)) =
    ∑ r ∈ Finset.range numParts, ∑ l ∈ Finset.range shard,
      valAt (xs.getD r (zeroTensor [b, s, shard])) (idx / o * shard + l) *
      valAt (ws.getD r (zeroTensor [o, shard])) (idx % o * shard + l) := by
    exact Finset.sum_congr rfl fun r hr =>
      Finset.sum_congr rfl fun l hl => hval_eq r hr l hl
  simp only [show numParts * shard = shard * numParts from Nat.mul_comm numParts shard]
  rw [hlhs_rw]
  -- Convert LHS Finset.sum to List.sum via Fin.sum_ofFn
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_ofFn]
  -- Now both sides are List.sum; show the lists are equal
  congr 1
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_zipWith, hxs_len, hws_len]
  · intro n hn1 hn2
    simp only [List.length_ofFn] at hn1
    simp only [List.getElem_ofFn, List.getElem_map]
    have hn_xs : n < xs.length := by omega
    have hn_ws : n < ws.length := by omega
    simp only [List.getElem_zipWith]
    have hxn : xs[n].shape = [b, s, shard] := hxs_shapes _ (List.getElem_mem hn_xs)
    have hwn : ws[n].shape = [o, shard] := hws_shapes _ (List.getElem_mem hn_ws)
    conv_rhs => simp only [fw_linear, hxn, hwn]
    rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, prodShape, List.foldl]; exact hidx_bso)]
    simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte, hrow, hcol]
    apply Finset.sum_congr rfl; intro l _
    simp only [List.getD, List.getElem?_eq_getElem hn_xs, List.getElem?_eq_getElem hn_ws,
      Option.getD_some]

theorem fw_linear_allReduce_coarse
    (numRanks b s shard o : Nat)
    (smStore pmStore : Store) (outTid : Tid)
    (initSM initPM : Store)
    (xSmTid wSmTid xPm0 xPm1 xPm2 xPm3 wPm0 wPm1 wPm2 wPm3 : Tid)
    (hsm : smStore outTid = fw_linear (initSM xSmTid) (initSM wSmTid))
    (hpm : pmStore outTid = allReducePrim numRanks 0
      [fw_linear (initPM xPm0) (initPM wPm0),
       fw_linear (initPM xPm1) (initPM wPm1),
       fw_linear (initPM xPm2) (initPM wPm2),
       fw_linear (initPM xPm3) (initPM wPm3)])
    (hx_rec : initSM xSmTid = reconstructWithDim 2 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3])
    (hw_rec : initSM wSmTid = reconstructWithDim 1 numRanks 0
      [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3])
    (hxsm_shape : (initSM xSmTid).shape = [b, s, shard * numRanks])
    (hwsm_shape : (initSM wSmTid).shape = [o, shard * numRanks])
    (hxpm0 : (initPM xPm0).shape = [b, s, shard])
    (hxpm1 : (initPM xPm1).shape = [b, s, shard])
    (hxpm2 : (initPM xPm2).shape = [b, s, shard])
    (hxpm3 : (initPM xPm3).shape = [b, s, shard])
    (hwpm0 : (initPM wPm0).shape = [o, shard])
    (hwpm1 : (initPM wPm1).shape = [o, shard])
    (hwpm2 : (initPM wPm2).shape = [o, shard])
    (hwpm3 : (initPM wPm3).shape = [o, shard])
    (hxlen : [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3].length = numRanks)
    (hwlen : [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3].length = numRanks)
    (hb : 0 < b) (hs : 0 < s) (hshard : 0 < shard) (ho : 0 < o)
    (hnr : 0 < numRanks) :
    (smStore outTid).shape = [b, s, o] ∧
    [(pmStore outTid).shape] = [[b, s, o]] ∧
    smStore outTid = reconstructWithDim 0 numRanks 0 [pmStore outTid] := by
  have hxpm_shapes : ∀ x ∈ [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3],
      x.shape = [b, s, shard] := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hwpm_shapes : ∀ w ∈ [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3],
      w.shape = [o, shard] := by
    intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hx_dimN : initSM xSmTid = allGatherPrimDimN 2 numRanks 0
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3] := by
    rw [hx_rec]; simp [reconstructWithDim, hxpm0]
  have hw_dimN : initSM wSmTid = allGatherPrimDimN 1 numRanks 0
      [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3] := by
    rw [hw_rec]; simp [reconstructWithDim, hwpm0]
  have hdistr : fw_linear (initSM xSmTid) (initSM wSmTid) =
      allReducePrim numRanks 0
        [fw_linear (initPM xPm0) (initPM wPm0),
         fw_linear (initPM xPm1) (initPM wPm1),
         fw_linear (initPM xPm2) (initPM wPm2),
         fw_linear (initPM xPm3) (initPM wPm3)] := by
    rw [hx_dimN, hw_dimN]
    have := fw_linear_3d_column_parallel numRanks b s shard o
      [initPM xPm0, initPM xPm1, initPM xPm2, initPM xPm3]
      [initPM wPm0, initPM wPm1, initPM wPm2, initPM wPm3]
      hxpm_shapes hwpm_shapes
      (by simp [hxlen]) (by simp [hwlen])
      (by simp [hxpm0]) (by simp [hwpm0])
      hnr hb hs hshard ho
    simpa [List.zipWith] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]
    exact fw_linear_3d_shape b s (shard * numRanks) o _ _ hxsm_shape hwsm_shape
  · rw [hpm]
    have hfw0_shape : (fw_linear (initPM xPm0) (initPM wPm0)).shape = [b, s, o] :=
      fw_linear_3d_shape b s shard o _ _ hxpm0 hwpm0
    have hhead : [fw_linear (initPM xPm0) (initPM wPm0),
        fw_linear (initPM xPm1) (initPM wPm1),
        fw_linear (initPM xPm2) (initPM wPm2),
        fw_linear (initPM xPm3) (initPM wPm3)].head? =
        some (fw_linear (initPM xPm0) (initPM wPm0)) := rfl
    have hsh := allReducePrim_shape numRanks 0 _ _ hhead
    simp [hsh, hfw0_shape]
  · rw [hsm, hdistr, ← hpm]
    simp [reconstructWithDim]


private lemma tccg3_lhs_bound (idx : Nat) (hidx : idx < 131072) :
    idx / 8192 * 8192 + (idx % 1024 / 16 * 128 + (idx % 8192 / 1024 * 16 + idx % 16)) < 131072 := by
  omega

private lemma tccg3_fi_bound (idx : Nat) (hidx : idx < 131072) :
    idx / 16 * 4 + idx % 4 < 32768 := by omega

private lemma tccg3_ci_bound (idx : Nat) (hidx : idx < 131072) :
    (idx / 16 * 4 + idx % 4) / 2048 * 2048 +
    ((idx / 16 * 4 + idx % 4) % 256 / 4 * 32 +
    ((idx / 16 * 4 + idx % 4) % 2048 / 256 * 4 + idx % 4)) < 32768 := by
  have hfi : idx / 16 * 4 + idx % 4 < 32768 := by omega
  have : (idx / 16 * 4 + idx % 4) / 2048 ≤ 15 := by omega
  have : (idx / 16 * 4 + idx % 4) % 256 / 4 ≤ 63 := by omega
  have : (idx / 16 * 4 + idx % 4) % 2048 / 256 ≤ 7 := by omega
  have : idx % 4 ≤ 3 := by omega
  omega

private lemma tccg3_idx_eq (idx : Nat) (hidx : idx < 131072) :
    idx / 8192 * 8192 + (idx % 1024 / 16 * 128 + (idx % 8192 / 1024 * 16 + idx % 16)) =
    ((idx / 16 * 4 + idx % 4) / 2048 * 2048 +
      ((idx / 16 * 4 + idx % 4) % 256 / 4 * 32 +
      ((idx / 16 * 4 + idx % 4) % 2048 / 256 * 4 + idx % 4))) / 4 * 16 +
    (idx % 16) / 4 * 4 +
    ((idx / 16 * 4 + idx % 4) / 2048 * 2048 +
      ((idx / 16 * 4 + idx % 4) % 256 / 4 * 32 +
      ((idx / 16 * 4 + idx % 4) % 2048 / 256 * 4 + idx % 4))) % 4 := by
  have := tccg3_ci_bound idx hidx
  have h1 : (idx / 16 * 4 + idx % 4) / 2048 = idx / 8192 := by omega
  have h2 : (idx / 16 * 4 + idx % 4) % 256 / 4 = idx % 1024 / 16 := by omega
  have h3 : (idx / 16 * 4 + idx % 4) % 2048 / 256 = idx % 8192 / 1024 := by omega
  have h4 : (idx / 16 * 4 + idx % 4) % 4 = idx % 4 := by omega
  simp only [h1, h2, h3]
  have h5 : (idx / 8192 * 2048 + (idx % 1024 / 16 * 32 + (idx % 8192 / 1024 * 4 + idx % 4))) / 4 =
      idx / 8192 * 512 + idx % 1024 / 16 * 8 + idx % 8192 / 1024 := by omega
  have h6 : (idx / 8192 * 2048 + (idx % 1024 / 16 * 32 + (idx % 8192 / 1024 * 4 + idx % 4))) % 4 =
      idx % 4 := by omega
  simp only [h5, h6]
  omega

theorem transposeAxes_12_chunkPrim_gather3
    (x : Tensor) (hshape : x.shape = [16, 64, 8, 16]) :
    transposeAxes 1 2 x = allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrim 4 0 x),
       transposeAxes 1 2 (chunkPrim 4 1 x),
       transposeAxes 1 2 (chunkPrim 4 2 x),
       transposeAxes 1 2 (chunkPrim 4 3 x)] := by
  have hpiece_shape : ∀ r, (transposeAxes 1 2 (chunkPrim 4 r x)).shape = [16, 8, 64, 4] := by
    intro r; simp [transposeAxes, chunkPrim, Tensor.mkShape, listSwapAt, hshape,
                    appendLast, dropLast, divNat, lastD]
  have hLHS_shape : (transposeAxes 1 2 x).shape = [16, 8, 64, 16] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hhead : (([transposeAxes 1 2 (chunkPrim 4 0 x),
       transposeAxes 1 2 (chunkPrim 4 1 x),
       transposeAxes 1 2 (chunkPrim 4 2 x),
       transposeAxes 1 2 (chunkPrim 4 3 x)].head?.map (fun t => t.shape)).getD []) =
       [16, 8, 64, 4] := by
    simp [List.head?, Option.map, hpiece_shape]
  have hRHS_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrim 4 0 x),
       transposeAxes 1 2 (chunkPrim 4 1 x),
       transposeAxes 1 2 (chunkPrim 4 2 x),
       transposeAxes 1 2 (chunkPrim 4 3 x)]).shape = [16, 8, 64, 16] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hpiece_shape]
  -- Concrete list computation facts (avoid List.getLast stuck-ness in simp only)
  have h_dl : dropLast [16, 64, 8, 16] = [16, 64, 8] := by simp [dropLast]
  have h_ld : lastD [16, 64, 8, 16] = 16 := by simp [lastD]
  have h_dv : divNat 16 4 = 4 := by simp [divNat]
  have h_al : appendLast [16, 64, 8] 4 = [16, 64, 8, 4] := by simp [appendLast]
  have h_ls12 : listSwapAt [16, 64, 8, 4] 1 2 = [16, 8, 64, 4] := by simp [listSwapAt]
  have h_ls_x : listSwapAt [16, 64, 8, 16] 1 2 = [16, 8, 64, 16] := by simp [listSwapAt]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 131072 := by simpa [prodShape] using hidx
  -- Concrete getLast reductions
  have h_getLast_16_64_8_16 : ∀ h, ([16, 64, 8, 16] : List Nat).getLast h = 16 := fun _ => rfl
  have h_getLast_16_64_8_4 : ∀ h, ([16, 64, 8, 4] : List Nat).getLast h = 4 := fun _ => rfl
  have h_getLast_16_8_64_4 : ∀ h, ([16, 8, 64, 4] : List Nat).getLast h = 4 := fun _ => rfl
  have h_getLast_16_8_64_16 : ∀ h, ([16, 8, 64, 16] : List Nat).getLast h = 16 := fun _ => rfl
  -- Simp lemmas for if-elimination and list operations
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_1024 : (1024 : Nat) ≠ 0 := by omega
  have hne_128 : (128 : Nat) ≠ 0 := by omega
  have hne_16 : (16 : Nat) ≠ 0 := by omega
  have hne_1 : (1 : Nat) ≠ 0 := by omega
  have hne_2048 : (2048 : Nat) ≠ 0 := by omega
  have hne_256 : (256 : Nat) ≠ 0 := by omega
  have hne_32 : (32 : Nat) ≠ 0 := by omega
  have hne_4 : (4 : Nat) ≠ 0 := by omega
  have hne_32768 : (32768 : Nat) ≠ 0 := by omega
  have hne_131072 : (131072 : Nat) ≠ 0 := by omega
  rw [valAt_of_lt _ _ (by simp [hLHS_shape, prodShape]; exact hidx'),
      valAt_of_lt _ _ (by simp [hRHS_shape, prodShape]; exact hidx')]
  -- Case-split on which piece is selected: (idx % 16) / 4 ∈ {0,1,2,3}
  have hr_cases : (idx % 16) / 4 = 0 ∨ (idx % 16) / 4 = 1 ∨ (idx % 16) / 4 = 2 ∨ (idx % 16) / 4 = 3 := by omega
  -- Pre-compute chunkPrim shape reduction
  have hchunk_shape : ∀ r, (chunkPrim 4 r x).shape = [16, 64, 8, 4] := by
    intro r; simp [chunkPrim, Tensor.mkShape, hshape, appendLast, dropLast, divNat, lastD]
  have htchunk_shape : ∀ r, (transposeAxes 1 2 (chunkPrim 4 r x)).shape = [16, 8, 64, 4] := by
    intro r; simp [transposeAxes, Tensor.mkShape, hchunk_shape, listSwapAt]
  -- Arithmetic facts that simp only cannot compute (Nat.mul is @[extern])
  have h_44 : (4 : Nat) * 4 = 16 := by norm_num
  rcases hr_cases with h | h | h | h <;>
  · -- Inline concrete piece shape for valAt bound checks
    -- Common simp lemmas
    have ps1 := show prodShape [8, 64, 16] = 8192 from by simp [prodShape]
    have ps2 := show prodShape [64, 16] = 1024 from by simp [prodShape]
    have ps3 := show prodShape [16] = 16 from by simp [prodShape]
    have ps4 := show prodShape ([] : List Nat) = 1 from by simp [prodShape]
    have ps5 := show prodShape [8, 64, 4] = 2048 from by simp [prodShape]
    have ps6 := show prodShape [64, 4] = 256 from by simp [prodShape]
    have ps7 := show prodShape [4] = 4 from by simp [prodShape]
    have ps8 := show prodShape [64, 8, 16] = 8192 from by simp [prodShape]
    have ps9 := show prodShape [8, 16] = 128 from by simp [prodShape]
    have ps10 := show prodShape [64, 8, 4] = 2048 from by simp [prodShape]
    have ps11 := show prodShape [8, 4] = 32 from by simp [prodShape]
    have ps12 := show prodShape [16, 8, 64, 16] = 131072 from by simp [prodShape]
    have ps13 := show prodShape [16, 64, 8, 16] = 131072 from by simp [prodShape]
    have ps14 := show prodShape [16, 8, 64, 4] = 32768 from by simp [prodShape]
    have ps15 := show prodShape [16, 64, 8, 4] = 32768 from by simp [prodShape]
    -- Simplify LHS
    conv_lhs =>
      simp (config := { maxSteps := 2000000 }) only [
        transposeAxes, Tensor.mkShape, hshape, listSwapAt, h_ls_x,
        flatToMulti, multiToFlat, valAt,
        ps1, ps2, ps3, ps4, ps8, ps9, ps12, ps13,
        List.getD, List.set, List.length, Nat.sub_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Option.getD_some, Option.getD_none,
        hne_8192, hne_1024, hne_128, hne_16, hne_1,
        Nat.mul_one, Nat.add_zero, Nat.div_one, Nat.mod_one,
        if_neg, if_pos, ite_false, ite_true, dite_true, dite_false]
    -- First unfold outer allGatherPrimDimN + select piece
    simp only [h, allGatherPrimDimN, Tensor.mkShape, hpiece_shape,
      List.getD, List.drop, List.foldl, List.head?,
      Option.map, Option.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some,
      hne_4, hne_16, hne_1, ite_false,
      Nat.mul_one, Nat.add_zero, Nat.div_one, Nat.mod_one, h_44]
    -- Single simp pass with hshape, unfolding all definitions
    simp (config := { maxSteps := 8000000 }) only [hshape,
      transposeAxes, chunkPrim, Tensor.mkShape,
      listSwapAt, appendLast, dropLast, divNat, lastD,
      h_getLast_16_64_8_16,
      List.dropLast, List.getLastD,
      List.cons_append, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some,
      List.getD, List.set,
      flatToMulti, multiToFlat, valAt,
      ps4, ps5, ps6, ps7, ps10, ps11, ps13, ps14, ps15, hne_1,
      hne_2048, hne_256, hne_4,
      Nat.mul_one, Nat.add_zero, Nat.div_one, ite_false]
    -- Normalize mod-of-mod chains (omega proves these individually)
    have hmm1 : ∀ n, n % 8192 % 1024 = n % 1024 := fun n => by omega
    have hmm2 : ∀ n, n % 1024 % 16 = n % 16 := fun n => by omega
    have hmm3 : ∀ n, n % 16 % 4 = n % 4 := fun n => by omega
    have hmm4 : ∀ n, n % 2048 % 256 = n % 256 := fun n => by omega
    have hmm5 : ∀ n, n % 256 % 4 = n % 4 := fun n => by omega
    -- Key lemmas: div/mod of (n * 4 + r) where r < 4
    have hdm1 : ∀ n, (n * 4 + idx % 4) / 4 = n := fun n => by omega
    have hdm2 : ∀ n, (n * 4 + idx % 4) % 4 = idx % 4 := fun n => by omega
    -- Concrete arithmetic that simp only cannot compute
    have h_16d4 : (16 : Nat) / 4 = 4 := by norm_num
    have h_0m4 : (0 : Nat) % 4 = 0 := by norm_num
    have h_1m4 : (1 : Nat) % 4 = 1 := by norm_num
    have h_2m4 : (2 : Nat) % 4 = 2 := by norm_num
    have h_3m4 : (3 : Nat) % 4 = 3 := by norm_num
    simp only [hmm1, hmm2, hmm3, hmm4, hmm5, hdm2,
               h_16d4, h_0m4, h_1m4, h_2m4, h_3m4,
               Nat.zero_mul, Nat.add_zero, Nat.one_mul]
    conv_lhs => rw [dif_pos (tccg3_lhs_bound idx hidx')]
    conv_rhs => rw [dif_pos (tccg3_fi_bound idx hidx')]
    conv_rhs => rw [dif_pos (tccg3_ci_bound idx hidx')]
    conv_rhs => rw [dif_pos (by have := tccg3_ci_bound idx hidx'; omega)]
    refine congr_arg x.val (Fin.ext ?_)
    have key := tccg3_idx_eq idx hidx'
    rw [h] at key
    exact key

-- valAt of scalarDiv distributes: valAt (scalarDiv t c) k = valAt t k / c
theorem valAt_scalarDiv (t : Tensor) (c : Scalar) (k : Nat) :
    valAt (scalarDiv t c) k = valAt t k / c := by
  unfold scalarDiv valAt Tensor.mkShape
  split <;> simp_all [zero_div]

-- scalarDiv commutes with allGatherPrimDimN (gatherDim=0, numParts=4, shape [4,8,64,64])
/-!
## Part 7: transposeAxes 2 3 commutes with chunkPrimDimN 0 / allGatherPrimDimN 0

For a tensor of shape [16, 8, 64, 16]:
  transposeAxes 2 3 x = allGatherPrimDimN 0 4 0
    [transposeAxes 2 3 (chunkPrimDimN 0 4 0 x),
     transposeAxes 2 3 (chunkPrimDimN 0 4 1 x),
     transposeAxes 2 3 (chunkPrimDimN 0 4 2 x),
     transposeAxes 2 3 (chunkPrimDimN 0 4 3 x)]

Decomposed into 3 helpers:
  (A) valAt_chunkPrimDimN_0_4 : valAt (chunkPrimDimN 0 4 r x) idx = valAt x (r * 32768 + idx)
  (B) valAt_transposeAxes_23_8_64_16 : valAt (transposeAxes 2 3 x) idx =
        valAt x (idx / 8192 * 8192 + idx % 8192 / 1024 * 1024 + idx % 64 * 16 + idx % 1024 / 64)
  (C) valAt_allGatherPrimDimN_0_4_32768 : valAt (allGather ...) idx =
        valAt (xs.getD (idx / 32768) ...) (idx % 32768)

Used by Goal_11.
-/

-- Helper A: valAt of chunkPrimDimN 0 4 for shape [16, 8, 64, 16]
private lemma valAt_chunkPrimDimN_0_4 (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 8, 64, 16]) (hr : r < 4) (hidx : idx < 32768) :
    valAt (chunkPrimDimN 0 4 r x) idx = valAt x (r * 32768 + idx) := by
  have hps : prodShape x.shape = 131072 := by simp [hshape, prodShape]
  have hfi_bound : r * 32768 + idx < 131072 := by omega
  have hps2 : prodShape [4, 8, 64, 16] = 32768 := by simp [prodShape]
  have hchunk_shape : (chunkPrimDimN 0 4 r x).shape = [4, 8, 64, 16] := by
    simp [chunkPrimDimN, Tensor.mkShape, hshape]
  have hps_chunk : prodShape (chunkPrimDimN 0 4 r x).shape = 32768 := by
    rw [hchunk_shape]; exact hps2
  rw [valAt_of_lt _ _ (by rw [hps_chunk]; exact hidx)]
  rw [valAt_of_lt _ _ (by rw [hps]; exact hfi_bound)]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hshape, List.getD,
    List.getElem?_cons_zero,
    Option.getD_some, List.drop, List.foldl]
  have : (16 : Nat) / 4 = 4 := by norm_num
  have : (4 : Nat) * (8 * 64 * 16) = 32768 := by norm_num
  have : (16 : Nat) * (8 * 64 * 16) = 131072 := by norm_num
  have : (8 : Nat) * 64 * 16 = 8192 := by norm_num
  have hne_4 : (4 : Nat) ≠ 0 := by omega
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_32768 : (32768 : Nat) ≠ 0 := by omega
  have hne_131072 : (131072 : Nat) ≠ 0 := by omega
  have h_4x8192 : (4 : Nat) * 8192 = 32768 := by norm_num
  simp only [*, Nat.one_mul, ite_false]
  have h0 : idx / 32768 = 0 := Nat.div_eq_of_lt hidx
  have hm : idx % 32768 = idx := Nat.mod_eq_of_lt hidx
  simp only [h0, hm, Nat.zero_mul, Nat.zero_add]
  rw [show r % 4 = r from Nat.mod_eq_of_lt hr]
  have heq : (r * 4 + idx / 8192) * 8192 + idx % 8192 = r * 32768 + idx := by omega
  rw [heq, valAt_of_lt _ _ (by rw [hps]; exact hfi_bound)]

-- Helper B1: valAt of transposeAxes 2 3 for shape [16, 8, 64, 16]
private lemma valAt_transposeAxes_23_16_8_64_16 (x : Tensor) (idx : Nat)
    (hshape : x.shape = [16, 8, 64, 16]) (hidx : idx < 131072) :
    valAt (transposeAxes 2 3 x) idx =
    valAt x (idx / 8192 * 8192 + idx % 8192 / 1024 * 1024 + idx % 64 * 16 + idx % 1024 / 64) := by
  have hinner : idx / 8192 * 8192 + idx % 8192 / 1024 * 1024 + idx % 64 * 16 + idx % 1024 / 64 < 131072 := by omega
  have hps_in : prodShape x.shape = 131072 := by simp [hshape, prodShape]
  have hout_shape : (transposeAxes 2 3 x).shape = [16, 8, 16, 64] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hps_out : prodShape (transposeAxes 2 3 x).shape = 131072 := by
    rw [hout_shape]; simp [prodShape]
  rw [valAt_of_lt _ _ (by rw [hps_out]; exact hidx),
      valAt_of_lt _ _ (by rw [hps_in]; exact hinner)]
  unfold transposeAxes Tensor.mkShape
  simp only [hshape, listSwapAt, flatToMulti, valAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  have ps1 := show prodShape [8, 16, 64] = 8192 from by simp [prodShape]
  have ps2 := show prodShape [16, 64] = 1024 from by simp [prodShape]
  have ps3 := show prodShape [64] = 64 from by simp [prodShape]
  have ps4 := show prodShape ([] : List Nat) = 1 from by simp [prodShape]
  have ps5 := show prodShape [8, 64, 16] = 8192 from by simp [prodShape]
  have ps6 := show prodShape [64, 16] = 1024 from by simp [prodShape]
  have ps7 := show prodShape [16] = 16 from by simp [prodShape]
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_1024 : (1024 : Nat) ≠ 0 := by omega
  have hne_64 : (64 : Nat) ≠ 0 := by omega
  have hne_16 : (16 : Nat) ≠ 0 := by omega
  have hne_1 : (1 : Nat) ≠ 0 := by omega
  simp only [ps1, ps2, ps3, ps4,
    hne_8192, hne_1024, hne_64, hne_1, Nat.div_one, ite_false]
  have hmm1 : ∀ n, n % 8192 % 1024 = n % 1024 := fun n => by omega
  have hmm2 : ∀ n, n % 8192 % 1024 % 64 = n % 64 := fun n => by omega
  have hinner' : idx / 8192 * 8192 + (idx % 8192 / 1024 * 1024 + (idx % 64 * 16 + idx % 1024 / 64)) < 131072 := by omega
  have ps9 := show prodShape [16, 8, 64, 16] = 131072 from by simp [prodShape]
  simp [hmm1, List.set, Option.getD_some, multiToFlat, prodShape, dif_pos hinner']
  simp only [Nat.add_assoc]

-- Helper B2: valAt of transposeAxes 2 3 for shape [4, 8, 64, 16]
private lemma valAt_transposeAxes_23_4_8_64_16 (x : Tensor) (idx : Nat)
    (hshape : x.shape = [4, 8, 64, 16]) (hidx : idx < 32768) :
    valAt (transposeAxes 2 3 x) idx =
    valAt x (idx / 8192 * 8192 + idx % 8192 / 1024 * 1024 + idx % 64 * 16 + idx % 1024 / 64) := by
  have hinner : idx / 8192 * 8192 + idx % 8192 / 1024 * 1024 + idx % 64 * 16 + idx % 1024 / 64 < 32768 := by omega
  have hps_in : prodShape x.shape = 32768 := by simp [hshape, prodShape]
  have hout_shape : (transposeAxes 2 3 x).shape = [4, 8, 16, 64] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hps_out : prodShape (transposeAxes 2 3 x).shape = 32768 := by
    rw [hout_shape]; simp [prodShape]
  rw [valAt_of_lt _ _ (by rw [hps_out]; exact hidx),
      valAt_of_lt _ _ (by rw [hps_in]; exact hinner)]
  unfold transposeAxes Tensor.mkShape
  simp only [hshape, listSwapAt, flatToMulti, valAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  have ps1 := show prodShape [8, 16, 64] = 8192 from by simp [prodShape]
  have ps2 := show prodShape [16, 64] = 1024 from by simp [prodShape]
  have ps3 := show prodShape [64] = 64 from by simp [prodShape]
  have ps4 := show prodShape ([] : List Nat) = 1 from by simp [prodShape]
  have ps5 := show prodShape [8, 64, 16] = 8192 from by simp [prodShape]
  have ps6 := show prodShape [64, 16] = 1024 from by simp [prodShape]
  have ps7 := show prodShape [16] = 16 from by simp [prodShape]
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_1024 : (1024 : Nat) ≠ 0 := by omega
  have hne_64 : (64 : Nat) ≠ 0 := by omega
  have hne_16 : (16 : Nat) ≠ 0 := by omega
  have hne_1 : (1 : Nat) ≠ 0 := by omega
  simp only [ps1, ps2, ps3, ps4, hne_8192, hne_1024, hne_64, hne_1, Nat.div_one, ite_false]
  have hmm1 : ∀ n, n % 8192 % 1024 = n % 1024 := fun n => by omega
  have hmm2 : ∀ n, n % 8192 % 1024 % 64 = n % 64 := fun n => by omega
  have hinner' : idx / 8192 * 8192 + (idx % 8192 / 1024 * 1024 + (idx % 64 * 16 + idx % 1024 / 64)) < 32768 := by omega
  have ps11 := show prodShape [4, 8, 64, 16] = 32768 from by simp [prodShape]
  simp [hmm1, List.set, Option.getD_some, multiToFlat, prodShape, dif_pos hinner']
  simp only [Nat.add_assoc]

-- Helper C: valAt of allGatherPrimDimN 0 4 for piece shape [4, 8, 16, 64]
private lemma valAt_allGatherPrimDimN_0_4_32768
    (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 8, 16, 64])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 131072 / 8192 / 4) (zeroTensor [4, 8, 16, 64]))
      ((idx / 8192 % 4) * 8192 + idx % 8192) := by
  have h4x4 : (4 : Nat) * 4 = 16 := by norm_num
  have h4x8192 : (4 : Nat) * 8192 = 32768 := by norm_num
  have h16x8192 : (16 : Nat) * 8192 = 131072 := by norm_num
  have h_ps_out : prodShape [16, 8, 16, 64] = 131072 := by simp [prodShape]
  have hmm_131072 : idx % 131072 = idx := Nat.mod_eq_of_lt hidx
  have hdiv_131072 : idx / 131072 = 0 := Nat.div_eq_of_lt hidx
  unfold allGatherPrimDimN
  rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps_out, List.getD, List.drop, List.foldl, List.length,
    List.getElem?_cons_zero,
    h4x4, h4x8192, h16x8192, hmm_131072, hdiv_131072,
    dif_pos hidx]

-- Main index arithmetic: LHS index = RHS composed index
theorem transposeAxes_23_chunkPrimDimN0_gather0
    (x : Tensor) (hshape : x.shape = [16, 8, 64, 16]) :
    transposeAxes 2 3 x = allGatherPrimDimN 0 4 0
      [transposeAxes 2 3 (chunkPrimDimN 0 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 3 x)] := by
  have hpiece_shape : ∀ r, (transposeAxes 2 3 (chunkPrimDimN 0 4 r x)).shape = [4, 8, 16, 64] := by
    intro r; simp [transposeAxes, chunkPrimDimN, Tensor.mkShape, listSwapAt, hshape]
  have hLHS_shape : (transposeAxes 2 3 x).shape = [16, 8, 16, 64] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hhead : (([transposeAxes 2 3 (chunkPrimDimN 0 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 3 x)].head?.map (fun t => t.shape)).getD []) =
       [4, 8, 16, 64] := by
    simp [List.head?, Option.map, hpiece_shape]
  have hRHS_shape : (allGatherPrimDimN 0 4 0
      [transposeAxes 2 3 (chunkPrimDimN 0 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 0 4 3 x)]).shape = [16, 8, 16, 64] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hpiece_shape]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 131072 := by simpa [prodShape] using hidx
  -- LHS: use helper B1 (shape [16, 8, 64, 16])
  rw [valAt_transposeAxes_23_16_8_64_16 x idx hshape hidx']
  -- RHS: use helper C (unsimplified form)
  rw [valAt_allGatherPrimDimN_0_4_32768 _ idx hhead hidx']
  -- RHS now: valAt (pieces.getD (idx % 131072 / 8192 / 4) ...) ((idx / 8192 % 4) * 8192 + idx % 8192)
  have hmm : idx % 131072 = idx := Nat.mod_eq_of_lt hidx'
  have hchunk_shape : ∀ r, (chunkPrimDimN 0 4 r x).shape = [4, 8, 64, 16] := by
    intro r; simp [chunkPrimDimN, Tensor.mkShape, hshape]
  have hlocal_bound : (idx / 8192 % 4) * 8192 + idx % 8192 < 32768 := by omega
  have hr_cases : idx / 8192 / 4 = 0 ∨ idx / 8192 / 4 = 1 ∨ idx / 8192 / 4 = 2 ∨ idx / 8192 / 4 = 3 := by omega
  -- Rewrite piece index: idx % 131072 / 8192 / 4 = idx / 8192 / 4 (since idx % 131072 = idx)
  simp only [hmm]
  rcases hr_cases with h | h | h | h <;>
  · simp only [h, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [valAt_transposeAxes_23_4_8_64_16 _ _ (hchunk_shape _) hlocal_bound]
    rw [valAt_chunkPrimDimN_0_4 x _ _ hshape (by omega) (by
      have : (idx / 8192 % 4) * 8192 + idx % 8192 < 32768 := hlocal_bound
      have ht := @valAt_transposeAxes_23_4_8_64_16
      omega)]
    exact congr_arg (valAt x) (by
      have h1 : idx / 8192 = idx / 32768 * 4 + idx % 32768 / 8192 := by omega
      have h2 : idx % 32768 % 8192 = idx % 8192 := by omega
      have h3 : idx % 32768 % 64 = idx % 64 := by omega
      have h4 : idx % 32768 % 1024 = idx % 1024 := by omega
      omega)

/-- `chunkPrimDimN 3` on a 4D tensor equals `chunkPrim` (both chunk the last dim).
    Concrete version for numParts = 4 and shape [16, 64, 8, 16]. -/
theorem chunkPrimDimN_3_eq_chunkPrim_16_64_8_16
    (rank : Nat) (x : Tensor) (hsh : x.shape = [16, 64, 8, 16]) :
    chunkPrimDimN 3 4 rank x = chunkPrim 4 rank x := by
  apply Tensor.ext
  · simp [chunkPrimDimN, chunkPrim, Tensor.mkShape, hsh,
          List.set, List.getD, List.drop, dropLast, lastD, appendLast, divNat]
  · intro idx hidx
    have hsh_dimN : (chunkPrimDimN 3 4 rank x).shape = [16, 64, 8, 4] := by
      simp [chunkPrimDimN, Tensor.mkShape, hsh, List.set, List.getD]
    have hsh_prim : (chunkPrim 4 rank x).shape = [16, 64, 8, 4] := by
      simp [chunkPrim, Tensor.mkShape, hsh, dropLast, lastD, appendLast, divNat]
    rw [hsh_dimN] at hidx
    have hidx32k : idx < 32768 := by simpa [prodShape] using hidx
    rw [valAt_of_lt _ _ (by rw [hsh_dimN]; simpa [prodShape]),
        valAt_of_lt _ _ (by rw [hsh_prim]; simpa [prodShape])]
    unfold chunkPrimDimN chunkPrim Tensor.mkShape
    simp only [hsh, List.getD, List.drop, List.foldl, lastD, divNat,
               show ¬(4 : Nat) = 0 from by omega,
               show ¬(1 : Nat) = 0 from by omega,
               ite_false]
    -- Reduce stuck list index operations
    have h1 : ([16, 64, 8, 16] : List Nat)[3]?.getD 0 = 16 := by decide
    have h2 : ([16, 64, 8, 16] : List Nat).getLastD 0 = 16 := by decide
    simp only [h1, h2, show (16 : Nat) / 4 = 4 from by omega, show ¬(4 : Nat) = 0 from by omega,
               ite_false, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]
    congr 1; omega

/-- Wrapper for `transposeAxes_12_chunkPrim_gather3` using `chunkPrimDimN 3`. -/
theorem transposeAxes_12_chunkPrimDimN3_gather3
    (x : Tensor) (hshape : x.shape = [16, 64, 8, 16]) :
    transposeAxes 1 2 x = allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)] := by
  simp only [chunkPrimDimN_3_eq_chunkPrim_16_64_8_16 _ x hshape]
  exact transposeAxes_12_chunkPrim_gather3 x hshape

/-! ## Gather-chunk dim3 roundtrip for shape [16, 8, 64, 64] -/

lemma valAt_ag3_np4 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 8, 64, 16])
    (hidx : idx < 524288) :
    valAt (allGatherPrimDimN 3 4 0 xs) idx =
    valAt (xs.getD (idx % 64 / 16) (zeroTensor [16, 8, 64, 16]))
      (idx / 64 * 16 + idx % 16) := by
  have hshape_out : (allGatherPrimDimN 3 4 0 xs).shape = [16, 8, 64, 64] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : idx < prodShape (allGatherPrimDimN 3 4 0 xs).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]; omega
  rw [valAt_of_lt _ _ hlt_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [show (16 : Nat) * 4 = 64 from by norm_num,
    show (16 : Nat) * 1 = 16 from by norm_num,
    (show (64 : Nat) ≠ 0 by omega), (show (1 : Nat) ≠ 0 by omega),
    (show (16 : Nat) ≠ 0 by omega),
    ite_false]
  simp only [show ∀ n, n % 64 / 1 / 16 = n % 64 / 16 from fun n => by omega,
    show ∀ n, n / 64 * 16 + (n % 64 / 1) % 16 * 1 + n % 64 % 1 =
      n / 64 * 16 + n % 16 from fun n => by omega]

lemma valAt_chunk3_np4 (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 8, 64, 64]) (hidx : idx < 131072) :
    valAt (chunkPrimDimN 3 4 r x) idx =
    valAt x (idx / 16 * 64 + (r % 4) * 16 + idx % 16) := by
  unfold chunkPrimDimN; rw [hshape]
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD, List.drop, List.foldl, List.set]
  norm_num
  conv_lhs => rw [show (if (4 : Nat) = 0 then (0 : Nat) else 64 / 4) = 16 from by decide]
  simp only [valAt, Tensor.mkShape,
    show prodShape [16, 8, 64, 16] = 131072 from by simp [prodShape]]
  rw [dif_pos hidx]
  exact congrArg (valAt x) (by omega)

theorem gather_chunk_dim3 (x : Tensor) (hshape : x.shape = [16, 8, 64, 64]) :
    allGatherPrimDimN 3 4 0 [chunkPrimDimN 3 4 0 x, chunkPrimDimN 3 4 1 x,
      chunkPrimDimN 3 4 2 x, chunkPrimDimN 3 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 3 4 r x).shape = [16, 8, 64, 16] := by
    intro r; rw [chunkPrimDimN_shape 3 4 r _ _ hshape (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 3 4 0 x, chunkPrimDimN 3 4 1 x,
      chunkPrimDimN 3 4 2 x, chunkPrimDimN 3 4 3 x].head?.map (·.shape)).getD []) =
      [16, 8, 64, 16] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  apply Tensor.ext
  · rw [allGatherPrimDimN_shape 3 4 _ _ hhead]; simp [List.set, List.getD, hshape]
  · intro idx hidx
    have hidx' : idx < 524288 := by
      rw [allGatherPrimDimN_shape 3 4 _ _ hhead] at hidx
      simp [List.set, List.getD, prodShape] at hidx; omega
    rw [valAt_ag3_np4 _ idx hhead hidx']
    set p := idx % 64 / 16 with hp_def
    have hp_range : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
    rcases hp_range with h | h | h | h <;>
      simp only [h, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD] <;>
      rw [valAt_chunk3_np4 x _ _ hshape (by omega)] <;>
      exact congrArg (valAt x) (by omega)

theorem scalarDiv_ag3_comm (x0 x1 x2 x3 : Tensor) (c : Scalar)
    (h0 : x0.shape = [16, 8, 64, 16]) :
    scalarDiv (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3]) c =
    allGatherPrimDimN 3 4 0 [scalarDiv x0 c, scalarDiv x1 c,
      scalarDiv x2 c, scalarDiv x3 c] := by
  have hhead_x : (([x0, x1, x2, x3].head?.map (·.shape)).getD []) = [16, 8, 64, 16] := by
    simp [List.head?, Option.map, h0]
  have hhead_sd : (([scalarDiv x0 c, scalarDiv x1 c, scalarDiv x2 c,
      scalarDiv x3 c].head?.map (·.shape)).getD []) = [16, 8, 64, 16] := by
    simp [List.head?, Option.map, scalarDiv, Tensor.mkShape, h0]
  have hLHS_shape : (scalarDiv (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3]) c).shape =
      [16, 8, 64, 64] := by
    simp only [scalarDiv, Tensor.mkShape, Fin.is_lt, valAt_of_lt, Fin.eta]
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_x]; simp [List.set, List.getD]
  have hRHS_shape : (allGatherPrimDimN 3 4 0 [scalarDiv x0 c, scalarDiv x1 c,
      scalarDiv x2 c, scalarDiv x3 c]).shape = [16, 8, 64, 64] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_sd]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 524288 := by simpa [prodShape] using hidx
  rw [valAt_scalarDiv]
  rw [valAt_ag3_np4 _ _ hhead_x hidx']
  rw [valAt_ag3_np4 _ _ hhead_sd hidx']
  have hr_cases : idx % 64 / 16 = 0 ∨ idx % 64 / 16 = 1 ∨
      idx % 64 / 16 = 2 ∨ idx % 64 / 16 = 3 := by omega
  rcases hr_cases with h | h | h | h <;>
  · simp only [h, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    exact (valAt_scalarDiv _ c _).symm

/-! ## Shared shape lemmas -/

theorem batchedMatmul_4d_shape (x y : Tensor) (d0 d1 n k m : Nat)
    (hx : x.shape = [d0, d1, n, k]) (hy : y.shape = [d0, d1, k, m]) :
    (batchedMatmul x y).shape = [d0, d1, n, m] := by
  unfold batchedMatmul; rw [hx, hy]; simp [Tensor.mkShape]

theorem transpose2d_4d_shape (x : Tensor) (d0 d1 d2 d3 : Nat)
    (hx : x.shape = [d0, d1, d2, d3]) :
    (transpose2d x).shape = [d0, d1, d3, d2] := by
  unfold transpose2d; rw [hx]; simp [Tensor.mkShape]

/-! ## Shared valAt lemmas for allGatherPrimDimN -/

lemma valAt_gd0_4_64_128 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 64, 128])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 131072 / 8192 / 4) (zeroTensor [4, 64, 128]))
      ((idx / 8192 % 4) * 8192 + idx % 8192) := by
  unfold allGatherPrimDimN; rw [hhead]
  simp only [valAt, Tensor.mkShape, List.getD, List.getElem?_cons_zero, Option.getD_some,
    Nat.reduceMul, List.set_cons_zero, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, show (4 : Nat) * 4 = 16 from by norm_num,
    List.drop, List.foldl_cons, List.foldl, one_mul,
    show (16 : Nat) * 8192 = 131072 from by norm_num, OfNat.ofNat_ne_zero, ↓reduceIte,
    show (4 : Nat) * 8192 = 32768 from by norm_num, Nat.reduceDvd, Nat.mod_mod_of_dvd, ↓dreduceIte,
    List.drop_succ_cons, List.drop_zero, List.foldl_nil,
    show prodShape [16, 64, 128] = 131072 from by simp [prodShape], Lean.Elab.WF.paramLet,
    zero_mul, Nat.div_eq_of_lt hidx, Nat.mod_eq_of_lt hidx, dif_pos hidx]

lemma valAt_gd0_4_8_64_64 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 8, 64, 64])
    (hidx : idx < 524288) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 524288 / 32768 / 4) (zeroTensor [4, 8, 64, 64]))
      ((idx / 32768 % 4) * 32768 + idx % 32768) := by
  have h4x4 : (4 : Nat) * 4 = 16 := by norm_num
  have h4x32768 : (4 : Nat) * 32768 = 131072 := by norm_num
  have h16x32768 : (16 : Nat) * 32768 = 524288 := by norm_num
  have h_ps_out : prodShape [16, 8, 64, 64] = 524288 := by simp [prodShape]
  have hmm : idx % 524288 = idx := Nat.mod_eq_of_lt hidx
  have hdv : idx / 524288 = 0 := Nat.div_eq_of_lt hidx
  unfold allGatherPrimDimN; rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps_out, List.getD, List.drop, List.foldl,
    List.length, List.getElem?_cons_zero,
    h4x4, h4x32768, h16x32768, hmm, hdv, dif_pos hidx]

lemma valAt_gd0_4_8_16_64 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 8, 16, 64])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 131072 / 8192 / 4) (zeroTensor [4, 8, 16, 64]))
      ((idx / 8192 % 4) * 8192 + idx % 8192) := by
  have h4x4 : (4 : Nat) * 4 = 16 := by norm_num
  have h4x8192 : (4 : Nat) * 8192 = 32768 := by norm_num
  have h16x8192 : (16 : Nat) * 8192 = 131072 := by norm_num
  have h_ps_out : prodShape [16, 8, 16, 64] = 131072 := by simp [prodShape]
  have hmm : idx % 131072 = idx := Nat.mod_eq_of_lt hidx
  have hdv : idx / 131072 = 0 := Nat.div_eq_of_lt hidx
  unfold allGatherPrimDimN; rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps_out, List.getD, List.drop, List.foldl,
    List.length, List.getElem?_cons_zero,
    h4x4, h4x8192, h16x8192, hmm, hdv, dif_pos hidx]

/-! ## Shared valAt lemmas for transposeAxes -/

lemma valAt_ta12_16_8_64_16 (x : Tensor) (idx : Nat)
    (hshape : x.shape = [16, 8, 64, 16]) (hidx : idx < 131072) :
    valAt (transposeAxes 1 2 x) idx =
    valAt x (idx / 8192 * 8192 + idx % 128 / 16 * 1024 +
             idx % 8192 / 128 * 16 + idx % 16) := by
  have hinner : idx / 8192 * 8192 + idx % 128 / 16 * 1024 +
      idx % 8192 / 128 * 16 + idx % 16 < 131072 := by omega
  have hps_in : prodShape x.shape = 131072 := by simp [hshape, prodShape]
  have hout_shape : (transposeAxes 1 2 x).shape = [16, 64, 8, 16] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hps_out : prodShape (transposeAxes 1 2 x).shape = 131072 := by
    rw [hout_shape]; simp [prodShape]
  rw [valAt_of_lt _ _ (by rw [hps_out]; exact hidx),
      valAt_of_lt _ _ (by rw [hps_in]; exact hinner)]
  unfold transposeAxes Tensor.mkShape
  simp only [hshape, listSwapAt, flatToMulti, valAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  have ps1 := show prodShape [64, 8, 16] = 8192 from by simp [prodShape]
  have ps2 := show prodShape [8, 16] = 128 from by simp [prodShape]
  have ps3 := show prodShape [16] = 16 from by simp [prodShape]
  have ps4 := show prodShape ([] : List Nat) = 1 from by simp [prodShape]
  have ps5 := show prodShape [8, 64, 16] = 8192 from by simp [prodShape]
  have ps6 := show prodShape [64, 16] = 1024 from by simp [prodShape]
  have hne_8192 : (8192 : Nat) ≠ 0 := by omega
  have hne_1024 : (1024 : Nat) ≠ 0 := by omega
  have hne_128 : (128 : Nat) ≠ 0 := by omega
  have hne_16 : (16 : Nat) ≠ 0 := by omega
  have hne_1 : (1 : Nat) ≠ 0 := by omega
  simp only [ps1, ps2, ps3, ps4, hne_8192, hne_128, hne_16, hne_1,
    Nat.div_one, ite_false]
  have hmm1 : ∀ n, n % 8192 % 128 = n % 128 := fun n => by omega
  have hmm2 : ∀ n, n % 8192 % 128 % 16 = n % 16 := fun n => by omega
  have ps_out := show prodShape [16, 8, 64, 16] = 131072 from by simp [prodShape]
  have hinner' : idx / 8192 * 8192 + (idx % 128 / 16 * 1024 +
      (idx % 8192 / 128 * 16 + idx % 16)) < 131072 := by omega
  simp [hmm1, List.set, Option.getD_some, multiToFlat, prodShape, dif_pos hinner']
  simp only [Nat.add_assoc]

/-! ## Shared valAt lemma for allGatherPrimDimN 1 -/

lemma valAt_ag1_16_2_64_16 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 2, 64, 16])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
    valAt (xs.getD (idx % 8192 / 2048) (zeroTensor [16, 2, 64, 16]))
      (idx / 8192 * 2048 + (idx % 8192 / 1024 % 2) * 1024 + idx % 1024) := by
  have hshape_out : (allGatherPrimDimN 1 4 0 xs).shape = [16, 8, 64, 16] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]; omega
  rw [valAt_of_lt _ _ hlt_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [show (1 : Nat) * 64 = 64 from by norm_num,
    show (64 : Nat) * 16 = 1024 from by norm_num,
    show (2 : Nat) * 4 = 8 from by norm_num,
    show (8 : Nat) * 1024 = 8192 from by norm_num,
    show (2 : Nat) * 1024 = 2048 from by norm_num,
    (show (8192 : Nat) ≠ 0 by omega), (show (1024 : Nat) ≠ 0 by omega),
    (show (2 : Nat) ≠ 0 by omega),
    ite_false]
  simp only [show ∀ n, n % 8192 / 1024 / 2 = n % 8192 / 2048 from fun n => by omega,
    show ∀ n, n % 8192 % 1024 = n % 1024 from fun n => by omega]


lemma valAt_chunkDimN0 (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 64, 128]) (hidx : idx < 32768) :
    valAt (chunkPrimDimN 0 4 r x) idx =
    valAt x ((r % 4) * 32768 + idx) := by
  unfold chunkPrimDimN; rw [hshape]
  simp only [List.getD, List.getElem?_cons_zero,
    Option.getD, List.drop, List.foldl, List.set]
  norm_num
  conv_lhs => rw [show (if (4 : Nat) = 0 then (0 : Nat) else 16 / 4) = 4 from by decide]
  simp only [valAt, Tensor.mkShape,
    show prodShape [4, 64, 128] = 32768 from by simp [prodShape]]
  rw [dif_pos hidx]
  exact congrArg (valAt x) (by omega)

lemma valAt_chunkDim0 (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 64, 128]) (hidx : idx < 32768) :
    valAt (chunkPrimDim0 4 r x) idx =
    valAt x ((r % 4) * 32768 + idx) := by
  unfold chunkPrimDim0; rw [hshape]
  simp only [divNat, Tensor.mkShape]
  norm_num
  simp only [valAt,
    show prodShape [4, 64, 128] = 32768 from by simp [prodShape]]
  rw [dif_pos hidx]
  exact congrArg (valAt x) (by omega)

lemma chunkPrimDimN_0_eq_chunkPrimDim0 (r : Nat) (x : Tensor)
    (hshape : x.shape = [16, 64, 128]) :
    chunkPrimDimN 0 4 r x = chunkPrimDim0 4 r x := by
  have hs1 : (chunkPrimDimN 0 4 r x).shape = [4, 64, 128] := by
    rw [chunkPrimDimN_shape 0 4 r _ _ hshape (by omega)]; simp [List.set, List.getD]
  have hs2 : (chunkPrimDim0 4 r x).shape = [4, 64, 128] :=
    chunkPrimDim0_shape' 4 r 4 64 128 x (by rw [hshape]) (by omega)
  apply Tensor.ext (by rw [hs1, hs2])
  intro idx hidx
  have hidx' : idx < 32768 := by rw [hs1] at hidx; simp [prodShape] at hidx; omega
  rw [valAt_chunkDimN0 x r idx hshape hidx', valAt_chunkDim0 x r idx hshape hidx']

lemma valAt_ag1_16_16_128 (xs : List Tensor) (addr : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 16, 128])
    (haddr : addr < 131072) :
    valAt (allGatherPrimDimN 1 4 0 xs) addr =
    valAt (xs.getD (addr % 8192 / 2048) (zeroTensor [16, 16, 128]))
      (addr / 8192 * 2048 + addr % 2048) := by
  have hshape : (allGatherPrimDimN 1 4 0 xs).shape = [16, 64, 128] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt : addr < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    simp only [hshape, prodShape, List.foldl, Nat.one_mul]; omega
  rw [valAt_of_lt _ _ hlt]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    (show (8192 : Nat) ≠ 0 by omega), (show (128 : Nat) ≠ 0 by omega),
    (show (16 : Nat) ≠ 0 by omega), ite_false,
    show ∀ n, n % 8192 % 128 = n % 128 from fun n => by omega,
    show ∀ n, n % 8192 / 128 / 16 = n % 8192 / 2048 from fun n => by omega,
    show ∀ n, n % 8192 / 128 % 16 = n % 2048 / 128 from fun n => by omega,
    show (16 : Nat) * 4 = 64 from by norm_num,
    show (1 : Nat) * 128 = 128 from by norm_num,
    show (16 : Nat) * 128 = 2048 from by norm_num,
    show (64 : Nat) * 128 = 8192 from by norm_num,
    show ∀ a n, a + n % 2048 / 128 * 128 + n % 128 = a + n % 2048 from fun a n => by
      have := Nat.div_add_mod (n % 2048) 128; omega]

lemma valAt_ag2_16_64_2_16 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 64, 2, 16])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
    valAt (xs.getD (idx % 128 / 32) (zeroTensor [16, 64, 2, 16]))
      (idx / 128 * 32 + (idx % 128 / 16 % 2) * 16 + idx % 16) := by
  have hshape_out : (allGatherPrimDimN 2 4 0 xs).shape = [16, 64, 8, 16] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt_prod : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]; omega
  rw [valAt_of_lt _ _ hlt_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [show (1 : Nat) * 16 = 16 from by norm_num,
    show (2 : Nat) * 4 = 8 from by norm_num,
    show (8 : Nat) * 16 = 128 from by norm_num,
    show (2 : Nat) * 16 = 32 from by norm_num,
    (show (128 : Nat) ≠ 0 by omega), (show (16 : Nat) ≠ 0 by omega),
    (show (2 : Nat) ≠ 0 by omega),
    ite_false]
  simp only [show ∀ n, n % 128 / 16 / 2 = n % 128 / 32 from fun n => by omega,
    show ∀ n, n % 128 % 16 = n % 16 from fun n => by omega]

lemma valAt_bwl_3d_fst (g x w : Tensor) (b s : Nat) (idx : Nat)
    (hg : g.shape = [b, s, 128]) (hx : x.shape = [b, s, 128]) (hw : w.shape = [128, 128])
    (hidx : idx < b * s * 128) (hs_pos : 0 < s) :
    valAt (bw_linear g x w).1 idx =
    ∑ j ∈ Finset.range 128,
      valAt g ((idx / (s * 128) * s + idx % (s * 128) / 128) * 128 + j) *
      valAt w (j * 128 + idx % (s * 128) % 128) := by
  have hbwl : bw_linear g x w =
      (Tensor.mkShape [b, s, 128] (fun outIdx =>
        let si := s * 128
        ∑ j ∈ Finset.range 128,
          valAt g (((if si = 0 then 0 else outIdx.1 / si) * s +
            (if (128:Nat) = 0 then 0 else (if si = 0 then 0 else outIdx.1 % si) / 128)) * 128 + j) *
          valAt w (j * 128 + (if (128:Nat) = 0 then 0 else (if si = 0 then 0 else outIdx.1 % si) % 128))),
       Tensor.mkShape [128, 128] (k_matmul_transpose (b * s) 128 128 g x)) := by
    simp [bw_linear, hg, hx, hw, Tensor.mkShape]
  rw [hbwl]
  simp [valAt, Tensor.mkShape, prodShape, List.foldl, hidx,
    (show s * 128 ≠ 0 from by omega), (show (128 : Nat) ≠ 0 from by omega)]

lemma valAt_gd0_4_64_8_16 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 64, 8, 16])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 131072 / 8192 / 4) (zeroTensor [4, 64, 8, 16]))
      ((idx / 8192 % 4) * 8192 + idx % 8192) := by
  unfold allGatherPrimDimN; rw [hhead]
  simp [valAt, Tensor.mkShape, List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero,
    show (4 : Nat) * 4 = 16 from by norm_num,
    show (4 : Nat) * 8192 = 32768 from by norm_num,
    show (16 : Nat) * 8192 = 131072 from by norm_num,
    show prodShape [16, 64, 8, 16] = 131072 from by simp [prodShape],
    Nat.mod_eq_of_lt hidx, Nat.div_eq_of_lt hidx, dif_pos hidx]

lemma valAt_gd0_4_8_64_16 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [4, 8, 64, 16])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 0 4 0 xs) idx =
    valAt (xs.getD (idx % 131072 / 8192 / 4) (zeroTensor [4, 8, 64, 16]))
      ((idx / 8192 % 4) * 8192 + idx % 8192) := by
  have h4x4 : (4 : Nat) * 4 = 16 := by norm_num
  have h4x8192 : (4 : Nat) * 8192 = 32768 := by norm_num
  have h16x8192 : (16 : Nat) * 8192 = 131072 := by norm_num
  have h_ps_out : prodShape [16, 8, 64, 16] = 131072 := by simp [prodShape]
  have hmm : idx % 131072 = idx := Nat.mod_eq_of_lt hidx
  have hdv : idx / 131072 = 0 := Nat.div_eq_of_lt hidx
  unfold allGatherPrimDimN; rw [hhead]
  simp [valAt, Tensor.mkShape, h_ps_out, List.getD, List.drop, List.foldl,
    List.length, List.getElem?_cons_zero,
    h4x4, h4x8192, h16x8192, hmm, hdv, dif_pos hidx]

lemma valAt_gd2_16_64_32 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [16, 64, 32])
    (hidx : idx < 131072) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
    valAt (xs.getD (idx % 128 / 32) (zeroTensor [16, 64, 32]))
      (idx / 128 * 32 + idx % 32) := by
  have hshape_out : (allGatherPrimDimN 2 4 0 xs).shape = [16, 64, 128] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hlt : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    simp only [hshape_out, prodShape, List.foldl, Nat.one_mul]; omega
  rw [valAt_of_lt _ _ hlt]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    show (32 : Nat) * 4 = 128 from by norm_num,
    show (1 : Nat) * 32 = 32 from by norm_num,
    show (128 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega,
    show (1 : Nat) ≠ 0 from by omega,
    ite_false,
    show ∀ n, n % 128 % 32 = n % 32 from fun n => by omega,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]

lemma valAt_ta12_16_2_64_16 (x : Tensor) (fi : Nat)
    (hshape : x.shape = [16, 2, 64, 16]) (hfi : fi < 32768) :
    valAt (transposeAxes 1 2 x) fi =
    valAt x (fi / 2048 * 2048 + fi % 32 / 16 * 1024 +
             fi % 2048 / 32 * 16 + fi % 16) := by
  have hinner : fi / 2048 * 2048 + fi % 32 / 16 * 1024 +
      fi % 2048 / 32 * 16 + fi % 16 < 32768 := by omega
  have hps_in : prodShape x.shape = 32768 := by simp [hshape, prodShape]
  have hout_shape : (transposeAxes 1 2 x).shape = [16, 64, 2, 16] := by
    simp [transposeAxes, Tensor.mkShape, listSwapAt, hshape]
  have hps_out : prodShape (transposeAxes 1 2 x).shape = 32768 := by
    rw [hout_shape]; simp [prodShape]
  rw [valAt_of_lt _ _ (by rw [hps_out]; exact hfi),
      valAt_of_lt _ _ (by rw [hps_in]; exact hinner)]
  unfold transposeAxes Tensor.mkShape
  simp only [hshape, listSwapAt, flatToMulti, valAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  have ps1 := show prodShape [2, 64, 16] = 2048 from by simp [prodShape]
  have ps2 := show prodShape [64, 16] = 1024 from by simp [prodShape]
  have ps3 := show prodShape [16] = 16 from by simp [prodShape]
  have ps4 := show prodShape ([] : List Nat) = 1 from by simp [prodShape]
  simp only [ps3, ps4,
    (show (16 : Nat) ≠ 0 by omega), (show (1 : Nat) ≠ 0 by omega),
    Nat.div_one, ite_false]
  have hmm1 : ∀ n, n % 2048 % 32 = n % 32 := fun n => by omega
  have hinner' : fi / 2048 * 2048 + (fi % 32 / 16 * 1024 +
      (fi % 2048 / 32 * 16 + fi % 16)) < 32768 := by omega
  simp [hmm1, List.set, Option.getD_some, multiToFlat, prodShape, dif_pos hinner']
  simp only [Nat.add_assoc]

lemma valAt_td_16_8_64_16 (x : Tensor) (idx : Nat)
    (hshape : x.shape = [16, 8, 64, 16]) (hidx : idx < 131072) :
    valAt (transpose2d x) idx =
    valAt x (idx / 1024 * 1024 + (idx % 1024 % 64) * 16 + idx % 1024 / 64) := by
  unfold transpose2d; rw [hshape]
  simp only [List.reverse, List.reverseAux, valAt, Tensor.mkShape]
  have hps : prodShape [16, 8, 16, 64] = 131072 := by simp [prodShape]
  rw [dif_pos (by rw [hps]; exact hidx)]
  simp only [show (64 : Nat) * 16 ≠ 0 from by omega, ite_false,
    show (64 : Nat) ≠ 0 from by omega,
    show (64 : Nat) * 16 = 1024 from by norm_num]

/-! ## Gather-chunk roundtrip helpers (shared across Goal files) -/

lemma valAt_chunk0 (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 64, 128]) (hidx : idx < 32768) :
    valAt (chunkPrimDimN 0 4 r x) idx =
    valAt x ((r % 4) * 32768 + idx) := by
  unfold chunkPrimDimN; rw [hshape]
  simp only [List.getD, List.getElem?_cons_zero,
    Option.getD, List.drop, List.foldl, List.set]
  norm_num
  conv_lhs => rw [show (if (4 : Nat) = 0 then (0 : Nat) else 16 / 4) = 4 from by decide]
  simp only [valAt, Tensor.mkShape,
    show prodShape [4, 64, 128] = 32768 from by simp [prodShape]]
  rw [dif_pos hidx]
  exact congrArg (valAt x) (by omega)

theorem gather_chunk_dim0 (T : Tensor)
    (hT : T.shape = [16, 64, 128]) :
    allGatherPrimDimN 0 4 0 [chunkPrimDimN 0 4 0 T, chunkPrimDimN 0 4 1 T,
      chunkPrimDimN 0 4 2 T, chunkPrimDimN 0 4 3 T] = T := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 0 4 r T).shape = [4, 64, 128] := by
    intro r; rw [chunkPrimDimN_shape 0 4 r _ _ hT (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 0 4 0 T, chunkPrimDimN 0 4 1 T,
      chunkPrimDimN 0 4 2 T, chunkPrimDimN 0 4 3 T].head?.map (·.shape)).getD []) =
      [4, 64, 128] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  apply Tensor.ext
  · rw [allGatherPrimDimN_shape 0 4 _ _ hhead]; simp [List.set, List.getD, hT]
  · intro idx hidx
    have hidx' : idx < 131072 := by
      rw [allGatherPrimDimN_shape 0 4 _ _ hhead] at hidx
      simp [List.set, List.getD, prodShape] at hidx; omega
    rw [valAt_gd0_4_64_128 _ idx hhead hidx']
    set p := idx % 131072 / 8192 / 4 with hp_def
    have hp_range : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
    rcases hp_range with h | h | h | h <;>
      simp only [h, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD] <;>
      rw [valAt_chunk0 T _ _ hT (by omega)] <;>
      exact congrArg (valAt T) (by omega)

lemma valAt_chunk1 (x : Tensor) (r idx : Nat)
    (hshape : x.shape = [16, 8, 64, 16]) (hidx : idx < 32768) :
    valAt (chunkPrimDimN 1 4 r x) idx =
    valAt x ((idx / 2048) * 8192 + (r % 4 * 2 + idx % 2048 / 1024) * 1024 + idx % 1024) := by
  have hinner : (idx / 2048) * 8192 + (r % 4 * 2 + idx % 2048 / 1024) * 1024 + idx % 1024 < 131072 := by omega
  have hps_in : prodShape x.shape = 131072 := by simp [hshape, prodShape]
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [16, 2, 64, 16] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hshape (by omega)]; simp [List.set, List.getD]
  have hps_out : prodShape (chunkPrimDimN 1 4 r x).shape = 32768 := by
    rw [hchunk_shape]; simp [prodShape]
  rw [valAt_of_lt _ _ (by rw [hps_out]; exact hidx),
      valAt_of_lt _ _ (by rw [hps_in]; exact hinner)]
  unfold chunkPrimDimN Tensor.mkShape valAt
  simp only [hshape, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 from by omega,
    show (2048 : Nat) ≠ 0 from by omega,
    ite_false]
  norm_num
  simp only [show prodShape [16, 8, 64, 16] = 131072 from by simp [prodShape],
    dif_pos hinner]

theorem gather_chunk_dim1 (T : Tensor)
    (hT : T.shape = [16, 8, 64, 16]) :
    allGatherPrimDimN 1 4 0 [chunkPrimDimN 1 4 0 T, chunkPrimDimN 1 4 1 T,
      chunkPrimDimN 1 4 2 T, chunkPrimDimN 1 4 3 T] = T := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r T).shape = [16, 2, 64, 16] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ hT (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 1 4 0 T, chunkPrimDimN 1 4 1 T,
      chunkPrimDimN 1 4 2 T, chunkPrimDimN 1 4 3 T].head?.map (·.shape)).getD []) =
      [16, 2, 64, 16] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  apply Tensor.ext
  · rw [allGatherPrimDimN_shape 1 4 _ _ hhead]; simp [List.set, List.getD, hT]
  · intro idx hidx
    have hidx' : idx < 131072 := by
      rw [allGatherPrimDimN_shape 1 4 _ _ hhead] at hidx
      simp [List.set, List.getD, prodShape] at hidx; omega
    rw [valAt_ag1_16_2_64_16 _ idx hhead hidx']
    set p := idx % 8192 / 2048 with hp_def
    have hp_range : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
    rcases hp_range with h | h | h | h <;>
      simp only [h, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD] <;>
      rw [valAt_chunk1 T _ _ hT (by omega)] <;>
      exact congrArg (valAt T) (by omega)

end TrainVerify.Denote.Common
