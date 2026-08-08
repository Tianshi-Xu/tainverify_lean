/- Tensor-level dim-0 commute facts used by the ordinary cache-source proof. -/
import denote.Denote

set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

noncomputable section

/-- RMSNorm preserves its two-dimensional input shape. -/
theorem ordinary_fw_rms_norm_shape2 (x w : Tensor) (a b : Nat)
    (h : x.shape = [a, b]) : (fw_rms_norm x w).shape = [a, b] := by
  unfold fw_rms_norm
  rw [h]
  rfl

/-- fw_rms_norm commutes with dim-0 sharding. Row-wise reduction is
    orthogonal to dim-0 sharding, so this cleanly commutes. -/
theorem ordinary_fw_rms_norm_allGather0_commute_2 (a b w : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden]) :
    fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead]; simp [List.set, List.getD]
  have hrms_shape : ∀ c : Tensor, c.shape = [shard, hidden] → (fw_rms_norm c w).shape = [shard, hidden] := by
    intro c hc; unfold fw_rms_norm; rw [hc]; simp [Tensor.mkShape]
  have hrms_a : (fw_rms_norm a w).shape = [shard, hidden] := hrms_shape a ha
  have hrms_b : (fw_rms_norm b w).shape = [shard, hidden] := hrms_shape b hb
  have hhead_rms : (([fw_rms_norm a w, fw_rms_norm b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hrms_a]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_rms]; simp [List.set, List.getD]
  have hLHS_shape : (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w).shape = [shard * 2, hidden] := by
    unfold fw_rms_norm; rw [hG_shape]; simp [Tensor.mkShape]
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * hidden := by simpa [prodShape] using hidx
    set row := idx / hidden with hrow_def
    set j := idx % hidden with hj_def
    have hj_lt : j < hidden := by rw [hj_def]; exact Nat.mod_lt _ hhid
    have hrow_lt : row < 2 * shard := by
      rw [hrow_def]; exact Nat.div_lt_iff_lt_mul hhid |>.mpr (by linarith [hidx_bound])
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; exact Nat.div_lt_iff_lt_mul hshard |>.mpr (by linarith [hrow_lt])
    have hidx_eq : idx = (r * shard + i) * hidden + j := by
      rw [hr_def, hi_def, hj_def, hrow_def]
      have h1 : row = shard * (row / shard) + row % shard := (Nat.div_add_mod row shard).symm
      have h2 : idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
      calc idx = hidden * (idx / hidden) + idx % hidden := h2
        _ = row * hidden + j := by rw [← hrow_def, ← hj_def]; ring
        _ = (shard * (row / shard) + row % shard) * hidden + j := by rw [← h1]
        _ = (row / shard * shard + row % shard) * hidden + j := by ring
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_rms : ∀ r' (_ : r' < 2),
        (([fw_rms_norm a w, fw_rms_norm b w].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hrms_a, hrms_b]
    -- LHS at idx: unfold fw_rms_norm on the gathered tensor.
    have hLHS_val : valAt (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w) idx =
        (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx *
          (1 / sqrtFn (rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b]) (idx / hidden) hidden + rmsNormEps))) *
          valAt w (idx % hidden) := by
      unfold fw_rms_norm
      rw [show (allGatherPrimDimN 0 2 0 [a, b]).shape.reverse = hidden :: [shard * 2] from by rw [hG_shape]; rfl]
      simp only [Tensor.mkShape, valAt]
      have hidx_lt_prod : idx < prodShape (allGatherPrimDimN 0 2 0 [a, b]).shape := by
        rw [hG_shape]; simp [prodShape]; exact hidx_bound
      simp [hidx_lt_prod]
    rw [hLHS_val, hidx_eq]
    -- Show rmsMeanSqAt commutes: rmsMeanSqAt (allGather [a,b]) (r*shard+i) hidden = rmsMeanSqAt (getD r) i hidden
    have hrms_commute : rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b]) (r * shard + i) hidden =
        rmsMeanSqAt ([a, b].getD r (zeroTensor [shard, hidden])) i hidden := by
      unfold rmsMeanSqAt
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead hshapes_ab r hr_lt i hi_lt k hk]
    have hrow_div : (r * shard + i) * hidden / hidden = r * shard + i := by
      rw [Nat.mul_div_cancel _ hhid]
    have hrow_div' : ((r * shard + i) * hidden + j) / hidden = r * shard + i := by
      rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
          Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
    have hrow_mod : ((r * shard + i) * hidden + j) % hidden = j := by
      rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
    rw [hrow_div', hrow_mod]
    rw [hrms_commute]
    -- Now for allGather values.
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead hshapes_ab
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_rms_norm a w, fw_rms_norm b w]
          (by omega) hshard hhid hhead_rms hshapes_rms r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_rms : [fw_rms_norm a w, fw_rms_norm b w].getD r (zeroTensor [shard, hidden]) =
        fw_rms_norm ([a, b].getD r (zeroTensor [shard, hidden])) w := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_rms]
    -- Now unfold RHS: valAt (fw_rms_norm c w) at (i * hidden + j)
    set c := [a, b].getD r (zeroTensor [shard, hidden]) with hc_def
    have hc_shape : c.shape = [shard, hidden] := hshapes_ab r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    have h_ihidden_div : (i * hidden + j) / hidden = i := by
      rw [show i * hidden + j = j + hidden * i from by ring,
          Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
    have h_ihidden_mod : (i * hidden + j) % hidden = j := by
      rw [show i * hidden + j = j + hidden * i from by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
    unfold fw_rms_norm
    rw [show c.shape.reverse = hidden :: [shard] from by rw [hc_shape]; rfl]
    simp only [Tensor.mkShape, valAt]
    have hloc_lt_prod : i * hidden + j < prodShape c.shape := by
      rw [hc_shape]; simp [prodShape]; exact hloc_bound
    simp [hloc_lt_prod, h_ihidden_div, h_ihidden_mod]


#print axioms ordinary_fw_rms_norm_allGather0_commute_2

end
end TrainVerify.Denote.GeneratedPatterns
