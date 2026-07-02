import denote.yoco_goals.Pattern_4

/-!
# Pattern_4 pure-math lemmas

Two building blocks used to prove `goal_4_stmt_cut`:

* `softmax_allGather2_dim0_2048_64` — softmax distributes over dim-0 all-gather
  (softmax reduces on the last dim, orthogonal to token-parallel chunking).
* `stack_allGather_commute_24_2048_64` — layer-stack and dim-0 all-gather commute
  (stacking prepends a new leading dim, turning the original dim 0 into dim 1;
  so `allGather_dim0 → stack` equals `stack → allGather_dim1`).

The concrete shape `[2048, 64]` × 24 layers × 2 ranks is exactly the shape encountered
in `sm_goal_4` / `pm_goal_4`.
-/

set_option maxHeartbeats 8000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

/-- Softmax valAt for last-dim `64`, index expressed as `row * 64 + col`. -/
theorem softmax_valAt_d64 (x : Tensor) (pre : List Nat) (idx : Nat)
    (hrev : x.shape.reverse = 64 :: pre) (hidx : idx < prodShape x.shape) :
    valAt (softmax x) idx =
      (if (∑ j ∈ Finset.range 64, expFn (valAt x (idx / 64 * 64 + j))) = 0 then 0
       else expFn (valAt x (idx / 64 * 64 + idx % 64))
            / ∑ j ∈ Finset.range 64, expFn (valAt x (idx / 64 * 64 + j))) := by
  have heq : softmax x = Tensor.mkShape x.shape (fun outIdx =>
      if (∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j))) = 0 then 0
      else expFn (valAt x (outIdx.1 / 64 * 64 + outIdx.1 % 64))
           / ∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j))) := by
    unfold softmax; rw [hrev]; rfl
  rw [heq]
  rw [valAt_of_lt _ _ (show idx < prodShape
      (Tensor.mkShape x.shape (fun outIdx =>
        if (∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j))) = 0 then 0
        else expFn (valAt x (outIdx.1 / 64 * 64 + outIdx.1 % 64))
             / ∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j)))).shape from hidx)]
  rfl

/-- **Lemma A**: softmax distributes over dim-0 all-gather for shard shape `[2048, 64]`.

    Softmax reduces on the last dim (`64` = experts), which lives entirely
    within each shard, so per-shard softmax followed by dim-0 all-gather
    equals the full softmax. -/
theorem softmax_allGather2_dim0_2048_64 (a b : Tensor)
    (ha : a.shape = [2048, 64]) (hb : b.shape = [2048, 64]) :
    softmax (allGatherPrimDimN 0 2 0 [a, b]) =
      allGatherPrimDimN 0 2 0 [softmax a, softmax b] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
    simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]; simp [List.set, List.getD]
  have hsm_shape : ∀ c : Tensor, c.shape = [2048, 64] → (softmax c).shape = [2048, 64] := by
    intro c hc; unfold softmax; rw [hc]; rfl
  have hhead_sm : (([softmax a, softmax b] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [2048, 64] := by
    simp [hsm_shape a ha]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [softmax a, softmax b]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead_sm]; simp [List.set, List.getD]
  apply Tensor.ext
  · have h1 : (softmax (allGatherPrimDimN 0 2 0 [a, b])).shape = [4096, 64] := by
      unfold softmax; rw [hG_shape]; rfl
    rw [h1, hRHS_shape]
  · intro idx hidx
    have hidx_bound : idx < 262144 := by
      have h1 : (softmax (allGatherPrimDimN 0 2 0 [a, b])).shape = [4096, 64] := by
        unfold softmax; rw [hG_shape]; rfl
      rw [h1] at hidx
      simpa [prodShape] using hidx
    have hGrev : (allGatherPrimDimN 0 2 0 [a, b]).shape.reverse = 64 :: [4096] := by
      rw [hG_shape]; rfl
    have hGprod : idx < prodShape (allGatherPrimDimN 0 2 0 [a, b]).shape := by
      rw [hG_shape]; simpa [prodShape] using hidx_bound
    rw [softmax_valAt_d64 _ [4096] idx hGrev hGprod]
    set row := idx / 64 with hrow_def
    set col := idx % 64 with hcol_def
    have hrow_lt : row < 4096 := by rw [hrow_def]; omega
    have hcol_lt : col < 64 := by rw [hcol_def]; omega
    set r := row / 2048 with hr_def
    set i := row % 2048 with hi_def
    have hr_lt : r < 2 := by rw [hr_def]; omega
    have hi_lt : i < 2048 := by rw [hi_def]; omega
    have hidx_eq : idx = (r * 2048 + i) * 64 + col := by
      rw [hr_def, hi_def, hcol_def, hrow_def]; omega
    rw [hidx_eq]
    have hRHS_val_gather :
        valAt (allGatherPrimDimN 0 2 0 [softmax a, softmax b]) ((r * 2048 + i) * 64 + col) =
        valAt (([softmax a, softmax b].getD r (zeroTensor [2048, 64]))) (i * 64 + col) := by
      apply allGatherPrimDimN0_valAt 2 2048 64 [softmax a, softmax b]
        (by omega) (by omega) (by omega) hhead_sm
      · intro r' hr'
        rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, hsm_shape a ha, hsm_shape b hb]
      · exact hr_lt
      · exact hi_lt
      · exact hcol_lt
    rw [hRHS_val_gather]
    have hgetD_sm : [softmax a, softmax b].getD r (zeroTensor [2048, 64]) =
        softmax ([a, b].getD r (zeroTensor [2048, 64])) := by
      rcases (by omega : r = 0 ∨ r = 1) with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_sm]
    set cr := [a, b].getD r (zeroTensor [2048, 64]) with hcr_def
    have hcr_shape : cr.shape = [2048, 64] := by
      rw [hcr_def]
      rcases (by omega : r = 0 ∨ r = 1) with h | h <;> rw [h] <;>
        simp [List.getD, ha, hb]
    have hcr_rev : cr.shape.reverse = 64 :: [2048] := by rw [hcr_shape]; rfl
    have hloc_lt : i * 64 + col < prodShape cr.shape := by
      rw [hcr_shape]; simp only [prodShape, List.foldl]; omega
    rw [softmax_valAt_d64 cr [2048] (i * 64 + col) hcr_rev hloc_lt]
    rw [show row = (r * 2048 + i) from by rw [hr_def, hi_def]; omega]
    have hloc_div : (i * 64 + col) / 64 = i := by omega
    have hloc_mod : (i * 64 + col) % 64 = col := by omega
    rw [hloc_div, hloc_mod]
    have hsum : (∑ j ∈ Finset.range 64,
          expFn (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * 2048 + i) * 64 + j)))
        = (∑ j ∈ Finset.range 64, expFn (valAt cr (i * 64 + j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [allGatherPrimDimN0_valAt 2 2048 64 [a, b] (by omega) (by omega) (by omega) hhead ?_ r hr_lt i hi_lt j hj]
      · intro r' hr'
        rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, ha, hb]
    have hnum :
        expFn (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * 2048 + i) * 64 + col))
      = expFn (valAt cr (i * 64 + col)) := by
      rw [allGatherPrimDimN0_valAt 2 2048 64 [a, b] (by omega) (by omega) (by omega) hhead ?_ r hr_lt i hi_lt col hcol_lt]
      · intro r' hr'
        rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, ha, hb]
    rw [hsum, hnum]

end TrainVerify.Denote.GeneratedPatterns
