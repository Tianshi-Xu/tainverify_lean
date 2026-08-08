/- Generic dim-0 sharding theorem for the supervised CE loss head. -/
import denote.DenoteMoE

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

/-- 2-D fw_linear shape: `[b, i] × [o, i] → [b, o]`. Moved up so subsequent theorems can use it. -/
private theorem fw_linear_2d_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

/-- fw_linear commutes with dim-0 sharding — 2-shard 2D version with shape hypothesis.
    Both a, b have shape [bshard, i], w has shape [o, i]. -/
theorem fw_linear_allGather0_commute_2_of (a b w : Tensor) (bshard i o : Nat)
    (hbshard : 0 < bshard) (hi : 0 < i) (ho : 0 < o)
    (ha : a.shape = [bshard, i]) (hb : b.shape = [bshard, i])
    (hw : w.shape = [o, i]) :
    fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w] := by
  -- Shape facts
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [bshard, i] := by
    simp [ha]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [bshard * 2, i] := by
    rw [allGatherPrimDimN_shape 0 2 _ [bshard, i] hhead_ab]; simp [List.set, List.getD]
  have hlin_a : (fw_linear a w).shape = [bshard, o] := fw_linear_2d_shape bshard i o a w ha hw
  have hlin_b : (fw_linear b w).shape = [bshard, o] := fw_linear_2d_shape bshard i o b w hb hw
  have hhead_lin : (([fw_linear a w, fw_linear b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [bshard, o] := by
    simp [hlin_a]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w]).shape = [bshard * 2, o] := by
    rw [allGatherPrimDimN_shape 0 2 _ [bshard, o] hhead_lin]; simp [List.set, List.getD]
  have hLHS_shape : (fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w).shape = [bshard * 2, o] :=
    fw_linear_2d_shape (bshard * 2) i o _ w hG_ab hw
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < bshard * 2 * o := by simpa [prodShape] using houtIdx
    -- Compute both sides via k_matmul.
    have hLHS_val : valAt (fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w) outIdx
        = k_matmul (bshard * 2) o i (allGatherPrimDimN 0 2 0 [a, b]) w
            ⟨outIdx, by show outIdx < prodShape [bshard * 2, o]; simp [prodShape]; linarith⟩ := by
      rw [TrainVerify.Denote.fw_linear_is_matmul (bshard * 2) i o _ w hG_ab hw]
      rw [valAt_of_lt _ _ (by show outIdx < prodShape [bshard * 2, o]; simp [prodShape]; linarith)]
      rfl
    rw [hLHS_val]
    -- Row-major decomposition of outIdx
    set row := outIdx / o with hrow_def
    set c := outIdx % o with hc_def
    have hc_lt : c < o := by rw [hc_def]; exact Nat.mod_lt _ ho
    have hrow_lt : row < bshard * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul ho]; linarith
    set r := row / bshard with hr_def
    set il := row % bshard with hil_def
    have hil_lt : il < bshard := by rw [hil_def]; exact Nat.mod_lt _ hbshard
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hbshard]; linarith
    have houtIdx_eq : outIdx = (r * bshard + il) * o + c := by
      subst r il c row
      have h1 : bshard * (outIdx / o / bshard) + outIdx / o % bshard = outIdx / o :=
        Nat.div_add_mod (outIdx / o) bshard
      have h2 : o * (outIdx / o) + outIdx % o = outIdx := Nat.div_add_mod outIdx o
      calc outIdx = o * (outIdx / o) + outIdx % o := h2.symm
        _ = o * (bshard * (outIdx / o / bshard) + outIdx / o % bshard) + outIdx % o := by rw [h1]
        _ = (outIdx / o / bshard * bshard + outIdx / o % bshard) * o + outIdx % o := by ring
    -- k_matmul unfolds to a Finset sum. The KEY is that gather0's valAt at (row * i + j) reads
    -- from shard `r` at local (il * i + j). So both sides get same sum.
    simp [k_matmul, prodShape]
    -- Row for LHS: outIdx / o = r * bshard + il (from houtIdx_eq)
    have hout_div : outIdx / o = r * bshard + il := by
      rw [houtIdx_eq]
      have h1 : ((r * bshard + il) * o + c) / o = c / o + (r * bshard + il) := by
        rw [Nat.add_comm, Nat.add_mul_div_right c (r * bshard + il) ho]
      rw [h1, Nat.div_eq_of_lt hc_lt]; ring
    have hout_mod : outIdx % o = c := by
      rw [houtIdx_eq]
      have h1 : ((r * bshard + il) * o + c) % o = c % o := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt hc_lt]
    rw [hout_div, hout_mod]
    -- Now compute RHS at outIdx
    have hRHS_val : valAt (allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w]) outIdx
        = valAt ([fw_linear a w, fw_linear b w].getD r (zeroTensor [bshard, o])) (il * o + c) := by
      rw [houtIdx_eq]
      have hshapes_lin : ∀ r' (_ : r' < 2),
          (([fw_linear a w, fw_linear b w].getD r' (zeroTensor [bshard, o]))).shape = [bshard, o] := by
        intro r' hr'
        have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
        rcases this with h | h <;> rw [h] <;> simp [List.getD, hlin_a, hlin_b]
      exact allGatherPrimDimN0_valAt 2 bshard o [fw_linear a w, fw_linear b w]
              (by omega) hbshard ho hhead_lin hshapes_lin r hr_lt il hil_lt c hc_lt
    rw [hRHS_val]
    -- getD r resolves to fw_linear a w or fw_linear b w
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    have hgetD_lin :
        [fw_linear a w, fw_linear b w].getD r (zeroTensor [bshard, o]) =
        fw_linear ([a, b].getD r (zeroTensor [bshard, i])) w := by
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_lin]
    -- Now RHS = valAt (fw_linear e_r w) (il * o + c) where e_r = [a,b].getD r ...
    set ear := [a, b].getD r (zeroTensor [bshard, i])
    have hear_shape : ear.shape = [bshard, i] := by
      show ([a, b].getD r (zeroTensor [bshard, i])).shape = [bshard, i]
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hloc_bound : il * o + c < bshard * o := by
      have h1 : il * o + c < il * o + o := by omega
      have h2 : il * o + o = (il + 1) * o := by ring
      have h3 : (il + 1) * o ≤ bshard * o := Nat.mul_le_mul_right _ (by omega)
      omega
    have hRHS_lin_val : valAt (fw_linear ear w) (il * o + c)
        = k_matmul bshard o i ear w ⟨il * o + c, by show il * o + c < prodShape [bshard, o]; simp [prodShape]; linarith⟩ := by
      rw [TrainVerify.Denote.fw_linear_is_matmul bshard i o ear w hear_shape hw]
      rw [valAt_of_lt _ _ (by show il * o + c < prodShape [bshard, o]; simp [prodShape]; linarith)]
      rfl
    rw [hRHS_lin_val]
    -- Now both sides are k_matmul sums. Show they equal term-by-term.
    simp [k_matmul, prodShape]
    -- LHS row index: r*bshard+il; RHS row index: il (divisor bshard already gives il)
    have hil_div : (il * o + c) / o = il := by
      have h1 : (il * o + c) / o = c / o + il := by
        rw [Nat.add_comm, Nat.add_mul_div_right c il ho]
      rw [h1, Nat.div_eq_of_lt hc_lt]; ring
    have hc_mod' : c % o = c := Nat.mod_eq_of_lt hc_lt
    rw [hil_div, hc_mod']
    -- Now sum indices align. valAt gather0[a,b] ((r*bshard+il) * i + j) = valAt ear (il * i + j)
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < i := by simp [Finset.mem_range] at hj; exact hj
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [bshard, i]))).shape = [bshard, i] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    congr 1
    rw [allGatherPrimDimN0_valAt 2 bshard i [a, b]
          (by omega) hbshard hi hhead_ab hshapes_ab r hr_lt il hil_lt j hj_lt]


/-- 1-D variant of `allGatherPrimDimN0_valAt` for shape `[Lshard]`:
    at flat idx `r * Lshard + i` in output `[Lshard * 2]`, reads shard r at local idx i. -/
private theorem allGatherPrimDimN0_valAt_1d (Lshard : Nat) (hLshard : 0 < Lshard)
    (Ws : List Tensor)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard])
    (hshapes : ∀ r' (_ : r' < 2), (Ws.getD r' (zeroTensor [Lshard])).shape = [Lshard])
    (r : Nat) (hr : r < 2) (i : Nat) (hi : i < Lshard) :
    valAt (allGatherPrimDimN 0 2 0 Ws) (r * Lshard + i)
      = valAt (Ws.getD r (zeroTensor [Lshard])) i := by
  unfold allGatherPrimDimN
  rw [hhead]
  simp only [List.getD, List.drop, List.foldl]
  -- Now: valAt (mkShape [Lshard * 2] fn) (r * Lshard + i) = valAt (Ws.getD r _) i
  -- where fn outIdx computes the gathered-value via preIdx/remainder/jFull/etc.
  have hbound : r * Lshard + i < Lshard * 2 := by
    calc r * Lshard + i < r * Lshard + Lshard := by omega
      _ = (r + 1) * Lshard := by ring
      _ ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
      _ = Lshard * 2 := by ring
  rw [valAt_of_lt _ _ (by
    show r * Lshard + i < prodShape ([Lshard].set 0 (([Lshard].getD 0 0) * 2))
    simp [prodShape, List.set, List.getD]
    exact hbound)]
  simp [Tensor.mkShape, List.set, List.getD]
  -- The mkShape function computes valAt (Ws.getD r' _) (preIdx * dimStride + jLocal * postStride + k)
  -- After all simplifications with dimSize=Lshard, postStride=1, dimStride=Lshard, fullDimStride=Lshard*2:
  -- preIdx = idx / (Lshard*2) = 0 (since idx < Lshard*2)
  -- remainder = idx % (Lshard*2) = idx
  -- jFull = remainder / 1 = idx
  -- k = remainder % 1 = 0
  -- r' = jFull / Lshard = r (given hi)
  -- jLocal = jFull % Lshard = i (given hi)
  -- Reads Ws[r] at (0 * Lshard + i * 1 + 0) = i.
  have hLshard_ne : Lshard ≠ 0 := Nat.pos_iff_ne_zero.mp hLshard
  have hLshard2_ne : Lshard * 2 ≠ 0 := Nat.mul_ne_zero hLshard_ne (by omega)
  have hidx_div_full : (r * Lshard + i) / (Lshard * 2) = 0 := by
    apply Nat.div_eq_of_lt; exact hbound
  have hidx_mod_full : (r * Lshard + i) % (Lshard * 2) = r * Lshard + i := by
    apply Nat.mod_eq_of_lt; exact hbound
  have hjFull_div : (r * Lshard + i) / Lshard = r := by
    have h1 : (r * Lshard + i) / Lshard = i / Lshard + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right i r hLshard]
    rw [h1, Nat.div_eq_of_lt hi]; ring
  have hjFull_mod : (r * Lshard + i) % Lshard = i := by
    have h1 : (r * Lshard + i) % Lshard = i % Lshard := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h1, Nat.mod_eq_of_lt hi]
  have hmod1 : (r * Lshard + i) % 1 = 0 := Nat.mod_one _
  simp [hLshard_ne, hLshard2_ne, hidx_div_full, hidx_mod_full, hjFull_div, hjFull_mod, hmod1]

/-- chunkPrimDimN 1-D helper: for a `[Lfull]` tensor, `chunkPrimDimN 0 2 r y` has shape
    `[Lfull/2]` and at flat idx i reads valAt y (r * Lshard + i) where Lshard = Lfull/2. -/
private theorem chunkPrimDimN_1d_valAt (Lshard : Nat) (hLshard : 0 < Lshard)
    (y : Tensor) (hy : y.shape = [Lshard * 2])
    (r : Nat) (hr : r < 2) (i : Nat) (hi : i < Lshard) :
    valAt (chunkPrimDimN 0 2 r y) i = valAt y (r * Lshard + i) := by
  unfold chunkPrimDimN
  rw [hy]
  simp only [List.set, List.drop, List.foldl, List.getD]
  -- outShape = [Lshard*2].set 0 (Lshard*2 / 2) = [Lshard]
  have hlt : i < Lshard := hi
  have hLshard2_div : (Lshard * 2) / 2 = Lshard := by omega
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  rw [valAt_of_lt _ _ (by
    show i < prodShape ([Lshard * 2].set 0 ((Lshard * 2) / 2))
    simp [prodShape, List.set, hLshard2_div]
    exact hi)]
  simp [Tensor.mkShape, List.set, hLshard2_div, hrmod]
  -- After simp: goal becomes valAt y (r * Lshard + i)
  -- The chunkPrimDimN computes preIdx * dimStride + jFull * postStride + k
  -- For 1-D: preIdx=0, postStride=1, dimStride=Lshard*2, jFull = r*Lshard+jLocal
  -- jLocal = i % Lshard, remainder = i % Lshard, k = 0
  have hi_mod : i % Lshard = i := Nat.mod_eq_of_lt hi
  have hi_div : i / Lshard = 0 := Nat.div_eq_of_lt hi
  have hLshard_ne : Lshard ≠ 0 := Nat.pos_iff_ne_zero.mp hLshard
  have hi_mod1 : i % 1 = 0 := Nat.mod_one _
  simp [hi_mod, hi_div, hLshard_ne, hi_mod1]

/-- fw_inner_chunk_ce fst commutes with dim-0 sharding — proven for 2D input, 1D labels.
    Requires labels < vocab (well-formed training data).
    Pattern_1 usage: x_a, x_b : [Lshard=2048, h_model=1024], w : [vocab, h_model], y : [L=4096]. -/
theorem fw_inner_chunk_ce_fst_allGather0_commute_2_of (x_a x_b w y : Tensor)
    (Lshard h_model vocab : Nat)
    (hLshard : 0 < Lshard) (hh : 0 < h_model) (hvocab : 0 < vocab)
    (hxa : x_a.shape = [Lshard, h_model]) (hxb : x_b.shape = [Lshard, h_model])
    (hw : w.shape = [vocab, h_model]) (hy : y.shape = [Lshard * 2])
    (hlabels_bound : ∀ l < Lshard * 2, scalarToNat (valAt y l) < vocab)
    (zLossScale : Scalar) :
    (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst
      = allGatherPrimDimN 0 2 0
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst] := by
  -- KEY reduction: use fw_linear commute to make logits into gather0 [logits_a, logits_b] first.
  have hlin_commute : fw_linear (allGatherPrimDimN 0 2 0 [x_a, x_b]) w
      = allGatherPrimDimN 0 2 0 [fw_linear x_a w, fw_linear x_b w] :=
    fw_linear_allGather0_commute_2_of x_a x_b w Lshard h_model vocab
      hLshard hh hvocab hxa hxb hw
  -- Shape witnesses for downstream reasoning.
  have hhead_x : (([x_a, x_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [Lshard, h_model] := by
    simp [hxa]
  have hG_x : (allGatherPrimDimN 0 2 0 [x_a, x_b]).shape = [Lshard * 2, h_model] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, h_model] hhead_x]; simp [List.set, List.getD]
  have hloss_a_shape : (fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst.shape = [Lshard] := by
    unfold fw_inner_chunk_ce
    simp [Tensor.mkShape]
    rw [hxa]; rfl
  have hloss_b_shape : (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst.shape = [Lshard] := by
    unfold fw_inner_chunk_ce
    simp [Tensor.mkShape]
    rw [hxb]; rfl
  have hhead_loss : (([(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
                    (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst] : List Tensor).head?.map (fun t => t.shape)).getD [] = [Lshard] := by
    simp [hloss_a_shape]
  have hshapes_loss : ∀ r' (_ : r' < 2),
      (([(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst].getD r' (zeroTensor [Lshard]))).shape = [Lshard] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hloss_a_shape, hloss_b_shape]
  -- Fw_linear output shapes
  have hlin_a_shape : (fw_linear x_a w).shape = [Lshard, vocab] :=
    fw_linear_2d_shape Lshard h_model vocab x_a w hxa hw
  have hlin_b_shape : (fw_linear x_b w).shape = [Lshard, vocab] :=
    fw_linear_2d_shape Lshard h_model vocab x_b w hxb hw
  have hlin_G_shape : (fw_linear (allGatherPrimDimN 0 2 0 [x_a, x_b]) w).shape = [Lshard * 2, vocab] :=
    fw_linear_2d_shape (Lshard * 2) h_model vocab _ w hG_x hw
  have hhead_lin : (([fw_linear x_a w, fw_linear x_b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [Lshard, vocab] := by
    simp [hlin_a_shape]
  have hshapes_lin : ∀ r' (_ : r' < 2),
      (([fw_linear x_a w, fw_linear x_b w].getD r' (zeroTensor [Lshard, vocab]))).shape = [Lshard, vocab] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hlin_a_shape, hlin_b_shape]
  -- Now prove tensor equality via extensionality
  have hLHS_loss_shape : (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst.shape = [Lshard * 2] := by
    unfold fw_inner_chunk_ce
    simp [Tensor.mkShape]
    rw [hG_x]; rfl
  have hRHS_shape : (allGatherPrimDimN 0 2 0
      [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
       (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst]).shape = [Lshard * 2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard] hhead_loss]; simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hLHS_loss_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_loss_shape] at houtIdx
    have houtIdx_bound : outIdx < Lshard * 2 := by simpa [prodShape] using houtIdx
    -- Decompose outIdx = r * Lshard + i
    set r := outIdx / Lshard with hr_def
    set i := outIdx % Lshard with hi_def
    have hi_lt : i < Lshard := by rw [hi_def]; exact Nat.mod_lt _ hLshard
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hLshard]; linarith
    have houtIdx_eq : outIdx = r * Lshard + i := by
      have h1 : Lshard * (outIdx / Lshard) + outIdx % Lshard = outIdx := Nat.div_add_mod outIdx Lshard
      rw [hr_def, hi_def]
      calc outIdx = Lshard * (outIdx / Lshard) + outIdx % Lshard := h1.symm
        _ = outIdx / Lshard * Lshard + outIdx % Lshard := by ring
    -- LHS unfold
    have hLHS_val : valAt (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst outIdx
        = (let logits := fw_linear (allGatherPrimDimN 0 2 0 [x_a, x_b]) w
           let l := outIdx
           let labelIdx := scalarToNat (valAt y l)
           xentLogSumExp logits l vocab - valAt logits (l * vocab + labelIdx)) := by
      unfold fw_inner_chunk_ce
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show outIdx < prodShape [(allGatherPrimDimN 0 2 0 [x_a, x_b]).shape.head?.getD 0]
        rw [hG_x]; simp [prodShape]; linarith)]
    rw [hLHS_val]
    -- Rewrite logits via linear commute
    rw [hlin_commute]
    -- RHS gather at r
    rw [houtIdx_eq]
    rw [allGatherPrimDimN0_valAt_1d Lshard hLshard
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst]
        hhead_loss hshapes_loss r hr_lt i hi_lt]
    -- Get local piece
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    have hgetD_loss : ∀ r0, r0 = 0 ∨ r0 = 1 →
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst].getD r0 (zeroTensor [Lshard]) =
        (fw_inner_chunk_ce ([x_a, x_b].getD r0 (zeroTensor [Lshard, h_model])) w
             (chunkPrimDimN 0 2 r0 y) vocab zLossScale).fst := by
      intro r0 hcases
      rcases hcases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_loss r hr_cases]
    -- Unfold local fw_inner_chunk_ce
    set ea := [x_a, x_b].getD r (zeroTensor [Lshard, h_model]) with hea_def
    have hea_shape : ea.shape = [Lshard, h_model] := by
      rcases hr_cases with h | h <;> rw [hea_def] <;> rw [h] <;> simp [List.getD, hxa, hxb]
    have hlin_ea_shape : (fw_linear ea w).shape = [Lshard, vocab] :=
      fw_linear_2d_shape Lshard h_model vocab ea w hea_shape hw
    have hRHS_local_val : valAt (fw_inner_chunk_ce ea w (chunkPrimDimN 0 2 r y) vocab zLossScale).fst i
        = (let logits := fw_linear ea w
           let l := i
           let labelIdx := scalarToNat (valAt (chunkPrimDimN 0 2 r y) l)
           xentLogSumExp logits l vocab - valAt logits (l * vocab + labelIdx)) := by
      unfold fw_inner_chunk_ce
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show i < prodShape [ea.shape.head?.getD 0]
        rw [hea_shape]; simp [prodShape]; linarith)]
    rw [hRHS_local_val]
    -- Now goal shape: `xentLSE (gather[lin_a,lin_b]) outIdx vocab - valAt gather[lin_a,lin_b] (outIdx*vocab+lblG) =
    --                  xentLSE (fw_linear ea w) i vocab - valAt (fw_linear ea w) (i*vocab+lblL)`
    -- where lblG = scalarToNat (valAt y outIdx), lblL = scalarToNat (valAt (chunk y r) i)
    -- Step 1: labels match via chunk 1-D helper
    have hlabel_eq : scalarToNat (valAt y outIdx) = scalarToNat (valAt (chunkPrimDimN 0 2 r y) i) := by
      congr 1
      rw [houtIdx_eq]
      exact (chunkPrimDimN_1d_valAt Lshard hLshard y hy r hr_lt i hi_lt).symm
    -- Step 2: fw_linear commute means gather0[lin_a, lin_b] at rows r*Lshard+i correspond to
    --         fw_linear ea w at row i.
    -- Use allGatherPrimDimN0_valAt (2-D) for each valAt.
    -- For xentLogSumExp: sums over range vocab, using per-row scores.
    -- Compute: valAt (gather[lin_a,lin_b]) ((r*Lshard+i)*vocab+j) = valAt (fw_linear ea w) (i*vocab+j) for j<vocab.
    have hlin_row_eq : ∀ j, j < vocab →
        valAt (allGatherPrimDimN 0 2 0 [fw_linear x_a w, fw_linear x_b w])
              ((r * Lshard + i) * vocab + j)
          = valAt (fw_linear ea w) (i * vocab + j) := by
      intro j hj
      -- Use allGatherPrimDimN0_valAt on [fw_linear x_a w, fw_linear x_b w]
      rw [allGatherPrimDimN0_valAt 2 Lshard vocab [fw_linear x_a w, fw_linear x_b w]
          (by omega) hLshard hvocab hhead_lin hshapes_lin r hr_lt i hi_lt j hj]
      -- Show [fw_linear x_a w, fw_linear x_b w].getD r _ = fw_linear ea w (case on r)
      rcases hr_cases with h | h
      · simp [List.getD, h, hea_def]
      · simp [List.getD, h, hea_def]
    -- Step 3: Rewrite labels & LSE — no need for houtIdx_eq applied to label yet.
    -- The goal after hRHS_local_val + hlin_commute has form:
    --   LHS: xentLSE (gather0) (r*Lshard+i) vocab - valAt (gather0) ((r*Lshard+i)*vocab + scalarToNat (valAt y (r*Lshard+i)))
    --   RHS: xentLSE (fw_linear ea w) i vocab - valAt (fw_linear ea w) (i*vocab + scalarToNat (valAt (chunk y r) i))
    -- Rewrite label match:
    have hlabel_eq' : valAt y (r * Lshard + i) = valAt (chunkPrimDimN 0 2 r y) i :=
      (chunkPrimDimN_1d_valAt Lshard hLshard y hy r hr_lt i hi_lt).symm
    -- LSE equality
    have hlse_eq :
        xentLogSumExp (allGatherPrimDimN 0 2 0 [fw_linear x_a w, fw_linear x_b w]) (r * Lshard + i) vocab
          = xentLogSumExp (fw_linear ea w) i vocab := by
      unfold xentLogSumExp
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj_lt : j < vocab := by simp [Finset.mem_range] at hj; exact hj
      rw [hlin_row_eq j hj_lt]
    -- Combined final rewrite: use `simp only` to substitute in the goal
    simp only [hlabel_eq', hlse_eq]
    -- Now goal reduces to matching the loss term:
    --   valAt (gather0) ((r*Lshard+i)*vocab + lbl) = valAt (fw_linear ea w) (i*vocab + lbl)
    -- where lbl = scalarToNat (valAt (chunkPrimDimN 0 2 r y) i)
    set lbl := scalarToNat (valAt (chunkPrimDimN 0 2 r y) i) with hlbl_def
    have hlbl_lt : lbl < vocab := by
      have h_valAt_eq : valAt (chunkPrimDimN 0 2 r y) i = valAt y (r * Lshard + i) :=
        chunkPrimDimN_1d_valAt Lshard hLshard y hy r hr_lt i hi_lt
      rw [hlbl_def, h_valAt_eq]
      apply hlabels_bound
      calc r * Lshard + i < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
        _ ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
        _ = Lshard * 2 := by ring
    rw [hlin_row_eq lbl hlbl_lt]

end TrainVerify.Denote.GeneratedPatterns
