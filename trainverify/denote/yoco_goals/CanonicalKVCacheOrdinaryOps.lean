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


/-! ## Layout-neutral row-local router machinery -/

/-- `f` maps `[a, d]`-shaped tensors to `[a, e]`-shaped tensors. -/
def OrdinaryRowLocalShape (f : Tensor → Tensor) (d e : Nat) : Prop :=
  ∀ (a : Nat) (x : Tensor), x.shape = [a, d] → (f x).shape = [a, e]

/-- Output row `ix` of `f x` is determined by input row `ix` of `x`: if two
(possibly differently sized) inputs agree on one whole row, the outputs agree on
the corresponding output row. -/
def OrdinaryRowLocalCongr (f : Tensor → Tensor) (d e : Nat) : Prop :=
  ∀ (a b : Nat) (x y : Tensor) (ix iy c : Nat),
    x.shape = [a, d] → y.shape = [b, d] → ix < a → iy < b → c < e →
    (∀ j, j < d → valAt x (ix * d + j) = valAt y (iy * d + j)) →
    valAt (f x) (ix * e + c) = valAt (f y) (iy * e + c)

theorem ordinary_lt_two_cases (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by omega

theorem ordinary_prodShape_2d (a b : Nat) : prodShape [a, b] = a * b := by
  simp only [prodShape, List.foldl, Nat.one_mul]

/-! ## Row-local operators commute with the CP2 dim-0 all-gather -/

theorem ordinary_rowLocal_allGather0_commute_2
    (f : Tensor → Tensor) (d e lDim : Nat)
    (hd : 0 < d) (he : 0 < e) (hl : 0 < lDim)
    (hshape : OrdinaryRowLocalShape f d e) (hcongr : OrdinaryRowLocalCongr f d e)
    (a0 a1 : Tensor)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d]) :
    f (allGatherPrimDimN 0 2 0 [a0, a1]) =
      allGatherPrimDimN 0 2 0 [f a0, f a1] := by
  have hheadA : (([a0, a1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, ha0]
  have hF0 : (f a0).shape = [lDim, e] := hshape lDim a0 ha0
  have hF1 : (f a1).shape = [lDim, e] := hshape lDim a1 ha1
  have hheadF : (([f a0, f a1].head?.map (fun t => t.shape)).getD []) =
      [lDim, e] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hF0]
  have hgetA : ∀ r (_ : r < 2),
      ([a0, a1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hgetF : ∀ r (_ : r < 2),
      ([f a0, f a1].getD r (zeroTensor [lDim, e])).shape = [lDim, e] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hF0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hF1
  have hG : (allGatherPrimDimN 0 2 0 [a0, a1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadA]
    simp only [List.set, List.getD_cons_zero]
  have hGF : (allGatherPrimDimN 0 2 0 [f a0, f a1]).shape = [lDim * 2, e] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, e] hheadF]
    simp only [List.set, List.getD_cons_zero]
  have hlhs : (f (allGatherPrimDimN 0 2 0 [a0, a1])).shape = [lDim * 2, e] :=
    hshape (lDim * 2) _ hG
  refine Tensor.ext ?_ ?_
  · rw [hlhs, hGF]
  · intro idx hidx
    rw [hlhs, ordinary_prodShape_2d] at hidx
    set row := idx / e with hrowdef
    set c := idx % e with hcdef
    have hc : c < e := Nat.mod_lt _ he
    have hrow : row < lDim * 2 := (Nat.div_lt_iff_lt_mul he).mpr hidx
    have hidxEq : idx = row * e + c := by
      rw [hrowdef, hcdef]; exact (Nat.div_add_mod' idx e).symm
    set r := row / lDim with hrdef
    set i := row % lDim with hidef
    have hi : i < lDim := Nat.mod_lt _ hl
    have hr : r < 2 := by
      rw [hrdef]
      exact (Nat.div_lt_iff_lt_mul hl).mpr (by rw [Nat.mul_comm]; exact hrow)
    have hrowEq : row = r * lDim + i := by
      rw [hrdef, hidef]; exact (Nat.div_add_mod' row lDim).symm
    have hgetAshape : ([a0, a1].getD r (zeroTensor [lDim, d])).shape =
        [lDim, d] := hgetA r hr
    have hrowVals : ∀ j, j < d →
        valAt (allGatherPrimDimN 0 2 0 [a0, a1]) (row * d + j) =
          valAt ([a0, a1].getD r (zeroTensor [lDim, d])) (i * d + j) := by
      intro j hj
      rw [hrowEq]
      exact allGatherPrimDimN0_valAt 2 lDim d [a0, a1] (by decide) hl hd
        hheadA hgetA r hr i hi j hj
    rw [hidxEq]
    rw [hcongr (lDim * 2) lDim (allGatherPrimDimN 0 2 0 [a0, a1])
      ([a0, a1].getD r (zeroTensor [lDim, d])) row i c hG hgetAshape hrow hi hc
      hrowVals]
    rw [hrowEq]
    rw [allGatherPrimDimN0_valAt 2 lDim e [f a0, f a1] (by decide) hl he
      hheadF hgetF r hr i hi c hc]
    interval_cases r
    · simp only [List.getD_cons_zero]
    · simp only [List.getD_cons_succ, List.getD_cons_zero]

/-! ## Instance 2: `fw_topk_routing` (all three outputs) -/

/-- Reduced form of `softmax` on a 2-D tensor. -/
theorem ordinary_softmax_is_2d (a d : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) :
    softmax x = Tensor.mkShape [a, d] (fun outIdx =>
      let expSum := ∑ j ∈ Finset.range d,
        expFn (valAt x (outIdx.1 / d * d + j))
      if expSum = 0 then 0
      else expFn (valAt x (outIdx.1 / d * d + outIdx.1 % d)) / expSum) := by
  have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold softmax
  rw [hx]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, if_neg hd']

theorem ordinary_softmax_valAt_2d (a d : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) (i c : Nat) (hi : i < a) (hc : c < d) :
    valAt (softmax x) (i * d + c) =
      (let expSum := ∑ j ∈ Finset.range d, expFn (valAt x (i * d + j))
       if expSum = 0 then 0 else expFn (valAt x (i * d + c)) / expSum) := by
  have hbound : i * d + c < prodShape [a, d] := by
    rw [ordinary_prodShape_2d]
    calc i * d + c < i * d + d := Nat.add_lt_add_left hc _
      _ = (i + 1) * d := by ring
      _ ≤ a * d := Nat.mul_le_mul_right _ hi
  rw [ordinary_softmax_is_2d a d x hd hx]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  have hdiv : (i * d + c) / d = i := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * d + c) % d = c := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  show (let expSum := ∑ j ∈ Finset.range d,
          expFn (valAt x ((i * d + c) / d * d + j))
        if expSum = 0 then 0
        else expFn (valAt x ((i * d + c) / d * d + (i * d + c) % d)) /
          expSum) = _
  rw [hdiv, hmod]

/-- `softmax` is row local: agreeing rows give agreeing softmax rows. -/
theorem ordinary_softmax_row_congr (a b d : Nat) (x y : Tensor) (ix iy : Nat)
    (hd : 0 < d) (hx : x.shape = [a, d]) (hy : y.shape = [b, d])
    (hix : ix < a) (hiy : iy < b)
    (hrow : ∀ j, j < d → valAt x (ix * d + j) = valAt y (iy * d + j)) :
    ∀ c, c < d → valAt (softmax x) (ix * d + c) = valAt (softmax y) (iy * d + c) := by
  intro c hc
  rw [ordinary_softmax_valAt_2d a d x hd hx ix c hix hc]
  rw [ordinary_softmax_valAt_2d b d y hd hy iy c hiy hc]
  have hsum : (∑ j ∈ Finset.range d, expFn (valAt x (ix * d + j))) =
      ∑ j ∈ Finset.range d, expFn (valAt y (iy * d + j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hrow j (Finset.mem_range.mp hj)]
  show (if _ = 0 then _ else _) = _
  rw [hsum, hrow c hc]

/-- The whole top-k row machinery only reads one row of `gate_scores`. -/
theorem ordinary_topk_row_machinery_congr (d top_k : Nat) (g h : Tensor) (l l' : Nat)
    (hrow : ∀ c, c < d → topkScoresAt g d l c = topkScoresAt h d l' c) :
    (∀ c, c < d → topkRank g d l c = topkRank h d l' c) ∧
      (∀ c, c < d → inTopK g d top_k l c = inTopK h d top_k l' c) ∧
      topkScoreSum g d top_k l = topkScoreSum h d top_k l' := by
  have hrank : ∀ c, c < d → topkRank g d l c = topkRank h d l' c := by
    intro c hc
    unfold topkRank
    congr 1
    refine Finset.filter_congr ?_
    intro e' he'
    rw [hrow e' (Finset.mem_range.mp he'), hrow c hc]
  have htop : ∀ c, c < d → inTopK g d top_k l c = inTopK h d top_k l' c := by
    intro c hc
    unfold inTopK
    rw [hrank c hc]
  refine ⟨hrank, htop, ?_⟩
  unfold topkScoreSum
  refine Finset.sum_congr rfl ?_
  intro e' he'
  have he'd := Finset.mem_range.mp he'
  rw [htop e' he'd, hrow e' he'd]

/-- Reduced form of the first output (`routing_probs`) of `fw_topk_routing`. -/
theorem ordinary_fw_topk_routing_fst_eq (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) :
    (fw_topk_routing x top_k d).1 = Tensor.mkShape [a, d] (fun outIdx =>
      if inTopK (softmax x) d top_k (outIdx.1 / d) (outIdx.1 % d) then
        (if topkScoreSum (softmax x) d top_k (outIdx.1 / d) = 0 then 0
         else topkScoresAt (softmax x) d (outIdx.1 / d) (outIdx.1 % d) /
           topkScoreSum (softmax x) d top_k (outIdx.1 / d))
      else 0) := by
  have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold fw_topk_routing
  rw [hx]
  simp only [List.head?_cons, Option.getD_some, if_neg hd']

/-- Reduced form of the second output (`routing_map`) of `fw_topk_routing`. -/
theorem ordinary_fw_topk_routing_snd_eq (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) :
    (fw_topk_routing x top_k d).2.1 = Tensor.mkShape [a, d] (fun outIdx =>
      if inTopK (softmax x) d top_k (outIdx.1 / d) (outIdx.1 % d) then 1
      else 0) := by
  have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold fw_topk_routing
  rw [hx]
  simp only [List.head?_cons, Option.getD_some, if_neg hd']

/-- Third output of `fw_topk_routing` is exactly `softmax`. -/
theorem ordinary_fw_topk_routing_thd_eq (top_k d : Nat) (x : Tensor) :
    (fw_topk_routing x top_k d).2.2 = softmax x := rfl

theorem ordinary_fw_topk_routing_fst_shape (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) : (fw_topk_routing x top_k d).1.shape = [a, d] := by
  rw [ordinary_fw_topk_routing_fst_eq a d top_k x hd hx]; rfl

theorem ordinary_fw_topk_routing_snd_shape (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) : (fw_topk_routing x top_k d).2.1.shape = [a, d] := by
  rw [ordinary_fw_topk_routing_snd_eq a d top_k x hd hx]; rfl

theorem ordinary_fw_topk_routing_fst_valAt (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) (i c : Nat) (hi : i < a) (hc : c < d) :
    valAt (fw_topk_routing x top_k d).1 (i * d + c) =
      (if inTopK (softmax x) d top_k i c then
        (if topkScoreSum (softmax x) d top_k i = 0 then 0
         else topkScoresAt (softmax x) d i c /
           topkScoreSum (softmax x) d top_k i)
      else 0) := by
  have hbound : i * d + c < prodShape [a, d] := by
    rw [ordinary_prodShape_2d]
    calc i * d + c < i * d + d := Nat.add_lt_add_left hc _
      _ = (i + 1) * d := by ring
      _ ≤ a * d := Nat.mul_le_mul_right _ hi
  have hdiv : (i * d + c) / d = i := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * d + c) % d = c := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [ordinary_fw_topk_routing_fst_eq a d top_k x hd hx]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  show (if inTopK (softmax x) d top_k ((i * d + c) / d) ((i * d + c) % d) then
      (if topkScoreSum (softmax x) d top_k ((i * d + c) / d) = 0 then 0
       else topkScoresAt (softmax x) d ((i * d + c) / d) ((i * d + c) % d) /
         topkScoreSum (softmax x) d top_k ((i * d + c) / d))
    else 0) = _
  rw [hdiv, hmod]

theorem ordinary_fw_topk_routing_snd_valAt (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) (i c : Nat) (hi : i < a) (hc : c < d) :
    valAt (fw_topk_routing x top_k d).2.1 (i * d + c) =
      (if inTopK (softmax x) d top_k i c then 1 else 0) := by
  have hbound : i * d + c < prodShape [a, d] := by
    rw [ordinary_prodShape_2d]
    calc i * d + c < i * d + d := Nat.add_lt_add_left hc _
      _ = (i + 1) * d := by ring
      _ ≤ a * d := Nat.mul_le_mul_right _ hi
  have hdiv : (i * d + c) / d = i := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * d + c) % d = c := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [ordinary_fw_topk_routing_snd_eq a d top_k x hd hx]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  show (if inTopK (softmax x) d top_k ((i * d + c) / d) ((i * d + c) % d) then
      (1 : Scalar) else 0) = _
  rw [hdiv, hmod]

/-- Common row-congruence core for the two derived `fw_topk_routing` outputs. -/
theorem ordinary_topk_scores_row_congr (a b d : Nat) (x y : Tensor) (ix iy : Nat)
    (hd : 0 < d) (hx : x.shape = [a, d]) (hy : y.shape = [b, d])
    (hix : ix < a) (hiy : iy < b)
    (hrow : ∀ j, j < d → valAt x (ix * d + j) = valAt y (iy * d + j)) :
    ∀ c, c < d →
      topkScoresAt (softmax x) d ix c = topkScoresAt (softmax y) d iy c := by
  intro c hc
  unfold topkScoresAt
  exact ordinary_softmax_row_congr a b d x y ix iy hd hx hy hix hiy hrow c hc

theorem OrdinaryRowLocalShape_topk_fst (d top_k : Nat) (hd : 0 < d) :
    OrdinaryRowLocalShape (fun x => (fw_topk_routing x top_k d).1) d d :=
  fun a x hx => ordinary_fw_topk_routing_fst_shape a d top_k x hd hx

theorem OrdinaryRowLocalShape_topk_snd (d top_k : Nat) (hd : 0 < d) :
    OrdinaryRowLocalShape (fun x => (fw_topk_routing x top_k d).2.1) d d :=
  fun a x hx => ordinary_fw_topk_routing_snd_shape a d top_k x hd hx

theorem OrdinaryRowLocalShape_topk_thd (d top_k : Nat) :
    OrdinaryRowLocalShape (fun x => (fw_topk_routing x top_k d).2.2) d d := by
  intro a x hx
  show (fw_topk_routing x top_k d).2.2.shape = [a, d]
  rw [ordinary_fw_topk_routing_thd_eq, softmax_shape_g18, hx]

theorem OrdinaryRowLocalCongr_topk_fst (d top_k : Nat) (hd : 0 < d) :
    OrdinaryRowLocalCongr (fun x => (fw_topk_routing x top_k d).1) d d := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  have hsc := ordinary_topk_scores_row_congr a b d x y ix iy hd hx hy hix hiy hrow
  obtain ⟨_, htop, hsum⟩ :=
    ordinary_topk_row_machinery_congr d top_k (softmax x) (softmax y) ix iy hsc
  rw [ordinary_fw_topk_routing_fst_valAt a d top_k x hd hx ix c hix hc]
  rw [ordinary_fw_topk_routing_fst_valAt b d top_k y hd hy iy c hiy hc]
  rw [htop c hc, hsum, hsc c hc]

theorem OrdinaryRowLocalCongr_topk_snd (d top_k : Nat) (hd : 0 < d) :
    OrdinaryRowLocalCongr (fun x => (fw_topk_routing x top_k d).2.1) d d := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  have hsc := ordinary_topk_scores_row_congr a b d x y ix iy hd hx hy hix hiy hrow
  obtain ⟨_, htop, _⟩ :=
    ordinary_topk_row_machinery_congr d top_k (softmax x) (softmax y) ix iy hsc
  rw [ordinary_fw_topk_routing_snd_valAt a d top_k x hd hx ix c hix hc]
  rw [ordinary_fw_topk_routing_snd_valAt b d top_k y hd hy iy c hiy hc]
  rw [htop c hc]

theorem OrdinaryRowLocalCongr_topk_thd (d top_k : Nat) (hd : 0 < d) :
    OrdinaryRowLocalCongr (fun x => (fw_topk_routing x top_k d).2.2) d d := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  show valAt (fw_topk_routing x top_k d).2.2 (ix * d + c) =
    valAt (fw_topk_routing y top_k d).2.2 (iy * d + c)
  rw [ordinary_fw_topk_routing_thd_eq, ordinary_fw_topk_routing_thd_eq]
  exact ordinary_softmax_row_congr a b d x y ix iy hd hx hy hix hiy hrow c hc



#print axioms ordinary_fw_rms_norm_allGather0_commute_2

end
end TrainVerify.Denote.GeneratedPatterns
