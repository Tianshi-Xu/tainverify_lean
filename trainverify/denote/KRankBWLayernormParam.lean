import denote.KRankLayernormGather

namespace TrainVerify.Denote
noncomputable section
open scoped BigOperators

-- Both parameter gradients reduce rows; only the scalar row contribution differs.
private def layernormParamOutput (isGamma : Bool) (g x gamma beta : Tensor) : Tensor :=
  if isGamma then (bw_layernorm g x gamma beta).2.1
  else (bw_layernorm g x gamma beta).2.2

private def layernormParamTerm (isGamma : Bool) (g x : Tensor)
    (d row j : Nat) : Scalar :=
  if isGamma then
    valAt g (row * d + j) *
      ((valAt x (row * d + j) - layerNormMeanAt x row d) *
        (1 / sqrtFn (layerNormVarAt x row d (layerNormMeanAt x row d) + layerNormEps)))
  else valAt g (row * d + j)

set_option maxHeartbeats 500000 in
private theorem layernormParamOutput_shape
    (isGamma : Bool) (g x gamma beta : Tensor) (b s d : Nat)
    (hx : x.shape = [b, s, d])
    (hgamma : gamma.shape = [d]) (hbeta : beta.shape = [d]) :
    (layernormParamOutput isGamma g x gamma beta).shape = [d] := by
  have hrev : x.shape.reverse = d :: [s, b] := by rw [hx]; rfl
  cases isGamma with
  | false => exact (bw_layernorm_db_shape g x gamma beta d [s, b] hrev).trans hbeta
  | true => exact (bw_layernorm_dw_shape g x gamma beta d [s, b] hrev).trans hgamma

set_option maxHeartbeats 500000 in
private theorem layernormParamOutput_valAt
    (isGamma : Bool) (g x gamma beta : Tensor) (b s d j : Nat)
    (hd : 0 < d) (hx : x.shape = [b, s, d])
    (hgamma : gamma.shape = [d]) (hbeta : beta.shape = [d]) (hj : j < d) :
    valAt (layernormParamOutput isGamma g x gamma beta) j =
      ∑ row ∈ Finset.range (b * s), layernormParamTerm isGamma g x d row j := by
  have hrev : x.shape.reverse = d :: [s, b] := by rw [hx]; rfl
  have hrows : prodShape x.shape / d = b * s := by
    rw [hx]
    simp only [prodShape, List.foldl, Nat.one_mul]
    exact Nat.mul_div_cancel (b * s) hd
  cases isGamma with
  | false =>
      change valAt (bw_layernorm g x gamma beta).2.2 j = _
      rw [bw_layernorm_db_eq g x gamma beta d [s, b] hrev]
      rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape, hbeta,
        prodShape, List.foldl, Nat.one_mul] using hj)]
      change (∑ row ∈ Finset.range (prodShape x.shape / d),
        layernormParamTerm false g x d row j) = _
      rw [hrows]
  | true =>
      change valAt (bw_layernorm g x gamma beta).2.1 j = _
      rw [bw_layernorm_dw_eq g x gamma beta d [s, b] hrev]
      rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape, hgamma,
        prodShape, List.foldl, Nat.one_mul] using hj)]
      change (∑ row ∈ Finset.range (prodShape x.shape / d),
        layernormParamTerm true g x d row j) = _
      rw [hrows]

set_option maxHeartbeats 500000 in
private theorem layernormParamTerm_gather
    (isGamma : Bool) (gs xs : List Tensor) (K b s d q r p j : Nat)
    (hK : 0 < K) (hs : 0 < s) (hd : 0 < d)
    (hq : q < b) (hr : r < K) (hp : p < s) (hj : j < d)
    (hghead : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, d])
    (hxhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, d]) :
    layernormParamTerm isGamma (allGatherPrimDimN 1 K 0 gs)
        (allGatherPrimDimN 1 K 0 xs) d (q * (s * K) + (r * s + p)) j =
      layernormParamTerm isGamma (gs.getD r (zeroTensor [b, s, d]))
        (xs.getD r (zeroTensor [b, s, d])) d (q * s + p) j := by
  have hg := allGatherPrimDimN_dim1_3d_valAt gs K b s d q r p j
    hK hs hd hq hr hp hj hghead
  cases isGamma with
  | false => exact hg
  | true =>
      dsimp only [layernormParamTerm]
      rw [hg, allGatherPrimDimN_dim1_3d_valAt xs K b s d q r p j
        hK hs hd hq hr hp hj hxhead,
        layerNormMeanAt_allGatherPrimDimN_dim1_3d xs K b s d q r p
          hK hs hd hq hr hp hxhead,
        layerNormVarAt_allGatherPrimDimN_dim1_3d xs K b s d q r p _
          hK hs hd hq hr hp hxhead]

private theorem param_map_sum_eq_range_sum
    (ts : List Tensor) (f : Tensor → Scalar) (default : Tensor) :
    (ts.map f).sum = ∑ r ∈ Finset.range ts.length, f (ts.getD r default) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map, List.sum_cons, List.length_cons]
      rw [Finset.sum_range_succ', ih]
      have h0 : (t :: ts).getD 0 default = t := by simp [List.getD]
      have hsucc : ∀ r, (t :: ts).getD (r + 1) default = ts.getD r default := by
        intro r
        simp [List.getD]
      simp only [h0, hsucc]
      rw [add_comm]

private theorem param_tensorSum_valAt (ts : List Tensor) (j : Nat)
    (hj : j < prodShape (tensorSum ts).shape) :
    valAt (tensorSum ts) j =
      ∑ r ∈ Finset.range ts.length, valAt (ts.getD r (zeroTensor [])) j := by
  have hfold : valAt (tensorSum ts) j =
      ts.foldl (fun acc t => acc + valAt t j) 0 := by
    cases ts with
    | nil => rw [valAt_of_lt _ _ hj]; rfl
    | cons t ts => rw [valAt_of_lt _ _ hj]; rfl
  rw [hfold, List.foldl_add_eq_sum]
  exact param_map_sum_eq_range_sum ts (fun t => valAt t j) (zeroTensor [])

-- The batch/rank interchange is essential: a dim-1 gather is not a flat
-- concatenation when b > 1.  Keep q outside r until the scalar sums commute.
set_option maxHeartbeats 500000 in
private theorem layernormParam_sequence_reduction_rank3
    (isGamma : Bool) (K b s d : Nat) (gs xs : List Tensor) (gamma beta : Tensor)
    (hK : 0 < K) (hs : 0 < s) (hd : 0 < d)
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [b, s, d])
    (hxsh : ∀ x ∈ xs, x.shape = [b, s, d])
    (hgamma : gamma.shape = [d]) (hbeta : beta.shape = [d]) :
    layernormParamOutput isGamma (allGatherPrimDimN 1 K 0 gs)
        (allGatherPrimDimN 1 K 0 xs) gamma beta =
      tensorSum (List.zipWith (fun g x => layernormParamOutput isGamma g x gamma beta) gs xs) := by
  classical
  have hgne : gs ≠ [] := by intro h; simp [h] at hglen; omega
  have hxne : xs ≠ [] := by intro h; simp [h] at hxlen; omega
  have hghead : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, d] := by
    obtain ⟨g, rest, rfl⟩ := List.exists_cons_of_ne_nil hgne
    exact hgsh g (by simp)
  have hxhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, d] := by
    obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hxne
    exact hxsh x (by simp)
  have hfull : (allGatherPrimDimN 1 K 0 xs).shape = [b, s * K, d] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, s, d] hxhead]
    simp [List.set, List.getD]
  let pieces := List.zipWith (fun g x => layernormParamOutput isGamma g x gamma beta) gs xs
  have hplen : pieces.length = K := by
    simp only [pieces, List.length_zipWith, hglen, hxlen, Nat.min_self]
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [d] := by
    obtain ⟨g, gr, rfl⟩ := List.exists_cons_of_ne_nil hgne
    obtain ⟨x, xr, rfl⟩ := List.exists_cons_of_ne_nil hxne
    change (layernormParamOutput isGamma g x gamma beta).shape = [d]
    exact layernormParamOutput_shape isGamma g x gamma beta b s d
      (hxsh x (by simp)) hgamma hbeta
  have hlhs : (layernormParamOutput isGamma (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) gamma beta).shape = [d] :=
    layernormParamOutput_shape isGamma _ _ gamma beta b (s * K) d hfull hgamma hbeta
  have hrhs : (tensorSum pieces).shape = [d] := by
    have hpne : pieces ≠ [] := by intro h; simp [h] at hplen; omega
    obtain ⟨t, ts, he⟩ := List.exists_cons_of_ne_nil hpne
    rw [he, tensorSum_shape]
    rw [he] at hphead
    exact hphead
  apply Tensor.ext (by rw [hlhs, hrhs])
  intro j hj
  have hjd : j < d := by
    rw [hlhs] at hj
    simpa only [prodShape, List.foldl, Nat.one_mul] using hj
  change valAt (layernormParamOutput isGamma _ _ gamma beta) j = valAt (tensorSum pieces) j
  rw [layernormParamOutput_valAt isGamma _ _ gamma beta b (s * K) d j
    hd hfull hgamma hbeta hjd,
    param_tensorSum_valAt pieces j (by rw [hrhs]; simpa only
      [prodShape, List.foldl, Nat.one_mul] using hjd), hplen]
  let F := fun row => layernormParamTerm isGamma (allGatherPrimDimN 1 K 0 gs)
    (allGatherPrimDimN 1 K 0 xs) d row j
  have hlocal : ∀ r, r < K →
      valAt (pieces.getD r (zeroTensor [])) j =
        ∑ q ∈ Finset.range b, ∑ p ∈ Finset.range s,
          F (q * (s * K) + (r * s + p)) := by
    intro r hr
    have hgr : r < gs.length := by rw [hglen]; exact hr
    have hxr : r < xs.length := by rw [hxlen]; exact hr
    have hpr : r < pieces.length := by rw [hplen]; exact hr
    have hxlocal : (xs.getD r (zeroTensor [b, s, d])).shape = [b, s, d] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr]
      exact hxsh xs[r] (List.getElem_mem hxr)
    have hget : pieces.getD r (zeroTensor []) =
        layernormParamOutput isGamma (gs.getD r (zeroTensor [b, s, d]))
          (xs.getD r (zeroTensor [b, s, d])) gamma beta := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr,
        List.getElem?_eq_getElem hgr, List.getElem?_eq_getElem hxr, Option.getD_some]
      exact List.getElem_zipWith
    rw [hget, layernormParamOutput_valAt isGamma _ _ gamma beta b s d j
      hd hxlocal hgamma hbeta hjd, Finset.sum_range_mul_eq_sum_sum b s]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro p hp
    exact (layernormParamTerm_gather isGamma gs xs K b s d q r p j
      hK hs hd (Finset.mem_range.mp hq) hr (Finset.mem_range.mp hp) hjd hghead hxhead).symm
  change (∑ row ∈ Finset.range (b * (s * K)), F row) = _
  calc
    (∑ row ∈ Finset.range (b * (s * K)), F row) =
        ∑ q ∈ Finset.range b, ∑ r ∈ Finset.range K,
          ∑ p ∈ Finset.range s, F (q * (s * K) + (r * s + p)) := by
      rw [Finset.sum_range_mul_eq_sum_sum b (s * K)]
      apply Finset.sum_congr rfl
      intro q _
      have hsplit := Finset.sum_range_mul_eq_sum_sum K s
        (fun t => F (q * (s * K) + t))
      simpa only [Nat.mul_comm K s] using hsplit
    _ = ∑ r ∈ Finset.range K, ∑ q ∈ Finset.range b,
          ∑ p ∈ Finset.range s, F (q * (s * K) + (r * s + p)) := Finset.sum_comm
    _ = ∑ r ∈ Finset.range K, valAt (pieces.getD r (zeroTensor [])) j := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hlocal r (Finset.mem_range.mp hr)).symm

set_option maxHeartbeats 500000 in
/-- Sequence-sharded LayerNorm bias gradients add across any positive rank count. -/
theorem bw_layernorm_dbeta_sequence_reduction_rank3
    (K b s d : Nat) (gs xs : List Tensor) (gamma beta : Tensor)
    (hK : 0 < K) (_hb : 0 < b) (hs : 0 < s) (hd : 0 < d)
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [b, s, d])
    (hxsh : ∀ x ∈ xs, x.shape = [b, s, d])
    (hgamma : gamma.shape = [d]) (hbeta : beta.shape = [d]) :
    (bw_layernorm (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) gamma beta).2.2 =
      tensorSum (List.zipWith (fun g x => (bw_layernorm g x gamma beta).2.2) gs xs) := by
  exact layernormParam_sequence_reduction_rank3 false K b s d gs xs gamma beta
    hK hs hd hglen hxlen hgsh hxsh hgamma hbeta

set_option maxHeartbeats 500000 in
/-- Sequence-sharded LayerNorm scale gradients add across any positive rank count.
Row means and variances are transported from the actual Denote LayerNorm kernel. -/
theorem bw_layernorm_dgamma_sequence_reduction_rank3
    (K b s d : Nat) (gs xs : List Tensor) (gamma beta : Tensor)
    (hK : 0 < K) (_hb : 0 < b) (hs : 0 < s) (hd : 0 < d)
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [b, s, d])
    (hxsh : ∀ x ∈ xs, x.shape = [b, s, d])
    (hgamma : gamma.shape = [d]) (hbeta : beta.shape = [d]) :
    (bw_layernorm (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) gamma beta).2.1 =
      tensorSum (List.zipWith (fun g x => (bw_layernorm g x gamma beta).2.1) gs xs) := by
  exact layernormParam_sequence_reduction_rank3 true K b s d gs xs gamma beta
    hK hs hd hglen hxlen hgsh hxsh hgamma hbeta

end
end TrainVerify.Denote
