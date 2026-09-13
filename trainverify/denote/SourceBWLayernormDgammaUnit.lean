import denote.KRankBWLayernormParam

/-!
# Source LayerNorm dγ: ordered DP batch reduction

Both G and the actual saved-X are reconstructed from ordered axis-0 chunks.
Gamma and beta are shared full-width tensors. Unlike dβ, saved-X values cannot
be discarded. The only new mathematics is row-read congruence; the existing
arbitrary-K sequence theorem performs the parameter-gradient summation.
These are Denote contracts, not graph ownership/capture claims.
-/
namespace TrainVerify.Denote
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000

-- Equal row reads preserve the actual mean, variance and normalized-X term.
private theorem dgamma_rank3_congr
    (a s a' s' H : Nat) (g x g' x' gamma beta : Tensor)
    (hH : 0 < H) (hx : x.shape = [a, s, H]) (hx' : x'.shape = [a', s', H])
    (hgamma : gamma.shape = [H]) (hrows : a * s = a' * s')
    (hgread : ∀ row, row < a * s → ∀ j, j < H →
      valAt g (row * H + j) = valAt g' (row * H + j))
    (hxread : ∀ row, row < a * s → ∀ j, j < H →
      valAt x (row * H + j) = valAt x' (row * H + j)) :
    (bw_layernorm g x gamma beta).2.1 = (bw_layernorm g' x' gamma beta).2.1 := by
  have hrev : x.shape.reverse = H :: [s, a] := by rw [hx]; rfl
  have hrev' : x'.shape.reverse = H :: [s', a'] := by rw [hx']; rfl
  have hn : prodShape x.shape / H = a * s := by
    rw [hx]
    simp only [prodShape, List.foldl, Nat.one_mul]
    exact Nat.mul_div_cancel (a * s) hH
  have hn' : prodShape x'.shape / H = a' * s' := by
    rw [hx']
    simp only [prodShape, List.foldl, Nat.one_mul]
    exact Nat.mul_div_cancel (a' * s') hH
  have hm : ∀ row, row < a * s →
      layerNormMeanAt x row H = layerNormMeanAt x' row H := by
    intro row hr
    unfold layerNormMeanAt
    apply congrArg (fun z : Scalar => z / (H : Scalar))
    exact Finset.sum_congr rfl (fun j hj => hxread row hr j (Finset.mem_range.mp hj))
  have hv : ∀ row, row < a * s → ∀ mean,
      layerNormVarAt x row H mean = layerNormVarAt x' row H mean := by
    intro row hr mean
    unfold layerNormVarAt
    apply congrArg (fun z : Scalar => z / (H : Scalar))
    apply Finset.sum_congr rfl
    intro j hj
    rw [hxread row hr j (Finset.mem_range.mp hj)]
  rw [bw_layernorm_dw_eq _ _ _ _ H _ hrev,
    bw_layernorm_dw_eq _ _ _ _ H _ hrev', hgamma]
  refine Tensor.ext (t1 := _) (t2 := _) ?_ ?_
  · rfl
  intro j hj
  have hjH : j < H := by
    simpa only [Tensor.mkShape, prodShape, List.foldl, Nat.one_mul] using hj
  rw [valAt_of_lt _ _ hj,
    valAt_of_lt (Tensor.mkShape [H] (fun wIdx =>
      ∑ row ∈ Finset.range (prodShape x'.shape / H),
        valAt g' (row * H + wIdx.1) *
          ((valAt x' (row * H + wIdx.1) - layerNormMeanAt x' row H) *
            (1 / sqrtFn (layerNormVarAt x' row H (layerNormMeanAt x' row H) + layerNormEps))))) j hj]
  change (∑ row ∈ Finset.range (prodShape x.shape / H),
    valAt g (row * H + j) * ((valAt x (row * H + j) - layerNormMeanAt x row H) *
      (1 / sqrtFn (layerNormVarAt x row H (layerNormMeanAt x row H) + layerNormEps)))) =
    (∑ row ∈ Finset.range (prodShape x'.shape / H),
    valAt g' (row * H + j) * ((valAt x' (row * H + j) - layerNormMeanAt x' row H) *
      (1 / sqrtFn (layerNormVarAt x' row H (layerNormMeanAt x' row H) + layerNormEps))))
  rw [hn, hn', ← hrows]
  apply Finset.sum_congr rfl
  intro row hr
  have hr' := Finset.mem_range.mp hr
  rw [hgread row hr' j hjH, hxread row hr' j hjH, hm row hr', hv row hr']

-- Proof-only contiguous row view, not a replacement source operation.
private def dgamma_flat (B S H : Nat) (t : Tensor) : Tensor :=
  Tensor.mkShape [1, B * S, H] (fun i => valAt t i.1)

private theorem dgamma_flat_read (B S H : Nat) (t : Tensor) (i : Nat)
    (hi : i < (B * S) * H) : valAt (dgamma_flat B S H t) i = valAt t i := by
  rw [valAt_of_lt _ _ (by
    simpa only [dgamma_flat, Tensor.mkShape, prodShape, List.foldl, Nat.one_mul] using hi)]
  rfl

private theorem dgamma_head_shape (ts : List Tensor) (K : Nat) (sh : Shape)
    (hK : 0 < K) (hlen : ts.length = K) (hsh : ∀ t ∈ ts, t.shape = sh) :
    (ts.head?.map (fun t => t.shape)).getD [] = sh := by
  cases ts with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons t ts => exact hsh t List.mem_cons_self

private theorem dgamma_flat_shapes (ts : List Tensor) (B S H : Nat) :
    ∀ t ∈ ts.map (dgamma_flat B S H), t.shape = [1, B * S, H] := by
  intro t ht
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  rfl

-- Axis-0 concatenation becomes axis-1 concatenation after flattening B,S.
-- This lemma is used separately for G and saved-X, retaining both values.
private theorem dgamma_batch_flat_read
    (K B S H : Nat) (ts : List Tensor)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hlen : ts.length = K) (hsh : ∀ t ∈ ts, t.shape = [B, S, H])
    (row j : Nat) (hr : row < (B * K) * S) (hj : j < H) :
    valAt (allGatherPrimDimN 0 K 0 ts) (row * H + j) =
      valAt (allGatherPrimDimN 1 K 0 (ts.map (dgamma_flat B S H))) (row * H + j) := by
  let fs := ts.map (dgamma_flat B S H)
  have hflen : fs.length = K := by rw [List.length_map]; exact hlen
  have hhead := dgamma_head_shape ts K [B, S, H] hK hlen hsh
  have hfhead := dgamma_head_shape fs K [1, B * S, H] hK hflen
    (dgamma_flat_shapes ts B S H)
  have hgetsh : ∀ r, r < K → (ts.getD r (zeroTensor [B, S, H])).shape = [B, S, H] := by
    intro r hr
    have hrt : r < ts.length := by rw [hlen]; exact hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrt]
    exact hsh ts[r] (List.getElem_mem hrt)
  have hget : ∀ r, r < K → fs.getD r (zeroTensor [1, B * S, H]) =
      dgamma_flat B S H (ts.getD r (zeroTensor [B, S, H])) := by
    intro r hr
    have hrt : r < ts.length := by rw [hlen]; exact hr
    have hrf : r < fs.length := by rw [hflen]; exact hr
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrt,
      List.getElem?_eq_getElem hrf, Option.getD_some]
    exact List.getElem_map (dgamma_flat B S H)
  let r := row / (B * S)
  let t := row % (B * S)
  have hBS : 0 < B * S := Nat.mul_pos hB hS
  have hrow : row < K * (B * S) := by nlinarith [hr]
  have hrK : r < K := (Nat.div_lt_iff_lt_mul hBS).mpr hrow
  have ht : t < B * S := Nat.mod_lt _ hBS
  have htB : t / S < B := (Nat.div_lt_iff_lt_mul hS).mpr ht
  have htS : t % S < S := Nat.mod_lt _ hS
  have hrt : r * (B * S) + t = row := by
    dsimp only [r, t]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod row (B * S)
  have hts : t / S * S + t % S = t := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod t S
  have hidx : ((r * B + t / S) * S + t % S) * H + j = row * H + j := by
    have he : (r * B + t / S) * S + t % S = row := by
      calc
        _ = r * (B * S) + (t / S * S + t % S) := by ring
        _ = row := by rw [hts, hrt]
    rw [he]
  have h0 := allGatherPrimDimN0_valAt_3D K B S H ts hK hB hS hH hhead
    hgetsh r hrK (t / S) htB (t % S) htS j hj
  have h1 := allGatherPrimDimN_dim1_3d_valAt fs K 1 (B * S) H 0 r t j
    hK hBS hH (by decide) hrK ht hj hfhead
  simp only [Nat.zero_mul, Nat.zero_add] at h1
  rw [hget r hrK, dgamma_flat_read B S H _ _ (by nlinarith [ht, hj]), hrt] at h1
  rw [hidx, hts] at h0
  exact h0.trans h1.symm

private theorem dgamma_flat_zip
    (B S H : Nat) (gamma beta : Tensor) (hH : 0 < H) (hgamma : gamma.shape = [H])
    (gs xs : List Tensor) (hxsh : ∀ x ∈ xs, x.shape = [B, S, H]) :
    List.zipWith (fun g x => (bw_layernorm g x gamma beta).2.1)
        (gs.map (dgamma_flat B S H)) (xs.map (dgamma_flat B S H)) =
      List.zipWith (fun g x => (bw_layernorm g x gamma beta).2.1) gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          change (bw_layernorm (dgamma_flat B S H g) (dgamma_flat B S H x) gamma beta).2.1 :: _ =
            (bw_layernorm g x gamma beta).2.1 :: _
          apply congrArg₂ List.cons
          · apply dgamma_rank3_congr 1 (B * S) B S H _ _ _ _ gamma beta
              hH rfl (hxsh x List.mem_cons_self) hgamma (by ring)
            · intro row hr j hj
              exact dgamma_flat_read B S H g _ (by nlinarith [hr, hj])
            · intro row hr j hj
              exact dgamma_flat_read B S H x _ (by nlinarith [hr, hj])
          · exact ih xs (fun t ht => hxsh t (List.mem_cons_of_mem x ht))

/-- Arbitrary positive DP rank count and local batch/sequence/hidden dimensions.
The two reconstruction premises concern inputs, never the desired output.
Exact lengths prevent zip truncation; gamma/beta are shared complete tensors. -/
theorem source_bw_layernorm_dgamma_batch_reduction
    (K B S H : Nat) (g x gamma beta : Tensor) (gs xs : List Tensor)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (_hg : g.shape = [B * K, S, H]) (hx : x.shape = [B * K, S, H])
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ t ∈ gs, t.shape = [B, S, H])
    (hxsh : ∀ t ∈ xs, t.shape = [B, S, H])
    (hgamma : gamma.shape = [H]) (hbeta : beta.shape = [H])
    (hpreG : g = allGatherPrimDimN 0 K 0 gs)
    (hpreX : x = allGatherPrimDimN 0 K 0 xs) :
    (bw_layernorm g x gamma beta).2.1 =
      tensorSum (List.zipWith (fun gi xi => (bw_layernorm gi xi gamma beta).2.1) gs xs) := by
  let fgs := gs.map (dgamma_flat B S H)
  let fxs := xs.map (dgamma_flat B S H)
  have hfglen : fgs.length = K := by rw [List.length_map]; exact hglen
  have hfxlen : fxs.length = K := by rw [List.length_map]; exact hxlen
  have hfgsh := dgamma_flat_shapes gs B S H
  have hfxsh := dgamma_flat_shapes xs B S H
  have hfxhead := dgamma_head_shape fxs K [1, B * S, H] hK hfxlen hfxsh
  have hfx : (allGatherPrimDimN 1 K 0 fxs).shape = [1, (B * S) * K, H] := by
    rw [allGatherPrimDimN_shape 1 K fxs [1, B * S, H] hfxhead]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
  have hleft : (bw_layernorm g x gamma beta).2.1 =
      (bw_layernorm (allGatherPrimDimN 1 K 0 fgs)
        (allGatherPrimDimN 1 K 0 fxs) gamma beta).2.1 := by
    apply dgamma_rank3_congr (B * K) S 1 ((B * S) * K) H _ _ _ _ gamma beta
      hH hx hfx hgamma (by ring)
    · intro row hr j hj
      rw [hpreG]
      exact dgamma_batch_flat_read K B S H gs hK hB hS hH hglen hgsh row j hr hj
    · intro row hr j hj
      rw [hpreX]
      exact dgamma_batch_flat_read K B S H xs hK hB hS hH hxlen hxsh row j hr hj
  have hcore := bw_layernorm_dgamma_sequence_reduction_rank3 K 1 (B * S) H fgs fxs
    gamma beta hK (by decide) (Nat.mul_pos hB hS) hH
    hfglen hfxlen hfgsh hfxsh hgamma hbeta
  rw [hleft, hcore]
  exact congrArg tensorSum (dgamma_flat_zip B S H gamma beta hH hgamma gs xs hxsh)

#print axioms source_bw_layernorm_dgamma_batch_reduction

end
end TrainVerify.Denote
