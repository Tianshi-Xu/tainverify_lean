import denote.KRankBWLayernormParam

/-!
# Source LayerNorm dβ: shape-only saved inputs and ordered DP/TP reduction

Only dβ is covered: neither dX nor dγ admits this saved-X relaxation.
All public adapters require positive dimensions, the exact input-list length,
G/saved-X shapes, and full-width gamma/beta shapes. Their only value relation
is reconstruction of the *input cotangent*. No output equality is a premise.
The record list binds the four inputs of each source invocation without zip
truncation. DP is rank-major contiguous axis-0 concatenation, not TP axis-1
interleaving when B > 1. The existing arbitrary-K sequence theorem supplies
all finite-sum mathematics; the DP adapter only changes flat row views.

This is a Denote theorem, not graph/capture ownership evidence. The original
source caller is checked separately against the shared run/parameter DAG.
-/

namespace TrainVerify.Denote
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000

/-- One actual source invocation, in G, saved-X, gamma, beta order. -/
structure DbetaSourceInput where
  g : Tensor
  x : Tensor
  gamma : Tensor
  beta : Tensor

def DbetaSourceInput.Shaped (p : DbetaSourceInput) (B S H : Nat) : Prop :=
  p.g.shape = [B, S, H] ∧ p.x.shape = [B, S, H] ∧
    p.gamma.shape = [H] ∧ p.beta.shape = [H]

def DbetaSourceInput.output (p : DbetaSourceInput) : Tensor :=
  (bw_layernorm p.g p.x p.gamma p.beta).2.2

/-- Nonempty saved-X geometry is sufficient; no saved values are compared.
Gamma shape preservation is an explicit source contract, although dβ itself
never reads gamma. No positivity is needed for this denotational equality. -/
theorem bw_layernorm_dbeta_shape_only
    (g x gamma beta x' gamma' beta' : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest)
    (hx : x'.shape = x.shape) (_hgamma : gamma'.shape = gamma.shape)
    (hbeta : beta'.shape = beta.shape) :
    (bw_layernorm g x gamma beta).2.2 =
      (bw_layernorm g x' gamma' beta').2.2 := by
  rw [bw_layernorm_db_eq g x gamma beta d rest hrev,
    bw_layernorm_db_eq g x' gamma' beta' d rest (by rw [hx]; exact hrev)]
  simp only [hx]
  refine Tensor.ext (t1 := _) (t2 := _) ?_ ?_
  · exact hbeta.symm
  · intro i hi
    rw [valAt_of_lt _ _ hi, valAt_of_lt _ _ (by
      simpa only [Tensor.mkShape, hbeta] using hi)]
    rfl

-- Bounded cotangent reads plus equal row counts suffice even across reshapes.
private theorem dbeta_rank3_congr
    (a s a' s' H : Nat) (g x gamma beta g' x' gamma' beta' : Tensor)
    (hH : 0 < H) (hx : x.shape = [a, s, H]) (hx' : x'.shape = [a', s', H])
    (hb : beta.shape = [H]) (hb' : beta'.shape = [H])
    (hrows : a * s = a' * s')
    (hread : ∀ row, row < a * s → ∀ j, j < H →
      valAt g (row * H + j) = valAt g' (row * H + j)) :
    (bw_layernorm g x gamma beta).2.2 =
      (bw_layernorm g' x' gamma' beta').2.2 := by
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
  rw [bw_layernorm_db_eq _ _ _ _ H _ hrev,
    bw_layernorm_db_eq _ _ _ _ H _ hrev', hb, hb']
  refine Tensor.ext (t1 := _) (t2 := _) ?_ ?_
  · rfl
  intro j hj
  have hjH : j < H := by
    simpa only [Tensor.mkShape, prodShape, List.foldl, Nat.one_mul] using hj
  rw [valAt_of_lt _ _ hj,
    valAt_of_lt (Tensor.mkShape [H] (fun bIdx =>
      ∑ row ∈ Finset.range (prodShape x'.shape / H), valAt g' (row * H + bIdx.1))) j hj]
  change (∑ row ∈ Finset.range (prodShape x.shape / H), valAt g (row * H + j)) =
    (∑ row ∈ Finset.range (prodShape x'.shape / H), valAt g' (row * H + j))
  rw [hn, hn', ← hrows]
  exact Finset.sum_congr rfl (fun row hr => hread row (Finset.mem_range.mp hr) j hjH)

private theorem dbeta_head_shape (ts : List Tensor) (K : Nat) (sh : Shape)
    (hK : 0 < K) (hlen : ts.length = K) (hsh : ∀ t ∈ ts, t.shape = sh) :
    (ts.head?.map (fun t => t.shape)).getD [] = sh := by
  cases ts with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons t ts => exact hsh t (List.mem_cons_self)

private theorem dbeta_zip_self (ts : List Tensor) (gamma beta : Tensor) :
    List.zipWith (fun g x => (bw_layernorm g x gamma beta).2.2) ts ts =
      ts.map (fun g => (bw_layernorm g g gamma beta).2.2) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.zipWith, List.map, ih]

/-- TP/sequence adapter with independent saved-X/gamma/beta on every rank.
Only G is gathered: saved-X need not equal the gather of local saved values. -/
theorem source_bw_layernorm_dbeta_sequence_reduction
    (K B S H : Nat) (full : DbetaSourceInput) (ps : List DbetaSourceInput)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hfull : full.Shaped B (S * K) H)
    (hlen : ps.length = K) (hsh : ∀ p ∈ ps, p.Shaped B S H)
    (hpre : full.g = allGatherPrimDimN 1 K 0 (ps.map DbetaSourceInput.g)) :
    full.output = tensorSum (ps.map DbetaSourceInput.output) := by
  let gs := ps.map DbetaSourceInput.g
  have hglen : gs.length = K := by rw [List.length_map]; exact hlen
  have hgsh : ∀ g ∈ gs, g.shape = [B, S, H] := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    exact (hsh p hp).1
  have hhead := dbeta_head_shape gs K [B, S, H] hK hglen hgsh
  have hfullg : (allGatherPrimDimN 1 K 0 gs).shape = [B, S * K, H] := by
    rw [allGatherPrimDimN_shape 1 K gs [B, S, H] hhead]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
  have hcore := bw_layernorm_dbeta_sequence_reduction_rank3 K B S H gs gs
    full.gamma full.beta hK hB hS hH hglen hglen hgsh hgsh hfull.2.2.1 hfull.2.2.2
  rw [dbeta_zip_self] at hcore
  have hleft : full.output =
      (bw_layernorm (allGatherPrimDimN 1 K 0 gs)
        (allGatherPrimDimN 1 K 0 gs) full.gamma full.beta).2.2 := by
    apply dbeta_rank3_congr B (S * K) B (S * K) H _ _ _ _ _ _ _ _
      hH hfull.2.1 hfullg hfull.2.2.2 hfull.2.2.2 rfl
    intro row hr j hj
    rw [hpre]
  rw [hleft, hcore]
  apply congrArg tensorSum
  change (ps.map DbetaSourceInput.g).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  exact bw_layernorm_dbeta_shape_only p.g p.g full.gamma full.beta
    p.x p.gamma p.beta H [S, B] (by rw [(hsh p hp).1]; rfl)
    ((hsh p hp).2.1.trans (hsh p hp).1.symm)
    ((hsh p hp).2.2.1.trans hfull.2.2.1.symm)
    ((hsh p hp).2.2.2.trans hfull.2.2.2.symm)

-- A proof-only flat row view: not a source operation or a replacement denotation.
private def dbeta_flat (B S H : Nat) (g : Tensor) : Tensor :=
  Tensor.mkShape [1, B * S, H] (fun i => valAt g i.1)

private theorem dbeta_flat_read (B S H : Nat) (g : Tensor) (i : Nat)
    (hi : i < (B * S) * H) : valAt (dbeta_flat B S H g) i = valAt g i := by
  rw [valAt_of_lt _ _ (by
    simpa only [dbeta_flat, Tensor.mkShape, prodShape, List.foldl, Nat.one_mul] using hi)]
  rfl

/-- DP batch-axis-0 adapter for arbitrary positive K, B, S, H and arbitrary G.
`hpre` is ordered *input* reconstruction. There is no saved-X reconstruction,
parameter-value replication, constant-cotangent, or output-equality premise. -/
theorem source_bw_layernorm_dbeta_batch_reduction
    (K B S H : Nat) (full : DbetaSourceInput) (ps : List DbetaSourceInput)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hfull : full.Shaped (B * K) S H)
    (hlen : ps.length = K) (hsh : ∀ p ∈ ps, p.Shaped B S H)
    (hpre : full.g = allGatherPrimDimN 0 K 0 (ps.map DbetaSourceInput.g)) :
    full.output = tensorSum (ps.map DbetaSourceInput.output) := by
  let gs := ps.map DbetaSourceInput.g
  let fs := gs.map (dbeta_flat B S H)
  let fg := allGatherPrimDimN 1 K 0 fs
  have hglen : gs.length = K := by rw [List.length_map]; exact hlen
  have hflen : fs.length = K := by rw [List.length_map]; exact hglen
  have hgsh : ∀ g ∈ gs, g.shape = [B, S, H] := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    exact (hsh p hp).1
  have hfsh : ∀ f ∈ fs, f.shape = [1, B * S, H] := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    rfl
  have hghead := dbeta_head_shape gs K [B, S, H] hK hglen hgsh
  have hfhead := dbeta_head_shape fs K [1, B * S, H] hK hflen hfsh
  have hfg : fg.shape = [1, (B * S) * K, H] := by
    rw [allGatherPrimDimN_shape 1 K fs [1, B * S, H] hfhead]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
  have hgetsh : ∀ r, r < K → (gs.getD r (zeroTensor [B, S, H])).shape = [B, S, H] := by
    intro r hr
    have hrg : r < gs.length := by rw [hglen]; exact hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrg]
    exact hgsh gs[r] (List.getElem_mem hrg)
  have hget : ∀ r, r < K → fs.getD r (zeroTensor [1, B * S, H]) =
      dbeta_flat B S H (gs.getD r (zeroTensor [B, S, H])) := by
    intro r hr
    have hrg : r < gs.length := by rw [hglen]; exact hr
    have hrf : r < fs.length := by rw [hflen]; exact hr
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrg,
      List.getElem?_eq_getElem hrf, Option.getD_some]
    exact List.getElem_map (dbeta_flat B S H)
  have hleft : full.output = (bw_layernorm fg fg full.gamma full.beta).2.2 := by
    apply dbeta_rank3_congr (B * K) S 1 ((B * S) * K) H _ _ _ _ _ _ _ _
      hH hfull.2.1 hfg hfull.2.2.2 hfull.2.2.2 (by ring)
    intro row hr j hj
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
    have h0 := allGatherPrimDimN0_valAt_3D K B S H gs hK hB hS hH hghead
      hgetsh r hrK (t / S) htB (t % S) htS j hj
    have h1 := allGatherPrimDimN_dim1_3d_valAt fs K 1 (B * S) H 0 r t j
      hK hBS hH (by decide) hrK ht hj hfhead
    simp only [Nat.zero_mul, Nat.zero_add] at h1
    rw [hget r hrK, dbeta_flat_read B S H _ _ (by nlinarith [ht, hj]), hrt] at h1
    rw [hidx, hts] at h0
    rw [hpre]
    exact h0.trans h1.symm
  have hcore := bw_layernorm_dbeta_sequence_reduction_rank3 K 1 (B * S) H fs fs
    full.gamma full.beta hK (by decide) (Nat.mul_pos hB hS) hH
    hflen hflen hfsh hfsh hfull.2.2.1 hfull.2.2.2
  rw [dbeta_zip_self] at hcore
  rw [hleft, hcore]
  apply congrArg tensorSum
  change ((ps.map DbetaSourceInput.g).map (dbeta_flat B S H)).map _ = _
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro p hp
  apply dbeta_rank3_congr 1 (B * S) B S H _ _ _ _ _ _ _ _
    hH rfl (hsh p hp).2.1 hfull.2.2.2 (hsh p hp).2.2.2 (by ring)
  intro row hr j hj
  exact dbeta_flat_read B S H p.g (row * H + j) (by nlinarith [hr, hj])

#print axioms bw_layernorm_dbeta_shape_only
#print axioms source_bw_layernorm_dbeta_sequence_reduction
#print axioms source_bw_layernorm_dbeta_batch_reduction

end
end TrainVerify.Denote
