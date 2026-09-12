import denote.KRankBWLayernorm
import denote.KRankAllToAll

/-!
# finalLN dX: a DP batch chunk followed by ordered TP sequence chunks

Edit-only candidate; parent lane owns kernel compilation and axiom audit.
The only LayerNorm mathematics used here is the public row-locality theorem.
The source input contract includes independent G and actual saved-X value
relations. The forward chain must supply saved-X reconstruction; this module
neither establishes that upstream chain nor borrows dβ's shape-only relaxation.
Shared gamma/beta are actual equal tensors, to be projected from caller frames.
No output equality, constant cotangent, or replicated saved-X is assumed.
-/
namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 800000

private theorem dx_shape (g x gamma beta : Tensor) (b s h : Nat)
    (hx : x.shape = [b, s, h]) :
    (bw_layernorm g x gamma beta).1.shape = [b, s, h] :=
  (bw_layernorm_dx_shape g x gamma beta h [s, b] (by rw [hx]; rfl)).trans hx

/-- Shape of a legal rank-three batch chunk. -/
theorem source_dx_chunk0_shape (K r b s h : Nat) (x : Tensor)
    (hK : 0 < K) (hx : x.shape = [b * K, s, h]) :
    (chunkPrimDimN 0 K r x).shape = [b, s, h] := by
  rw [chunkPrimDimN_shape 0 K r x _ hx hK.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel b hK]

/-- Shape of a legal rank-three sequence chunk. -/
theorem source_dx_chunk1_shape (K r b s h : Nat) (x : Tensor)
    (hK : 0 < K) (hx : x.shape = [b, s * K, h]) :
    (chunkPrimDimN 1 K r x).shape = [b, s, h] := by
  rw [chunkPrimDimN_shape 1 K r x _ hx hK.ne']
  simp only [List.set, List.getD_cons_succ, List.getD_cons_zero,
    Nat.mul_div_cancel s hK]

private theorem dx_chunk0_read (K r b s h : Nat) (x : Tensor)
    (hK : 0 < K) (hr : r < K) (hs : 0 < s) (hh : 0 < h)
    (hx : x.shape = [b * K, s, h]) (i : Nat) (hi : i < b * s * h) :
    valAt (chunkPrimDimN 0 K r x) i = valAt x (r * (b * s * h) + i) := by
  have hsH : s * h ≠ 0 := (Nat.mul_pos hs hh).ne'
  have hil : i < b * (s * h) := by simpa only [Nat.mul_assoc] using hi
  have hn : b * (s * h) ≠ 0 := by omega
  rw [valAt_of_lt _ _ (by
    rw [source_dx_chunk0_shape K r b s h x hK hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi)]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_zero, List.drop, List.foldl,
    Nat.one_mul, hK.ne', ite_false, Nat.mul_div_cancel b hK,
    Nat.mod_eq_of_lt hr, hsH, hn]
  rw [Nat.div_eq_of_lt hil, Nat.mod_eq_of_lt hil, Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    _ = r * (b * s * h) + ((s * h) * (i / (s * h)) + i % (s * h)) := by ring
    _ = _ := by rw [Nat.div_add_mod]

private theorem dx_chunk1_read (K r b s h : Nat) (x : Tensor)
    (hK : 0 < K) (hr : r < K) (hs : 0 < s) (hh : 0 < h)
    (hx : x.shape = [b, s * K, h]) (i : Nat) (hi : i < b * s * h) :
    valAt (chunkPrimDimN 1 K r x) i =
      valAt x ((i / (s * h) * (s * K) + r * s) * h + i % (s * h)) := by
  have hsH : s * h ≠ 0 := (Nat.mul_pos hs hh).ne'
  rw [valAt_of_lt _ _ (by
    rw [source_dx_chunk1_shape K r b s h x hK hx]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi)]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_succ, List.getD_cons_zero,
    List.drop, List.foldl, Nat.one_mul, hK.ne', ite_false,
    Nat.mul_div_cancel s hK, Nat.mod_eq_of_lt hr, hsH, hh.ne']
  congr 1
  calc
    _ = (i / (s * h) * (s * K) + r * s) * h +
        (h * ((i % (s * h)) / h) + (i % (s * h)) % h) := by ring
    _ = _ := by rw [Nat.div_add_mod]

private theorem dx_head (K : Nat) (ts : List Tensor) (sh : Shape)
    (hK : 0 < K) (hlen : ts.length = K) (hsh : ∀ t ∈ ts, t.shape = sh) :
    (ts.head?.map (fun t => t.shape)).getD [] = sh := by
  cases ts with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons t ts => exact hsh t List.mem_cons_self

/-- Arbitrary positive DP batch partition, preserving actual G and saved-X. -/
theorem bw_layernorm_dx_batch_chunk_dim0
    (D u B S H : Nat) (g x gamma beta : Tensor)
    (hD : 0 < D) (_hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hu : u < D)
    (_hg : g.shape = [B * D, S, H]) (hx : x.shape = [B * D, S, H])
    (_hgamma : gamma.shape = [H]) (_hbeta : beta.shape = [H]) :
    (bw_layernorm (chunkPrimDimN 0 D u g) (chunkPrimDimN 0 D u x) gamma beta).1 =
      chunkPrimDimN 0 D u (bw_layernorm g x gamma beta).1 := by
  have cx := source_dx_chunk0_shape D u B S H x hD hx
  have out := dx_shape g x gamma beta (B * D) S H hx
  have hl := dx_shape (chunkPrimDimN 0 D u g) _ gamma beta B S H cx
  have hr := source_dx_chunk0_shape D u B S H _ hD out
  apply Tensor.ext (hl.trans hr.symm)
  intro i hi
  have hib : i < B * S * H := by
    rw [hl] at hi
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  let row := i / H
  let j := i % H
  have hj : j < H := Nat.mod_lt _ hH
  have hrow : row < B * S := (Nat.div_lt_iff_lt_mul hH).mpr hib
  have he : row * H + j = i := by
    dsimp only [row, j]; rw [Nat.mul_comm]; exact Nat.div_add_mod i H
  have hfullrow : u * (B * S) + row < (B * D) * S := by
    have := Nat.mul_le_mul_right (B * S) (Nat.succ_le_iff.mpr hu)
    nlinarith
  rw [dx_chunk0_read D u B S H _ hD hu hS hH out i hib]
  have hidx : u * (B * S * H) + i = (u * (B * S) + row) * H + j := by
    nlinarith [he]
  rw [hidx, ← he]
  apply bw_layernorm_dx_row_congr _ _ _ _ gamma beta B S (B * D) S H
    row (u * (B * S) + row) j cx hx hH hrow hfullrow hj
  · intro k hk
    rw [dx_chunk0_read D u B S H g hD hu hS hH _hg _ (by nlinarith)]
    congr 1; ring
  · intro k hk
    rw [dx_chunk0_read D u B S H x hD hu hS hH hx _ (by nlinarith)]
    congr 1; ring

/-- Ordered TP input gathers imply the local dX chunk, using row locality.
The two input lists have exact length K; zip truncation is not an assumption. -/
theorem source_bw_layernorm_dx_sequence_local
    (K B S H : Nat) (g x gamma beta : Tensor) (gs xs : List Tensor)
    (hK : 0 < K) (_hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (_hg : g.shape = [B, S * K, H]) (hx : x.shape = [B, S * K, H])
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [B, S, H])
    (hxsh : ∀ x ∈ xs, x.shape = [B, S, H])
    (_hgamma : gamma.shape = [H]) (_hbeta : beta.shape = [H])
    (hgpre : g = allGatherPrimDimN 1 K 0 gs)
    (hxpre : x = allGatherPrimDimN 1 K 0 xs) (r : Fin K) :
    (bw_layernorm (gs.getD r.1 (zeroTensor [B, S, H]))
      (xs.getD r.1 (zeroTensor [B, S, H])) gamma beta).1 =
      chunkPrimDimN 1 K r.1 (bw_layernorm g x gamma beta).1 := by
  have hxr : r.1 < xs.length := by rw [hxlen]; exact r.2
  have hxl : (xs.getD r.1 (zeroTensor [B, S, H])).shape = [B, S, H] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr]
    exact hxsh xs[r.1] (List.getElem_mem hxr)
  have hl := dx_shape (gs.getD r.1 (zeroTensor [B, S, H])) _ gamma beta B S H hxl
  have hout := dx_shape g x gamma beta B (S * K) H hx
  have hr := source_dx_chunk1_shape K r.1 B S H _ hK hout
  apply Tensor.ext (hl.trans hr.symm)
  intro i hi
  have hib : i < B * S * H := by
    rw [hl] at hi
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  let q := i / (S * H)
  let z := i % (S * H)
  let p := z / H
  let j := z % H
  have hSH := Nat.mul_pos hS hH
  have hq : q < B := (Nat.div_lt_iff_lt_mul hSH).mpr (by
    simpa only [Nat.mul_assoc] using hib)
  have hz : z < S * H := Nat.mod_lt _ hSH
  have hp : p < S := (Nat.div_lt_iff_lt_mul hH).mpr hz
  have hj : j < H := Nat.mod_lt _ hH
  have hzEq : p * H + j = z := by
    dsimp only [p, j]; rw [Nat.mul_comm]; exact Nat.div_add_mod z H
  have hiEq : q * (S * H) + z = i := by
    dsimp only [q, z]; rw [Nat.mul_comm]; exact Nat.div_add_mod i (S * H)
  have hlocalidx : (q * S + p) * H + j = i := by nlinarith [hzEq, hiEq]
  have hglobalidx : (q * (S * K) + r.1 * S) * H + z =
      (q * (S * K) + (r.1 * S + p)) * H + j := by nlinarith [hzEq]
  have hlrow : q * S + p < B * S := by nlinarith
  have hrseq : r.1 * S + p < S * K := by
    have := Nat.mul_le_mul_right S (Nat.succ_le_iff.mpr r.2)
    nlinarith
  have hrrow : q * (S * K) + (r.1 * S + p) < B * (S * K) := by
    calc
      _ < q * (S * K) + (S * K) := Nat.add_lt_add_left hrseq _
      _ = (q + 1) * (S * K) := by ring
      _ ≤ B * (S * K) := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hq)
  rw [dx_chunk1_read K r.1 B S H _ hK r.2 hS hH hout i hib]
  change valAt _ i = valAt _ ((q * (S * K) + r.1 * S) * H + z)
  rw [hglobalidx, ← hlocalidx]
  apply bw_layernorm_dx_row_congr _ _ _ _ gamma beta B S B (S * K) H
    (q * S + p) (q * (S * K) + (r.1 * S + p)) j hxl hx hH hlrow hrrow hj
  · intro k hk
    rw [hgpre]
    exact (allGatherPrimDimN_dim1_3d_valAt gs K B S H q r.1 p k hK hS hH
      hq r.2 hp hk (dx_head K gs [B, S, H] hK hglen hgsh)).symm
  · intro k hk
    rw [hxpre]
    exact (allGatherPrimDimN_dim1_3d_valAt xs K B S H q r.1 p k hK hS hH
      hq r.2 hp hk (dx_head K xs [B, S, H] hK hxlen hxsh)).symm

/-- Source unit adapter. `hxpre` is an obligation of the forward saved-X
producer, not a theorem supplied by the completed cotangent chain. -/
theorem source_bw_layernorm_dx_unit_local
    (D T B S H u : Nat) (g x gamma beta : Tensor) (gs xs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hg : g.shape = [B * D, S * T, H])
    (hx : x.shape = [B * D, S * T, H])
    (hglen : gs.length = T) (hxlen : xs.length = T)
    (hgsh : ∀ g ∈ gs, g.shape = [B, S, H])
    (hxsh : ∀ x ∈ xs, x.shape = [B, S, H])
    (hgamma : gamma.shape = [H]) (hbeta : beta.shape = [H])
    (hgpre : chunkPrimDimN 0 D u g = allGatherPrimDimN 1 T 0 gs)
    (hxpre : chunkPrimDimN 0 D u x = allGatherPrimDimN 1 T 0 xs)
    (r : Fin T) :
    (bw_layernorm (gs.getD r.1 (zeroTensor [B, S, H]))
      (xs.getD r.1 (zeroTensor [B, S, H])) gamma beta).1 =
      chunkPrimDimN 1 T r.1 (chunkPrimDimN 0 D u (bw_layernorm g x gamma beta).1) := by
  rw [← bw_layernorm_dx_batch_chunk_dim0 D u B (S * T) H g x gamma beta
    hD hB (Nat.mul_pos hS hT) hH hu hg hx hgamma hbeta]
  exact source_bw_layernorm_dx_sequence_local T B S H _ _ gamma beta gs xs
    hT hB hS hH (source_dx_chunk0_shape D u B (S * T) H g hD hg)
    (source_dx_chunk0_shape D u B (S * T) H x hD hx)
    hglen hxlen hgsh hxsh hgamma hbeta hgpre hxpre r

#print axioms source_dx_chunk0_shape
#print axioms source_dx_chunk1_shape
#print axioms bw_layernorm_dx_batch_chunk_dim0
#print axioms source_bw_layernorm_dx_sequence_local
#print axioms source_bw_layernorm_dx_unit_local
end
end TrainVerify.Denote
