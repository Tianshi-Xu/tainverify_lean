import denote.KRankBWLinearDxSequence
import denote.KRankBWLinearDxRow
import denote.SourceLinearUnit

/-!
# Source backward-linear dX within an arbitrary DP unit

Torch weights have layout `[O,I]`: TP partitions their output rows (dimension 0)
and the gradient's output channels (dimension 2). Saved activations contribute
only their shapes to dX. Neither global/local nor inter-rank activation values
are identified here. This module deliberately makes no assertion about dW.

Exact-source compilation and kernel auditing belong to the parent lane.
-/

namespace TrainVerify.Denote
noncomputable section

/-- Replacing saved activation values while retaining the exact rank-3 shape
leaves dX unchanged. Gradient and weight values are completely arbitrary. -/
theorem source_bw_linear_dx_shape_only
    (g x x' w : Tensor) (B S O I : Nat)
    (hS : 0 < S) (hO : 0 < O) (hI : 0 < I)
    (hg : g.shape = [B, S, O])
    (hx : x.shape = [B, S, I]) (hx' : x'.shape = [B, S, I])
    (hw : w.shape = [O, I]) :
    (bw_linear g x w).1 = (bw_linear g x' w).1 := by
  exact (bw_linear_fst_eq_fw_linear_transpose_rank3 g x w B S O I
    hS hO hI hg hx hw).trans
    (bw_linear_fst_eq_fw_linear_transpose_rank3 g x' w B S O I
      hS hO hI hg hx' hw).symm

-- List bookkeeping only: preserve every rank and replace just its saved X.
private theorem source_dx_zip_saved_values
    (B S O I : Nat) (x : Tensor)
    (hS : 0 < S) (hO : 0 < O) (hI : 0 < I)
    (hx : x.shape = [B, S, I])
    (gs xs ws : List Tensor)
    (hxlen : xs.length = gs.length) (hwlen : ws.length = gs.length)
    (hgs : ∀ g ∈ gs, g.shape = [B, S, O])
    (hxs : ∀ a ∈ xs, a.shape = [B, S, I])
    (hws : ∀ w ∈ ws, w.shape = [O, I]) :
    List.zipWith (fun g w => (bw_linear g x w).1) gs ws =
      List.zipWith (fun (ga : Tensor × Tensor) (w : Tensor) => (bw_linear ga.1 ga.2 w).1)
        (List.zipWith Prod.mk gs xs) ws := by
  induction gs generalizing xs ws with
  | nil => rfl
  | cons g rest ih =>
    cases xs with
    | nil => simp only [List.length_nil, List.length_cons] at hxlen; omega
    | cons a tail =>
      cases ws with
      | nil => simp only [List.length_nil, List.length_cons] at hwlen; omega
      | cons w more =>
        simp only [List.zipWith]
        apply congrArg₂ List.cons
        · exact source_bw_linear_dx_shape_only g x a w B S O I hS hO hI
            (hgs g (List.mem_cons_self ..)) hx
            (hxs a (List.mem_cons_self ..)) (hws w (List.mem_cons_self ..))
        · exact ih tail more
            (Nat.succ.inj hxlen) (Nat.succ.inj hwlen)
            (fun z hz => hgs z (List.mem_cons_of_mem _ hz))
            (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
            (fun z hz => hws z (List.mem_cons_of_mem _ hz))

/-- Arbitrary positive DP/TP sizes, arbitrary legal DP unit, and independent
saved-X values. The only value premises reconstruct the *inputs* G and W.
All three ordered lists have exactly T entries, so neither zip can truncate.
The common local activation used internally is a shape witness, not a premise.
-/
theorem source_bw_linear_dx_batch_tp_unit
    (D T B S O I u : Nat) (G X W : Tensor) (gs xs ws : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hO : 0 < O) (hI : 0 < I) (hu : u < D)
    (hG : G.shape = [B * D, S, O * T])
    (hX : X.shape = [B * D, S, I]) (hW : W.shape = [O * T, I])
    (hglen : gs.length = T) (hxlen : xs.length = T) (hwlen : ws.length = T)
    (hgs : ∀ g ∈ gs, g.shape = [B, S, O])
    (hxs : ∀ x ∈ xs, x.shape = [B, S, I])
    (hws : ∀ w ∈ ws, w.shape = [O, I])
    (hgradient : chunkPrimDimN 0 D u G = allGatherPrimDimN 2 T 0 gs)
    (hweight : W = allGatherPrimDimN 0 T 0 ws) :
    chunkPrimDimN 0 D u (bw_linear G X W).1 =
      tensorSum (List.zipWith (fun (ga : Tensor × Tensor) (w : Tensor) => (bw_linear ga.1 ga.2 w).1)
        (List.zipWith Prod.mk gs xs) ws) := by
  let x := zeroTensor [B, S, I]
  have hx : x.shape = [B, S, I] := rfl
  have hlocalG : (chunkPrimDimN 0 D u G).shape = [B, S, O * T] := by
    rw [chunkPrimDimN_shape 0 D u G _ hG hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hWt : (transpose2d W).shape = [I, O * T] := by
    simp only [transpose2d, hW, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Tensor.mkShape]
  rw [bw_linear_fst_eq_fw_linear_transpose_rank3 G X W (B * D) S (O * T) I
    hS (Nat.mul_pos hO hT) hI hG hX hW]
  rw [fw_linear_batch_chunk_dim0 D u B S (O * T) I G (transpose2d W)
    hD hB hS (Nat.mul_pos hO hT) hI hu hG hWt]
  rw [← bw_linear_fst_eq_fw_linear_transpose_rank3
    (chunkPrimDimN 0 D u G) x W B S (O * T) I
    hS (Nat.mul_pos hO hT) hI hlocalG hx hW]
  rw [hgradient, hweight]
  rw [bw_linear_dx_row_reduction_rank3 T B S O I gs ws x
    hT hB hS hO hI hglen hwlen hgs hws hx]
  exact congrArg tensorSum (source_dx_zip_saved_values B S O I x hS hO hI hx
    gs xs ws (hxlen.trans hglen.symm) (hwlen.trans hglen.symm) hgs hxs hws)

/-- The local dX list contains every TP rank, in its original order. -/
theorem source_bw_linear_dx_local_list_length
    (T : Nat) (gs xs ws : List Tensor)
    (hglen : gs.length = T) (hxlen : xs.length = T) (hwlen : ws.length = T) :
    (List.zipWith (fun (ga : Tensor × Tensor) (w : Tensor) => (bw_linear ga.1 ga.2 w).1)
      (List.zipWith Prod.mk gs xs) ws).length = T := by
  simp only [List.length_zipWith, hglen, hxlen, hwlen, Nat.min_self]

#print axioms source_bw_linear_dx_shape_only
#print axioms source_bw_linear_dx_batch_tp_unit
#print axioms source_bw_linear_dx_local_list_length

end
end TrainVerify.Denote
