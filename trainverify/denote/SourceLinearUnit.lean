import denote.KRankLinearGather

/-!
# Source linear within one DP unit

The exact `fw_linear` semantics commute with a contiguous batch chunk.
Sequence-sharded inputs with a shared weight reconstruct on output dimension 1;
output-row-sharded weights with a shared unit input reconstruct on dimension 2.
Both source-output adapters derive all output shapes and reconstruction from
source input/weight facts and ordered individual producer equations.

Static candidate: compilation and kernel axiom auditing belong to the parent's
serial validation lane.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_linear_chunk_shape
    (D u B S H : Nat) (x : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, S, H]) :
    (chunkPrimDimN 0 D u x).shape = [B, S, H] := by
  rw [chunkPrimDimN_shape 0 D u x _ hx hD.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]

-- The existing 3D batch flat-read helpers are private. This bounded helper
-- is the same contiguous read used by SourceLayernormUnit, with no op changes.
private theorem source_linear_chunk0_flat
    (D u B S H : Nat) (x : Tensor)
    (hx : x.shape = [B * D, S, H]) (hD : 0 < D) (hu : u < D)
    (hS : 0 < S) (hH : 0 < H)
    (idx : Nat) (hi : idx < B * S * H) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * S * H) + idx) := by
  have hdiv : B * D / D = B := Nat.mul_div_cancel B hD
  have hshape := source_linear_chunk_shape D u B S H x hD hx
  have hbound : idx < prodShape (chunkPrimDimN 0 D u x).shape := by
    rw [hshape]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  have hstride : S * H ≠ 0 := (Nat.mul_pos hS hH).ne'
  have hlocal : idx < B * (S * H) := by
    simpa only [Nat.mul_assoc] using hi
  have hnonzero : B * (S * H) ≠ 0 := by omega
  rw [valAt_of_lt _ _ hbound]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_zero, List.drop, List.foldl,
    Nat.one_mul, hD.ne', ite_false, hdiv, Nat.mod_eq_of_lt hu,
    hstride, hnonzero]
  rw [Nat.div_eq_of_lt hlocal, Nat.mod_eq_of_lt hlocal,
    Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    (u * B + idx / (S * H)) * (S * H) + idx % (S * H) =
        u * (B * S * H) + ((S * H) * (idx / (S * H)) + idx % (S * H)) := by ring
    _ = u * (B * S * H) + idx := by rw [Nat.div_add_mod]

/-- A legal DP batch chunk commutes with rank-3 linear, keeping its shared
weight and its full contraction dimension unchanged. -/
theorem fw_linear_batch_chunk_dim0
    (D u B S I O : Nat) (fullx w : Tensor)
    (hD : 0 < D) (_hB : 0 < B) (hS : 0 < S) (hI : 0 < I) (hO : 0 < O)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, I])
    (hw : w.shape = [O, I]) :
    chunkPrimDimN 0 D u (fw_linear fullx w) =
      fw_linear (chunkPrimDimN 0 D u fullx) w := by
  have hlocal := source_linear_chunk_shape D u B S I fullx hD hfullx
  have hglobal := fw_linear_3d_shape (B * D) S I O fullx w hfullx hw
  have hleft := source_linear_chunk_shape D u B S O (fw_linear fullx w) hD hglobal
  have hright := fw_linear_3d_shape B S I O (chunkPrimDimN 0 D u fullx) w hlocal hw
  apply Tensor.ext (by rw [hleft, hright])
  intro idx hidx
  have hi : idx < B * S * O := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  let row := idx / O
  let col := idx % O
  have hcol : col < O := Nat.mod_lt _ hO
  have hrow : row < B * S := by
    dsimp only [row]
    rw [Nat.div_lt_iff_lt_mul hO]
    exact hi
  have hiEq : row * O + col = idx := by
    dsimp only [row, col]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod idx O
  have hfullrow : u * (B * S) + row < (B * D) * S := by
    calc
      u * (B * S) + row < u * (B * S) + B * S := Nat.add_lt_add_left hrow _
      _ = (u + 1) * (B * S) := by ring
      _ ≤ D * (B * S) := Nat.mul_le_mul_right (B * S) (Nat.succ_le_iff.mpr hu)
      _ = (B * D) * S := by ring
  have hglobalIdx : u * (B * S * O) + idx = (u * (B * S) + row) * O + col := by
    calc
      _ = u * (B * S * O) + (row * O + col) := by rw [hiEq]
      _ = _ := by ring
  rw [source_linear_chunk0_flat D u B S O (fw_linear fullx w)
    hglobal hD hu hS hO idx hi, hglobalIdx]
  conv_rhs => rw [← hiEq]
  rw [fw_linear_3d_valAt fullx w (B * D) S I O (u * (B * S) + row) col
    hO hfullrow hcol hfullx hw]
  rw [fw_linear_3d_valAt (chunkPrimDimN 0 D u fullx) w B S I O row col
    hO hrow hcol hlocal hw]
  apply Finset.sum_congr rfl
  intro j hj
  have hjI : j < I := Finset.mem_range.mp hj
  have hreadBound : row * I + j < B * S * I := by
    calc
      row * I + j < row * I + I := Nat.add_lt_add_left hjI _
      _ = (row + 1) * I := by ring
      _ ≤ (B * S) * I := Nat.mul_le_mul_right I (Nat.succ_le_iff.mpr hrow)
  rw [source_linear_chunk0_flat D u B S I fullx hfullx hD hu hS hI _ hreadBound]
  have hreadIdx : u * (B * S * I) + (row * I + j) =
      (u * (B * S) + row) * I + j := by ring
  rw [hreadIdx]

/-- Sequence-sharded source inputs and a replicated weight yield global and
local output shapes, and ordered sequence reconstruction inside one DP unit. -/
theorem source_linear_sequence_unit_output_reconstruct
    (D T B S I O u : Nat) (fullx w globalOut : Tensor)
    (xs localOuts : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hI : 0 < I) (hO : 0 < O)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, I])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, I])
    (hw : w.shape = [O, I])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs)
    (hglobal : globalOut = fw_linear fullx w)
    (hlocal : List.Forall₂ (fun x y => y = fw_linear x w) xs localOuts) :
    globalOut.shape = [B * D, S * T, O] ∧
      (∀ y ∈ localOuts, y.shape = [B, S, O]) ∧
      chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 1 T 0 localOuts := by
  have transport : ∀ {ins outs : List Tensor},
      List.Forall₂ (fun x y => y = fw_linear x w) ins outs →
      outs = ins.map (fun x => fw_linear x w) := by
    intro ins outs heq
    induction heq with
    | nil => rfl
    | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih
  have houts : localOuts = xs.map (fun x => fw_linear x w) := transport hlocal
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact fw_linear_3d_shape (B * D) (S * T) I O fullx w hfullx hw
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact fw_linear_3d_shape B S I O x w (hshapes x hx) hw
  · rw [hglobal, houts, fw_linear_batch_chunk_dim0 D u B (S * T) I O fullx w
      hD hB (Nat.mul_pos hS hT) hI hO hu hfullx hw, hpre]
    exact fw_linear_3d_allGatherPrimDimN_dim1_comm T B S I O xs w
      hT hB hS hI hO hlen hshapes hw

/-- Output-row-sharded source weights and the shared DP-unit input yield all
output shapes and ordered last-axis reconstruction. No full-weight or output
shape is assumed: the former follows from the source weight shards. -/
theorem source_linear_weight_unit_output_reconstruct
    (D T B S I O u : Nat) (fullx localx fullweight globalOut : Tensor)
    (ws localOuts : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hI : 0 < I) (hO : 0 < O)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, I])
    (hlen : ws.length = T) (hweights : ∀ w ∈ ws, w.shape = [O, I])
    (hpre : localx = chunkPrimDimN 0 D u fullx)
    (hweight : fullweight = allGatherPrimDimN 0 T 0 ws)
    (hglobal : globalOut = fw_linear fullx fullweight)
    (hlocal : List.Forall₂ (fun w y => y = fw_linear localx w) ws localOuts) :
    globalOut.shape = [B * D, S, O * T] ∧
      (∀ y ∈ localOuts, y.shape = [B, S, O]) ∧
      chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 2 T 0 localOuts := by
  have hlocalx : localx.shape = [B, S, I] := by
    rw [hpre]
    exact source_linear_chunk_shape D u B S I fullx hD hfullx
  have hhead : (ws.head?.map (fun t => t.shape)).getD [] = [O, I] := by
    cases hws : ws with
    | nil => simp only [hws, List.length_nil] at hlen; omega
    | cons w0 rest =>
      simp only [hws, List.head?, Option.map, Option.getD]
      exact hweights w0 (hws ▸ List.mem_cons_self ..)
  have hfullweight : fullweight.shape = [O * T, I] := by
    rw [hweight, allGatherPrimDimN_shape 0 T ws [O, I] hhead]
    simp only [List.set, List.getD_cons_zero]
  have transport : ∀ {ins outs : List Tensor},
      List.Forall₂ (fun w y => y = fw_linear localx w) ins outs →
      outs = ins.map (fw_linear localx) := by
    intro ins outs heq
    induction heq with
    | nil => rfl
    | cons hwy hrest ih => exact congrArg₂ List.cons hwy ih
  have houts : localOuts = ws.map (fw_linear localx) := transport hlocal
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact fw_linear_3d_shape (B * D) S I (O * T) fullx fullweight hfullx hfullweight
  · intro y hy
    rw [houts] at hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    exact fw_linear_3d_shape B S I O localx w hlocalx (hweights w hw)
  · rw [hglobal, houts, fw_linear_batch_chunk_dim0 D u B S I (O * T) fullx fullweight
      hD hB hS hI (Nat.mul_pos hO hT) hu hfullx hfullweight, ← hpre, hweight]
    exact fw_linear_3d_weight_allGatherPrimDimN_dim0_comm T B S I O localx ws
      hT hB hS hI hO hlen hlocalx hweights

#print axioms fw_linear_batch_chunk_dim0
#print axioms source_linear_sequence_unit_output_reconstruct
#print axioms source_linear_weight_unit_output_reconstruct

end
end TrainVerify.Denote
