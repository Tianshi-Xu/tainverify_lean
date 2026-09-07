import denote.KRankLayernormGather

namespace TrainVerify.Denote

noncomputable section

/-- Scalar `BW_sum` commutes with an arbitrary nonempty ordered dim-1 gather
of homogeneous positive rank-3 shards. The rank count is `xs.length`, with
no fixed-size or power-of-two restriction and no assumption on `g`.
Both sides broadcast `valAt g 0` to shape `[b, s * xs.length, h]`. -/
theorem bw_sum_allGatherPrimDimN_dim1_rank3
    (g : Tensor) (xs : List Tensor) (b s h : Nat)
    (hne : xs ≠ []) (hb : 0 < b) (hs : 0 < s) (hh : 0 < h)
    (hshapes : ∀ x ∈ xs, x.shape = [b, s, h]) :
    bw_sum g (allGatherPrimDimN 1 xs.length 0 xs) =
      allGatherPrimDimN 1 xs.length 0 (xs.map (bw_sum g)) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, h] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmaphead : ((xs.map (bw_sum g)).head?.map (fun t => t.shape)).getD [] =
      [b, s, h] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simp [bw_sum_shape, hshapes x (by simp)]
  have hgather_shape : (allGatherPrimDimN 1 xs.length 0 xs).shape =
      [b, s * xs.length, h] := by
    rw [allGatherPrimDimN_shape 1 xs.length _ [b, s, h] hhead]
    simp [List.set, List.getD]
  have hlhs_shape : (bw_sum g (allGatherPrimDimN 1 xs.length 0 xs)).shape =
      [b, s * xs.length, h] := by
    rw [bw_sum_shape, hgather_shape]
  have hrhs_shape : (allGatherPrimDimN 1 xs.length 0 (xs.map (bw_sum g))).shape =
      [b, s * xs.length, h] := by
    rw [allGatherPrimDimN_shape 1 xs.length _ [b, s, h] hmaphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx_bound : idx < b * (s * xs.length) * h := by
    rw [hlhs_shape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hidx
  conv_lhs =>
    rw [bw_sum_valAt_of_lt g _ idx (by
      rw [hgather_shape]
      simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hidx_bound)]
  -- Decompose the flattened global index into batch, rank, sequence, and feature.
  set j := idx % h with hjDef
  set row := idx / h with hrowDef
  have hj : j < h := by rw [hjDef]; exact Nat.mod_lt _ hh
  have hrow : row < b * (s * xs.length) := by
    rw [hrowDef, Nat.div_lt_iff_lt_mul hh]
    exact hidx_bound
  set q := row / (s * xs.length) with hqDef
  set u := row % (s * xs.length) with huDef
  have hSK : 0 < s * xs.length := Nat.mul_pos hs hK
  have hq : q < b := by
    rw [hqDef, Nat.div_lt_iff_lt_mul hSK]
    exact hrow
  have hu : u < s * xs.length := by rw [huDef]; exact Nat.mod_lt _ hSK
  set r := u / s with hrDef
  set p := u % s with hpDef
  have hr : r < xs.length := by
    rw [hrDef, Nat.div_lt_iff_lt_mul hs]
    simpa only [Nat.mul_comm] using hu
  have hp : p < s := by rw [hpDef]; exact Nat.mod_lt _ hs
  have hrowEq : row = q * (s * xs.length) + (r * s + p) := by
    have h1 := (Nat.div_add_mod row (s * xs.length)).symm
    have h2 := (Nat.div_add_mod u s).symm
    rw [← hqDef, ← huDef] at h1
    rw [← hrDef, ← hpDef] at h2
    calc
      row = s * xs.length * q + u := h1
      _ = q * (s * xs.length) + u := by ring
      _ = q * (s * xs.length) + (r * s + p) := by rw [h2]; ring
  have hidxEq : idx = (q * (s * xs.length) + (r * s + p)) * h + j := by
    have hi := (Nat.div_add_mod idx h).symm
    rw [← hrowDef, ← hjDef] at hi
    calc
      idx = h * row + j := hi
      _ = row * h + j := by ring
      _ = (q * (s * xs.length) + (r * s + p)) * h + j := by rw [hrowEq]
  rw [hidxEq]
  rw [allGatherPrimDimN_dim1_3d_valAt
    (xs.map (bw_sum g)) xs.length b s h q r p j hK hs hh hq hr hp hj hmaphead]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]
  -- The selected shard index is in bounds, so its backward sum has the same scalar value.
  have hlocal_row : q * s + p < b * s := by
    have hstep : q * s + p < (q + 1) * s := by
      rw [Nat.add_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right s (Nat.succ_le_of_lt hq))
  have hlocal_lt : (q * s + p) * h + j < b * s * h := by
    have hstep : (q * s + p) * h + j < (q * s + p + 1) * h := by
      calc
        _ < (q * s + p) * h + h := Nat.add_lt_add_left hj _
        _ = _ := by ring
    exact lt_of_lt_of_le hstep
      (Nat.mul_le_mul_right h (Nat.succ_le_of_lt hlocal_row))
  exact (bw_sum_valAt_of_lt g xs[r] ((q * s + p) * h + j) (by
    rw [hshapes xs[r] (List.getElem_mem hr)]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hlocal_lt)).symm

end

end TrainVerify.Denote
