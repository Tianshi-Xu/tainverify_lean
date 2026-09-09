import denote.ChunkGatherDim0

/-!
# Source initial embedding: contiguous DP batch slices

UNCOMPILED CANDIDATE: parent serial builder must compile and audit this module.
This is a value theorem for the existing `fw_embedding`, not a source evaluator
or a producer/store theorem. Apply it to one DP unit with the SAME weight on
both sides; hidden-axis weight reconstruction is a separate bridge.

No label-domain premise is needed: both sides preserve the exact `scalarToNat`
conversion and the same `valAt weight` lookup, including its zero default.
Source applicability is ordinary embedding (start = 0, stop = vocab), not an
arbitrary offset/vocab-sharded source call.
-/
namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

-- The existing dim0 coordinate lemma covers matrices, not embedding's 3D output.
private theorem source_embedding_chunk0_flat
    (K unit B S H : Nat) (x : Tensor)
    (hx : x.shape = [B * K, S, H]) (hK : 0 < K) (hu : unit < K)
    (hs : 0 < S) (hh : 0 < H)
    (idx : Nat) (hi : idx < B * S * H) :
    valAt (chunkPrimDimN 0 K unit x) idx =
      valAt x (unit * (B * S * H) + idx) := by
  have hdiv : B * K / K = B := Nat.mul_div_cancel B hK
  have hshape : (chunkPrimDimN 0 K unit x).shape = [B, S, H] := by
    rw [chunkPrimDimN_shape 0 K unit x _ hx hK.ne']
    simp only [List.set, List.getD_cons_zero, hdiv]
  have hbound : idx < prodShape (chunkPrimDimN 0 K unit x).shape := by
    rw [hshape]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  have hstride : S * H ≠ 0 := (Nat.mul_pos hs hh).ne'
  have hlocal : idx < B * (S * H) := by
    simpa only [Nat.mul_assoc] using hi
  have hnonzero : B * (S * H) ≠ 0 := by omega
  rw [valAt_of_lt _ _ hbound]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_zero, List.drop, List.foldl,
    Nat.one_mul, hK.ne', ite_false, hdiv, Nat.mod_eq_of_lt hu,
    hstride, hnonzero]
  rw [Nat.div_eq_of_lt hlocal, Nat.mod_eq_of_lt hlocal,
    Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    (unit * B + idx / (S * H)) * (S * H) + idx % (S * H) =
        unit * (B * S * H) + ((S * H) * (idx / (S * H)) + idx % (S * H)) := by ring
    _ = unit * (B * S * H) + idx := by rw [Nat.div_add_mod]

/-- A contiguous batch slice of IDs induces exactly the same batch slice of
embedding values. `piece` need not carry a separate shape premise: its shape
follows from the input chunk equality. `B` and `V` may even be zero. -/
theorem fw_embedding_batch_chunk_dim0
    (K unit B S V H : Nat) (ids piece weight : Tensor)
    (hK : 0 < K) (hu : unit < K) (hs : 0 < S) (hh : 0 < H)
    (hids : ids.shape = [B * K, S]) (hw : weight.shape = [V, H])
    (hpiece : piece = chunkPrimDimN 0 K unit ids) :
    fw_embedding piece weight = chunkPrimDimN 0 K unit (fw_embedding ids weight) := by
  have hdiv : B * K / K = B := Nat.mul_div_cancel B hK
  have hpieceShape : piece.shape = [B, S] := by
    rw [hpiece, chunkPrimDimN_shape 0 K unit ids _ hids hK.ne']
    simp only [List.set, List.getD_cons_zero, hdiv]
  have hlast : lastD weight.shape = H := by rw [hw]; rfl
  have hfullShape : (fw_embedding ids weight).shape = [B * K, S, H] := by
    rw [fw_embedding_shape, hids, hlast]
    rfl
  have hlocalShape : (fw_embedding piece weight).shape = [B, S, H] := by
    rw [fw_embedding_shape, hpieceShape, hlast]
    rfl
  have hchunkShape :
      (chunkPrimDimN 0 K unit (fw_embedding ids weight)).shape = [B, S, H] := by
    rw [chunkPrimDimN_shape 0 K unit _ _ hfullShape hK.ne']
    simp only [List.set, List.getD_cons_zero, hdiv]
  apply Tensor.ext (by rw [hlocalShape, hchunkShape])
  intro idx hidx
  have hi : idx < B * S * H := by
    rw [hlocalShape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hp : idx / H < B * S := by
    rw [Nat.div_lt_iff_lt_mul hh]
    exact hi
  have hrow : (idx / H) / S < B := by
    rw [Nat.div_lt_iff_lt_mul hs]
    exact hp
  have hidRead : valAt piece (idx / H) =
      valAt ids (unit * B * S + idx / H) := by
    have h := chunkPrimDimN0_valAt K unit (B * K) S ids hids hK hs hu
      ((idx / H) / S) (by rw [hdiv]; exact hrow)
      ((idx / H) % S) (Nat.mod_lt _ hs)
    rw [hdiv] at h
    have hflat : ((idx / H) / S) * S + (idx / H) % S = idx / H := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod (idx / H) S
    have hglobal : (unit * B + (idx / H) / S) * S + (idx / H) % S =
        unit * B * S + idx / H := by
      rw [Nat.add_mul, Nat.add_assoc, hflat]
    rw [hflat, hglobal] at h
    rw [hpiece]
    exact h
  have hlocalBound : idx < prodShape (piece.shape ++ [lastD weight.shape]) := by
    rw [hpieceShape, hlast]
    simpa only [List.cons_append, List.nil_append, prodShape, List.foldl,
      Nat.one_mul] using hi
  have hfullIdx : unit * (B * S * H) + idx < B * K * S * H := by
    calc
      unit * (B * S * H) + idx < unit * (B * S * H) + B * S * H :=
        Nat.add_lt_add_left hi _
      _ = (unit + 1) * (B * S * H) := by ring
      _ ≤ K * (B * S * H) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hu)
      _ = B * K * S * H := by ring
  have hfullBound : unit * (B * S * H) + idx <
      prodShape (ids.shape ++ [lastD weight.shape]) := by
    rw [hids, hlast]
    simpa only [List.cons_append, List.nil_append, prodShape, List.foldl,
      Nat.one_mul] using hfullIdx
  have hoffset : unit * (B * S * H) + idx = idx + H * (unit * B * S) := by ring
  have hquot : (unit * (B * S * H) + idx) / H = unit * B * S + idx / H := by
    rw [hoffset, Nat.add_mul_div_left _ _ hh, Nat.add_comm]
  have hrem : (unit * (B * S * H) + idx) % H = idx % H := by
    rw [hoffset, Nat.add_mul_mod_self_left]
  rw [source_embedding_chunk0_flat K unit B S H (fw_embedding ids weight)
    hfullShape hK hu hs hh idx hi]
  rw [fw_embedding_valAt, dif_pos hlocalBound, hlast,
    fw_embedding_valAt, dif_pos hfullBound, hlast, hquot, hrem, hidRead]

end
end TrainVerify.Denote
