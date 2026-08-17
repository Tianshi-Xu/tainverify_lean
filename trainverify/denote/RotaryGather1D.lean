import denote.Denote
import denote.InnerChunkCEShard

namespace TrainVerify.Denote

private theorem rotary_apply_pos_congr_1d
    (cs p p' x : Tensor) (L nh d : Nat)
    (hx : x.shape = [L, nh, d])
    (hpos : ∀ l, l < L → valAt p l = valAt p' l) :
    fw_rotary_apply cs p x nh = fw_rotary_apply cs p' x nh := by
  rw [fw_rotary_apply_reduce_c2a cs p x L nh d hx,
      fw_rotary_apply_reduce_c2a cs p' x L nh d hx]
  apply Tensor.ext
  · simp [Tensor.mkShape]
  · intro outIdx houtIdx
    have hprod : prodShape [L, nh, d] = L * nh * d := by simp [prodShape]
    have hbound : outIdx < L * nh * d := by
      have h := houtIdx
      simp only [Tensor.mkShape] at h
      rw [hprod] at h
      exact h
    have hd2 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hbound)
    have hnh2 : 0 < nh := Nat.pos_of_ne_zero (by rintro rfl; simp at hbound)
    have hl : outIdx / d / nh < L := by
      rw [Nat.div_lt_iff_lt_mul hnh2, Nat.div_lt_iff_lt_mul hd2]
      calc
        outIdx < L * nh * d := hbound
        _ = L * (nh * d) := by ring
        _ = L * nh * d := by ring
    rw [valAt_of_lt _ _ (by
      rw [show (Tensor.mkShape [L, nh, d] _).shape = [L, nh, d] from rfl, hprod]
      exact hbound)]
    rw [valAt_of_lt _ _ (by
      rw [show (Tensor.mkShape [L, nh, d] _).shape = [L, nh, d] from rfl, hprod]
      exact hbound)]
    simp only [Tensor.mkShape]
    rw [hpos _ hl]

/-- RoPE commutes with a two-rank dim-0 gather when positions are represented
as one-dimensional local shards. -/
theorem fw_rotary_apply_allGather0_commute_2_1d_shards
    (cs pa pb a b : Tensor) (L nh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hd : 0 < d)
    (hpa : pa.shape = [L]) (hpb : pb.shape = [L])
    (ha : a.shape = [L, nh, d]) (hb : b.shape = [L, nh, d]) :
    fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pa, pb])
        (allGatherPrimDimN 0 2 0 [a, b]) nh =
      allGatherPrimDimN 0 2 0
        [fw_rotary_apply cs pa a nh, fw_rotary_apply cs pb b nh] := by
  set pa2 := Tensor.mkShape [L, 1] (fun idx => valAt pa idx.1) with hpa2_def
  set pb2 := Tensor.mkShape [L, 1] (fun idx => valAt pb idx.1) with hpb2_def
  have hpa2_shape : pa2.shape = [L, 1] := rfl
  have hpb2_shape : pb2.shape = [L, 1] := rfl
  have hpa_val : ∀ i, i < L → valAt pa2 i = valAt pa i := by
    intro i hi
    have h : i < prodShape ([L, 1] : Shape) := by simp [prodShape]; omega
    show valAt (Tensor.mkShape [L, 1] (fun idx => valAt pa idx.1)) i = _
    rw [valAt_of_lt _ i h]
    rfl
  have hpb_val : ∀ i, i < L → valAt pb2 i = valAt pb i := by
    intro i hi
    have h : i < prodShape ([L, 1] : Shape) := by simp [prodShape]; omega
    show valAt (Tensor.mkShape [L, 1] (fun idx => valAt pb idx.1)) i = _
    rw [valAt_of_lt _ i h]
    rfl
  have hrank0 : fw_rotary_apply cs pa2 a nh = fw_rotary_apply cs pa a nh :=
    rotary_apply_pos_congr_1d cs pa2 pa a L nh d ha hpa_val
  have hrank1 : fw_rotary_apply cs pb2 b nh = fw_rotary_apply cs pb b nh :=
    rotary_apply_pos_congr_1d cs pb2 pb b L nh d hb hpb_val
  have hab_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [2 * L, nh, d] := by
    rw [allGatherPrimDimN_shape 0 2 [a, b] [L, nh, d] (by simp [ha])]
    simp only [List.set, List.getD_cons_zero]
    rw [Nat.mul_comm L 2]
  have hgather_pos : ∀ l, l < 2 * L →
      valAt (allGatherPrimDimN 0 2 0 [pa, pb]) l =
        valAt (allGatherPrimDimN 0 2 0 [pa2, pb2]) l := by
    intro l hl
    obtain ⟨r, i, hr, hi, rfl⟩ : ∃ r i, r < 2 ∧ i < L ∧ l = r * L + i := by
      refine ⟨l / L, l % L, ?_, Nat.mod_lt _ hL, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hL]
        omega
      · rw [Nat.mul_comm]
        exact (Nat.div_add_mod l L).symm
    have hleft := allGatherPrimDimN0_valAt_1d 2 L [pa, pb] (by omega) hL
      (by simp [hpa])
      (by intro rr hrr; rcases (by omega : rr = 0 ∨ rr = 1) with h | h <;>
        subst h <;> simp [List.getD, hpa, hpb]) r hr i hi
    have hright := allGatherPrimDimN0_valAt 2 L 1 [pa2, pb2] (by omega) hL (by omega)
      (by simp [hpa2_shape])
      (by intro rr hrr; rcases (by omega : rr = 0 ∨ rr = 1) with h | h <;>
        subst h <;> simp [List.getD, hpa2_shape, hpb2_shape]) r hr i hi 0 (by omega)
    simp only [Nat.mul_one, Nat.add_zero] at hright
    rw [hleft, hright]
    rcases (by omega : r = 0 ∨ r = 1) with h | h <;> subst h
    · simp only [List.getD_cons_zero]
      exact (hpa_val i hi).symm
    · simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      exact (hpb_val i hi).symm
  have hleft :
      fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pa, pb])
          (allGatherPrimDimN 0 2 0 [a, b]) nh =
        fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pa2, pb2])
          (allGatherPrimDimN 0 2 0 [a, b]) nh :=
    rotary_apply_pos_congr_1d cs _ _ _ (2 * L) nh d hab_shape hgather_pos
  rw [hleft,
      fw_rotary_apply_allGather0_commute_2 a b pa2 pb2 cs L nh d
        hL hnh hd ha hb hpa2_shape hpb2_shape,
      hrank0, hrank1]

/-- Two-output RoPE gather commutation with one-dimensional position shards. -/
theorem fw_rotary_embedding_allGather0_commute_2_1d_shards
    (cs pa pb qa qb ka kb : Tensor) (L qh kh d : Nat)
    (hL : 0 < L) (hqh : 0 < qh) (hkh : 0 < kh) (hd : 0 < d)
    (hpa : pa.shape = [L]) (hpb : pb.shape = [L])
    (hqa : qa.shape = [L, qh, d]) (hqb : qb.shape = [L, qh, d])
    (hka : ka.shape = [L, kh, d]) (hkb : kb.shape = [L, kh, d]) :
    fw_rotary_embedding cs (allGatherPrimDimN 0 2 0 [pa, pb])
        (allGatherPrimDimN 0 2 0 [qa, qb])
        (allGatherPrimDimN 0 2 0 [ka, kb]) qh kh =
      (allGatherPrimDimN 0 2 0
          [fw_rotary_apply cs pa qa qh, fw_rotary_apply cs pb qb qh],
       allGatherPrimDimN 0 2 0
          [fw_rotary_apply cs pa ka kh, fw_rotary_apply cs pb kb kh]) := by
  unfold fw_rotary_embedding
  rw [fw_rotary_apply_allGather0_commute_2_1d_shards cs pa pb qa qb L qh d
        hL hqh hd hpa hpb hqa hqb,
      fw_rotary_apply_allGather0_commute_2_1d_shards cs pa pb ka kb L kh d
        hL hkh hd hpa hpb hka hkb]

end TrainVerify.Denote
