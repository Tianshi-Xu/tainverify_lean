/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel
import denote.DenoteMoE

/-!
# Faithful zigzag attention preserves `Zigzag2Rel`

This module contains the small dim-0 CP2 chunk/gather inverse needed to expose the
ordinary full attention result as the hidden sources of the faithful collective.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-- Gathering the two dim-0 chunks of a three-dimensional CP2 tensor recovers it. -/
theorem allGather_chunk_cp2_dim0_3d
    (x : Tensor) (lDim qHeads vDim : Nat)
    (hx : x.shape = [2 * lDim, qHeads, vDim])
    (hl : 0 < lDim) (hh : 0 < qHeads) (hv : 0 < vDim) :
    allGatherPrimDimN 0 2 0
      [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x] = x := by
  have hc : ∀ r, (chunkPrimDimN 0 2 r x).shape = [lDim, qHeads, vDim] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r x [2 * lDim, qHeads, vDim] hx (by omega)]
    simp
  have hhead :
      (([chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [lDim, qHeads, vDim] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact hc 0
  have hg : (allGatherPrimDimN 0 2 0
      [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x]).shape =
      [2 * lDim, qHeads, vDim] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, qHeads, vDim] hhead]
    simp [List.set, List.getD, Nat.mul_comm]
  apply Tensor.ext
  · rw [hg, hx]
  · intro idx hidx
    rw [hg] at hidx
    have hbound : idx < (2 * lDim) * qHeads * vDim := by
      simpa [prodShape] using hidx
    let row := idx / (qHeads * vDim)
    let rem := idx % (qHeads * vDim)
    let j := rem / vDim
    let k := rem % vDim
    let r := row / lDim
    let i := row % lDim
    have hp : 0 < qHeads * vDim := Nat.mul_pos hh hv
    have hrow : row < 2 * lDim := by
      dsimp [row]
      exact Nat.div_lt_iff_lt_mul hp |>.mpr (by simpa [Nat.mul_assoc] using hbound)
    have hr : r < 2 := by
      dsimp [r]
      exact Nat.div_lt_iff_lt_mul hl |>.mpr (by simpa [Nat.mul_comm] using hrow)
    have hi : i < lDim := Nat.mod_lt _ hl
    have hj : j < qHeads := by
      dsimp [j, rem]
      exact Nat.div_lt_iff_lt_mul hv |>.mpr (Nat.mod_lt _ hp)
    have hk : k < vDim := by
      dsimp [k, rem]
      exact Nat.mod_lt _ hv
    have hidxeq : idx = ((r * lDim + i) * qHeads + j) * vDim + k := by
      have h1 : idx = row * (qHeads * vDim) + rem := by
        dsimp [row, rem]
        simpa [Nat.mul_comm] using (Nat.div_add_mod idx (qHeads * vDim)).symm
      have h2 : row = r * lDim + i := by
        dsimp [r, i]
        simpa [Nat.mul_comm] using (Nat.div_add_mod row lDim).symm
      have h3 : rem = j * vDim + k := by
        dsimp [j, k]
        simpa [Nat.mul_comm] using (Nat.div_add_mod rem vDim).symm
      rw [h1, h2, h3]
      ring
    have hshapes : ∀ r' (_ : r' < 2),
        ([chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x].getD r'
          (zeroTensor [lDim, qHeads, vDim])).shape = [lDim, qHeads, vDim] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with rfl | rfl <;> simp only [List.getD_cons_zero,
        List.getD_cons_succ] <;> exact hc _
    rw [hidxeq]
    rw [allGatherPrimDimN0_valAt_3D 2 lDim qHeads vDim _ (by omega) hl hh hv
      hhead hshapes r hr i hi j hj k hk]
    have hget :
        [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x].getD r
            (zeroTensor [lDim, qHeads, vDim]) = chunkPrimDimN 0 2 r x := by
      interval_cases r <;> rfl
    rw [hget]
    have hlocal : (i * qHeads + j) * vDim + k <
        prodShape (chunkPrimDimN 0 2 r x).shape := by
      rw [hc r]
      simp only [prodShape, List.foldl_cons, List.foldl_nil]
      rw [Nat.one_mul]
      calc
        (i * qHeads + j) * vDim + k
            = i * (qHeads * vDim) + (j * vDim + k) := by ring
        _ < i * (qHeads * vDim) + qHeads * vDim := by nlinarith
        _ = (i + 1) * (qHeads * vDim) := by ring
        _ ≤ lDim * qHeads * vDim := by
          calc
            (i + 1) * (qHeads * vDim) ≤ lDim * (qHeads * vDim) :=
              Nat.mul_le_mul_right _ (by omega)
            _ = lDim * qHeads * vDim := by ring
    rw [valAt_of_lt _ _ hlocal]
    unfold chunkPrimDimN
    have hhalf : 2 * lDim / 2 = lDim := by omega
    have hpne : qHeads * vDim ≠ 0 := Nat.ne_of_gt hp
    have hlocalne : lDim * (qHeads * vDim) ≠ 0 := by positivity
    simp only [hx, Tensor.mkShape, List.getD_cons_zero, List.drop,
      List.foldl_cons, List.foldl_nil, Nat.one_mul, hhalf,
      show (2 : Nat) ≠ 0 by omega, if_false, hpne, hlocalne,
      Nat.zero_mul, Nat.zero_add]
    have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
    have hsmall : (i * qHeads + j) * vDim + k < lDim * (qHeads * vDim) := by
      calc
        (i * qHeads + j) * vDim + k
            = i * (qHeads * vDim) + (j * vDim + k) := by ring
        _ < i * (qHeads * vDim) + qHeads * vDim := by nlinarith
        _ = (i + 1) * (qHeads * vDim) := by ring
        _ ≤ lDim * (qHeads * vDim) := Nat.mul_le_mul_right _ (by omega)
    have hrem : ((i * qHeads + j) * vDim + k) %
        (lDim * (qHeads * vDim)) = (i * qHeads + j) * vDim + k :=
      Nat.mod_eq_of_lt hsmall
    have hdiv : ((i * qHeads + j) * vDim + k) /
        (lDim * (qHeads * vDim)) = 0 := Nat.div_eq_of_lt hsmall
    have hjk : j * vDim + k < qHeads * vDim := by nlinarith
    have hdivp : ((i * qHeads + j) * vDim + k) / (qHeads * vDim) = i := by
      rw [show (i * qHeads + j) * vDim + k =
        (j * vDim + k) + (qHeads * vDim) * i by ring,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hjk, Nat.zero_add]
    have hmodp : ((i * qHeads + j) * vDim + k) % (qHeads * vDim) =
        j * vDim + k := by
      rw [show (i * qHeads + j) * vDim + k =
        (j * vDim + k) + (qHeads * vDim) * i by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjk]
    rw [hrmod, hdiv, hrem, hdivp, hmodp]
    congr 1
    ring

/-- Replacing CP2 source tensors by tensors with the same local token dimension
preserves cumulative-sequence well-formedness. -/
theorem ZigzagCuWF.transport_cp2_3d
    (cu : List Nat) (a b y0 y1 : Tensor) (lDim h d : Nat)
    (hwf : ZigzagCuWF cu [a, b] 2)
    (ha : a.shape.getD 0 0 = lDim)
    (hy0 : y0.shape = [lDim, h, d]) (hy1 : y1.shape = [lDim, h, d]) :
    ZigzagCuWF cu [y0, y1] 2 := by
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> simp [hy0, hy1]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero]
      rw [hy1, hy0]
  · simpa only [List.getD_cons_zero, hy0, ha] using hwf.local_tokens

namespace Zigzag2Rel

-- Faithful CP2 zigzag attention preserves the source-witness relation. K/V and
-- all attention parameters are arbitrary replicated inputs.
set_option maxHeartbeats 1600000 in
-- The extensional chunk/gather and collective normalization needs extra budget.
theorem attn_zigzag
    (fullQ q0 q1 cuShuffle k v cuAttn cuKV : Tensor)
    (lDim qHeads kvHeads qDim vDim : Nat) (causal : Bool) (window : Nat)
    (hrel : Zigzag2Rel fullQ q0 q1 cuShuffle
      [2 * lDim, qHeads, qDim] [lDim, qHeads, qDim])
    (hcu : cuAttn = cuShuffle)
    (hdecoded : decodeCuSeqlens cuShuffle = [0, 2 * lDim])
    (hl : 0 < lDim) (heven : lDim % 2 = 0)
    (hh : 0 < qHeads) (_hd : 0 < qDim) (hv : 0 < vDim) :
    Zigzag2Rel
      (fw_attn_varlen fullQ k v cuAttn cuKV
        qHeads kvHeads qDim vDim causal window)
      (fw_attn_zigzag_collective [q0, q1] k v cuAttn cuKV
        qHeads kvHeads qDim vDim causal window 2 0)
      (fw_attn_zigzag_collective [q0, q1] k v cuAttn cuKV
        qHeads kvHeads qDim vDim causal window 2 1)
      cuAttn [2 * lDim, qHeads, vDim] [lDim, qHeads, vDim] := by
  obtain ⟨source0, source1, hs⟩ := hrel
  have hs0 : source0.shape = [lDim, qHeads, qDim] := hs.source0_shape
  have hs1 : source1.shape = [lDim, qHeads, qDim] := hs.source1_shape
  have hu0 : fw_maybe_unshuffle_collective [q0, q1]
      (decodeCuSeqlens cuShuffle) 2 0 = source0 := by
    rw [hs.rank0_value, hs.rank1_value, hdecoded]
    simpa only [List.getD_cons_zero] using
      (fw_maybe_unshuffle_shuffle_collective_cp2_single
        source0 source1 lDim 0 [qHeads, qDim] hl heven (by omega) hs0 hs1)
  have hu1 : fw_maybe_unshuffle_collective [q0, q1]
      (decodeCuSeqlens cuShuffle) 2 1 = source1 := by
    rw [hs.rank0_value, hs.rank1_value, hdecoded]
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      (fw_maybe_unshuffle_shuffle_collective_cp2_single
        source0 source1 lDim 1 [qHeads, qDim] hl heven (by omega) hs0 hs1)
  let fullOut := fw_attn_varlen fullQ k v cuAttn cuKV
    qHeads kvHeads qDim vDim causal window
  let out0 := chunkPrimDimN 0 2 0 fullOut
  let out1 := chunkPrimDimN 0 2 1 fullOut
  have hfullOut : fullOut.shape = [2 * lDim, qHeads, vDim] := by
    apply fw_attn_varlen_shape
    rw [hs.full_shape]
    rfl
  have ho0 : out0.shape = [lDim, qHeads, vDim] := by
    dsimp [out0]
    rw [chunkPrimDimN_shape 0 2 0 fullOut _ hfullOut (by omega)]
    simp
  have ho1 : out1.shape = [lDim, qHeads, vDim] := by
    dsimp [out1]
    rw [chunkPrimDimN_shape 0 2 1 fullOut _ hfullOut (by omega)]
    simp
  refine of_sources out0 out1 ?_ ?_ ?_ hfullOut ho0 ho1 ?_
  · exact (allGather_chunk_cp2_dim0_3d fullOut lDim qHeads vDim
      hfullOut hl hh hv).symm
  · have hrange : List.range 2 = [0, 1] := by decide
    have hu0' : fw_maybe_unshuffle_collective [q0, q1] [0, 2 * lDim] 2 0 = source0 := by
      rwa [hdecoded] at hu0
    have hu1' : fw_maybe_unshuffle_collective [q0, q1] [0, 2 * lDim] 2 1 = source1 := by
      rwa [hdecoded] at hu1
    simp only [fw_attn_zigzag_collective, show (2 : Nat) ≠ 1 by omega, if_false,
      hcu, hdecoded, hrange, List.map]
    rw [hu0', hu1', ← hs.full_value]
    dsimp only [out0, out1, fullOut]
    rw [hcu]
  · have hrange : List.range 2 = [0, 1] := by decide
    have hu0' : fw_maybe_unshuffle_collective [q0, q1] [0, 2 * lDim] 2 0 = source0 := by
      rwa [hdecoded] at hu0
    have hu1' : fw_maybe_unshuffle_collective [q0, q1] [0, 2 * lDim] 2 1 = source1 := by
      rwa [hdecoded] at hu1
    simp only [fw_attn_zigzag_collective, show (2 : Nat) ≠ 1 by omega, if_false,
      hcu, hdecoded, hrange, List.map]
    rw [hu0', hu1', ← hs.full_value]
    dsimp only [out0, out1, fullOut]
    rw [hcu]
  · rw [hcu, hdecoded]
    have hwf : ZigzagCuWF [0, 2 * lDim] [source0, source1] 2 := by
      rw [← hdecoded]
      exact hs.cu_wf
    exact ZigzagCuWF.transport_cp2_3d [0, 2 * lDim] source0 source1 out0 out1
      lDim qHeads vDim hwf (by rw [hs0]; rfl) ho0 ho1

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
