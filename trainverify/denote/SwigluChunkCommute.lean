/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ChunkGatherDim0

/-!
# Elementwise ops commute with dim-0 chunking

`fw_swiglu` reads both inputs at the same flat index, so splitting the inputs
across ranks and computing locally gives the same shard as computing globally
and then splitting. That is what lets the self-decoder MoE branch relate its
per-rank `FW_swiglu` nodes back to the single-machine one.
-/

namespace TrainVerify.Denote

-- Scratch: swiglu is elementwise, so chunking on dim 0 commutes with it.
set_option maxRecDepth 1000000 in
theorem chunk_fw_swiglu_dim0 (numParts rank a b : Nat) (gate up : Tensor)
    (hg : gate.shape = [a, b]) (hu : up.shape = [a, b])
    (hnp : 0 < numParts) (hb : 0 < b) (hr : rank < numParts) (hdvd : numParts ∣ a) :
    chunkPrimDimN 0 numParts rank (fw_swiglu gate up) =
      fw_swiglu (chunkPrimDimN 0 numParts rank gate)
        (chunkPrimDimN 0 numParts rank up) := by
  have hnp' : numParts ≠ 0 := by omega
  have hsw_shape : (fw_swiglu gate up).shape = [a, b] := by
    unfold fw_swiglu; simp [Tensor.mkShape, hu]
  have hlhs : (chunkPrimDimN 0 numParts rank (fw_swiglu gate up)).shape
      = [a / numParts, b] := by
    rw [chunkPrimDimN_shape 0 numParts rank _ _ hsw_shape hnp']
    simp [List.set, List.getD]
  have hcg : (chunkPrimDimN 0 numParts rank gate).shape = [a / numParts, b] := by
    rw [chunkPrimDimN_shape 0 numParts rank _ _ hg hnp']
    simp [List.set, List.getD]
  have hcu : (chunkPrimDimN 0 numParts rank up).shape = [a / numParts, b] := by
    rw [chunkPrimDimN_shape 0 numParts rank _ _ hu hnp']
    simp [List.set, List.getD]
  have hrhs : (fw_swiglu (chunkPrimDimN 0 numParts rank gate)
      (chunkPrimDimN 0 numParts rank up)).shape = [a / numParts, b] := by
    unfold fw_swiglu; simp [Tensor.mkShape, hcu]
  apply Tensor.ext (by rw [hlhs, hrhs])
  intro idx hidx
  rw [hlhs] at hidx
  have hidxlt : idx < a / numParts * b := by simpa [prodShape] using hidx
  set i := idx / b with hidef
  set j := idx % b with hjdef
  have hj : j < b := Nat.mod_lt _ (by omega)
  have hi : i < a / numParts := by
    rw [hidef]; apply Nat.div_lt_of_lt_mul
    calc idx < a / numParts * b := hidxlt
      _ = b * (a / numParts) := by ring
  have hidx_eq : idx = i * b + j := by
    rw [hidef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx b).symm
  rw [hidx_eq]
  rw [chunkPrimDimN0_valAt numParts rank a b _ hsw_shape hnp hb hr i hi j hj]
  -- Bounds, stated up front rather than inline: `simpa ... using` does not align
  -- reliably here (AGENTS #8/#30).
  have hfull_lt : (rank * (a / numParts) + i) * b + j < a * b := by
    have hd : numParts * (a / numParts) = a := Nat.mul_div_cancel' hdvd
    have h1 : rank * (a / numParts) + i < a := by
      have hle : (rank + 1) * (a / numParts) ≤ numParts * (a / numParts) :=
        Nat.mul_le_mul_right _ hr
      calc rank * (a / numParts) + i < rank * (a / numParts) + a / numParts := by omega
        _ = (rank + 1) * (a / numParts) := by ring
        _ ≤ numParts * (a / numParts) := hle
        _ = a := hd
    calc (rank * (a / numParts) + i) * b + j < (rank * (a / numParts) + i) * b + b := by omega
      _ = (rank * (a / numParts) + i + 1) * b := by ring
      _ ≤ a * b := Nat.mul_le_mul_right _ h1
  have hloc_lt : i * b + j < a / numParts * b := by
    calc i * b + j < i * b + b := by omega
      _ = (i + 1) * b := by ring
      _ ≤ a / numParts * b := Nat.mul_le_mul_right _ hi
  -- `prodShape [x, y]` is `x * y`; convert once, then use the bounds above
  -- directly rather than asking omega to see through the fold.
  have hps : ∀ x y : Nat, prodShape [x, y] = x * y := by
    intro x y; simp [prodShape, List.foldl]
  have hup_bound : (rank * (a / numParts) + i) * b + j < prodShape up.shape := by
    rw [hu, hps]; exact hfull_lt
  have hcu_bound : i * b + j < prodShape (chunkPrimDimN 0 numParts rank up).shape := by
    rw [hcu, hps]; exact hloc_lt
  -- Rewrite the two `valAt` reads on the swiglu tensors BEFORE unfolding: once
  -- `fw_swiglu` is unfolded the tensor is a `Tensor.mkShape` literal and
  -- `valAt_of_lt` no longer matches.
  have hsw_bound : (rank * (a / numParts) + i) * b + j
      < prodShape (fw_swiglu gate up).shape := by
    rw [hsw_shape, hps]; exact hfull_lt
  have hswc_bound : i * b + j < prodShape (fw_swiglu
      (chunkPrimDimN 0 numParts rank gate) (chunkPrimDimN 0 numParts rank up)).shape := by
    rw [hrhs, hps]; exact hloc_lt
  rw [valAt_of_lt _ _ hsw_bound, valAt_of_lt _ _ hswc_bound]
  unfold fw_swiglu Tensor.mkShape
  simp only []
  rw [chunkPrimDimN0_valAt numParts rank a b gate hg hnp hb hr i hi j hj,
    chunkPrimDimN0_valAt numParts rank a b up hu hnp hb hr i hi j hj]

end TrainVerify.Denote
