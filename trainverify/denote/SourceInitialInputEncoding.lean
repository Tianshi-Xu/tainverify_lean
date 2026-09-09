import denote.ChunkGatherDim0

/-!
# Ordered source-list encoding commutes with batch chunking

Static proof candidate: deliberately uncompiled in this isolated lane; the
parent owns serial kernel checking. The encoding below is literally the tensor
record emitted by `Verdict/runtime_input_feed.py:85-91`. No evaluator is added.
The caller supplies ordered list slicing, not the desired tensor equality.
-/
namespace TrainVerify.Denote.SourceInitialInputEncoding
noncomputable section
set_option maxHeartbeats 500000

/-- The actual row-major Int-to-Scalar encoding used by the input emitter. -/
def intMatrix (rows width : Nat) (values : List Int) : Tensor :=
  { shape := [rows, width]
    val := fun i => ((values.getD i.val 0 : Int) : Scalar) }

private theorem matrix_prod (rows width : Nat) :
    prodShape [rows, width] = rows * width := by
  simp only [prodShape, List.foldl, Nat.one_mul]

theorem intMatrix_valAt (rows width : Nat) (values : List Int)
    (k : Nat) (hk : k < rows * width) :
    valAt (intMatrix rows width values) k = ((values.getD k 0 : Int) : Scalar) := by
  have hb : k < prodShape (intMatrix rows width values).shape := by
    change k < prodShape [rows, width]
    rw [matrix_prod]
    exact hk
  rw [valAt_of_lt _ _ hb]
  rfl

/-- Taking an ordered window preserves each in-window read and its offset. -/
theorem getD_ordered_slice (values : List Int) (start count k : Nat)
    (hk : k < count) :
    ((values.drop start).take count).getD k 0 = values.getD (start + k) 0 := by
  simp only [List.getD, List.getElem?_take_of_lt hk, List.getElem?_drop]

/-- Generic batch-row slice bridge. Exact lengths are part of the source
contract; they exclude truncated or surplus encodings. The pointwise argument
itself is stronger and does not need them, because both encodings use getD 0.
Rows may be zero; width and the number of units must be positive. -/
theorem intMatrix_ordered_slice_eq_chunk
    (fullValues localValues : List Int) (units unit rows width : Nat)
    (hunits : 0 < units) (hwidth : 0 < width) (hunit : unit < units)
    (_hfullLength : fullValues.length = rows * units * width)
    (_hlocalLength : localValues.length = rows * width)
    (hslice : localValues =
      (fullValues.drop (unit * rows * width)).take (rows * width)) :
    intMatrix rows width localValues =
      chunkPrimDimN 0 units unit (intMatrix (rows * units) width fullValues) := by
  have hdiv : rows * units / units = rows := Nat.mul_div_cancel rows hunits
  have hshape :
      (chunkPrimDimN 0 units unit (intMatrix (rows * units) width fullValues)).shape =
        [rows, width] := by
    rw [chunkPrimDimN_shape 0 units unit _ [rows * units, width]
      rfl (Nat.ne_of_gt hunits)]
    simp only [List.set, List.getD_cons_zero, hdiv]
  apply Tensor.ext (show [rows, width] = _ from hshape.symm)
  intro k hk
  change k < prodShape [rows, width] at hk
  rw [matrix_prod] at hk
  have hi : k / width < rows := by
    apply Nat.div_lt_of_lt_mul
    calc k < rows * width := hk
      _ = width * rows := Nat.mul_comm rows width
  have hj : k % width < width := Nat.mod_lt k hwidth
  have hflat : k / width * width + k % width = k := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod k width
  have hoff : (unit * rows + k / width) * width + k % width =
      unit * rows * width + k := by
    rw [Nat.add_mul, Nat.add_assoc, hflat]
  have hchunk := chunkPrimDimN0_valAt units unit (rows * units) width
    (intMatrix (rows * units) width fullValues) rfl hunits hwidth hunit
    (k / width) (by rw [hdiv]; exact hi) (k % width) hj
  rw [hdiv, hflat, hoff] at hchunk
  have hupper : (unit + 1) * (rows * width) ≤ units * (rows * width) :=
    Nat.mul_le_mul_right _ hunit
  have hglobal : unit * rows * width + k < rows * units * width := by
    calc
      unit * rows * width + k < unit * rows * width + rows * width :=
        Nat.add_lt_add_left hk _
      _ = (unit + 1) * (rows * width) := by ring
      _ ≤ units * (rows * width) := hupper
      _ = rows * units * width := by ring
  rw [hchunk, intMatrix_valAt rows width localValues k hk,
    intMatrix_valAt (rows * units) width fullValues _ hglobal, hslice,
    getD_ordered_slice fullValues (unit * rows * width) (rows * width) k hk]

/-- Adapter for named emitted tensor records. The two encoding equations are
`rfl` for the emitter's definitions; neither is a chunk-equality assumption. -/
theorem emitted_ordered_slice_eq_chunk
    (full piece : Tensor) (fullValues localValues : List Int)
    (units unit rows width : Nat)
    (hfull : full = intMatrix (rows * units) width fullValues)
    (hlocal : piece = intMatrix rows width localValues)
    (hunits : 0 < units) (hwidth : 0 < width) (hunit : unit < units)
    (hfullLength : fullValues.length = rows * units * width)
    (hlocalLength : localValues.length = rows * width)
    (hslice : localValues =
      (fullValues.drop (unit * rows * width)).take (rows * width)) :
    piece = chunkPrimDimN 0 units unit full := by
  rw [hfull, hlocal]
  exact intMatrix_ordered_slice_eq_chunk fullValues localValues units unit rows width
    hunits hwidth hunit hfullLength hlocalLength hslice

#print axioms intMatrix_ordered_slice_eq_chunk
#print axioms emitted_ordered_slice_eq_chunk
end
end TrainVerify.Denote.SourceInitialInputEncoding
