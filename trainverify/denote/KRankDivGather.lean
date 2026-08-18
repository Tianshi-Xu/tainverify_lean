import denote.RelationCompiler

namespace TrainVerify.Denote

noncomputable section

/-- Scalar division commutes with an arbitrary nonempty ordered dim-1 gather
of symbolic rank-4 shards.  The rank count is exactly `xs.length`. -/
theorem fw_div_allGatherPrimDimN_dim1_rank4
    (c : Scalar) (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    fw_div c (allGatherPrimDimN 1 xs.length 0 xs) =
      allGatherPrimDimN 1 xs.length 0 (xs.map (fw_div c)) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] =
      [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  exact fw_div_allGatherPrimDimN_eq_g17 c 1 xs.length xs
    [d0, d1, d2, d3] hK rfl hhead (by
      intro i hi
      exact hshapes xs[i] (List.getElem_mem hi))

/-- Scalar division commutes with an arbitrary nonempty ordered dim-2 gather
of symbolic rank-4 shards.  The rank count is exactly `xs.length`. -/
theorem fw_div_allGatherPrimDimN_dim2_rank4
    (c : Scalar) (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    fw_div c (allGatherPrimDimN 2 xs.length 0 xs) =
      allGatherPrimDimN 2 xs.length 0 (xs.map (fw_div c)) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] =
      [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  exact fw_div_allGatherPrimDimN_eq_g17 c 2 xs.length xs
    [d0, d1, d2, d3] hK rfl hhead (by
      intro i hi
      exact hshapes xs[i] (List.getElem_mem hi))

/-- Scalar division commutes with an arbitrary nonempty ordered dim-3 gather
of symbolic rank-4 shards.  The rank count is exactly `xs.length`. -/
theorem fw_div_allGatherPrimDimN_dim3_rank4
    (c : Scalar) (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    fw_div c (allGatherPrimDimN 3 xs.length 0 xs) =
      allGatherPrimDimN 3 xs.length 0 (xs.map (fw_div c)) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] =
      [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  exact fw_div_allGatherPrimDimN_eq_g17 c 3 xs.length xs
    [d0, d1, d2, d3] hK rfl hhead (by
      intro i hi
      exact hshapes xs[i] (List.getElem_mem hi))

end

end TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

noncomputable section

/-- Exact rank-4 dim-1 `ShardedRel` transport for arbitrary scalar division. -/
theorem ShardedRel.fw_div_dim1_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3])
    (c : Scalar) :
    ShardedRel (fw_div c full) (shards.map (fw_div c)) 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      fw_div_allGatherPrimDimN_dim1_rank4 c shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · rw [fw_div_shape_g17, h.full_shape]
  · simpa using h.shards_nonempty
  · exact h.gather_dim_lt
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rw [fw_div_shape_g17, h.shard_shapes source hsource]
  · simpa only [List.length_map] using h.shape_contract

/-- Exact rank-4 dim-2 `ShardedRel` transport for arbitrary scalar division. -/
theorem ShardedRel.fw_div_dim2_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3])
    (c : Scalar) :
    ShardedRel (fw_div c full) (shards.map (fw_div c)) 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      fw_div_allGatherPrimDimN_dim2_rank4 c shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · rw [fw_div_shape_g17, h.full_shape]
  · simpa using h.shards_nonempty
  · exact h.gather_dim_lt
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rw [fw_div_shape_g17, h.shard_shapes source hsource]
  · simpa only [List.length_map] using h.shape_contract

/-- Exact rank-4 dim-3 `ShardedRel` transport for arbitrary scalar division. -/
theorem ShardedRel.fw_div_dim3_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 3
      [d0, d1, d2, d3 * shards.length] [d0, d1, d2, d3])
    (c : Scalar) :
    ShardedRel (fw_div c full) (shards.map (fw_div c)) 3
      [d0, d1, d2, d3 * shards.length] [d0, d1, d2, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      fw_div_allGatherPrimDimN_dim3_rank4 c shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · rw [fw_div_shape_g17, h.full_shape]
  · simpa using h.shards_nonempty
  · exact h.gather_dim_lt
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rw [fw_div_shape_g17, h.shard_shapes source hsource]
  · simpa only [List.length_map] using h.shape_contract

end

end TrainVerify.Denote.RelationCompiler
