import denote.KRankDivGather

namespace TrainVerify.Denote.RelationCompiler

section

variable {full : Tensor} {shards : List Tensor}
variable {d0 d1 d2 d3 : Nat}

/-- Symbolic dim-1 witness: arbitrary scalar and dynamic ordered rank list. -/
theorem kRankDiv_dim1_symbolic_witness
    (c : Scalar)
    (h : ShardedRel full shards 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3]) :
    ShardedRel (fw_div c full) (shards.map (fw_div c)) 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3] :=
  h.fw_div_dim1_rank4 c

/-- Symbolic dim-2 witness: arbitrary scalar and no fixed ranks, extents, or TIDs. -/
theorem kRankDiv_dim2_symbolic_witness
    (c : Scalar)
    (h : ShardedRel full shards 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3]) :
    ShardedRel (fw_div c full) (shards.map (fw_div c)) 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3] :=
  h.fw_div_dim2_rank4 c

/-- Symbolic dim-3 witness: arbitrary scalar and no fixed ranks, extents, or TIDs. -/
theorem kRankDiv_dim3_symbolic_witness
    (c : Scalar)
    (h : ShardedRel full shards 3
      [d0, d1, d2, d3 * shards.length] [d0, d1, d2, d3]) :
    ShardedRel (fw_div c full) (shards.map (fw_div c)) 3
      [d0, d1, d2, d3 * shards.length] [d0, d1, d2, d3] :=
  h.fw_div_dim3_rank4 c

#print axioms fw_div_allGatherPrimDimN_dim1_rank4
#print axioms fw_div_allGatherPrimDimN_dim2_rank4
#print axioms fw_div_allGatherPrimDimN_dim3_rank4
#print axioms ShardedRel.fw_div_dim1_rank4
#print axioms ShardedRel.fw_div_dim2_rank4
#print axioms ShardedRel.fw_div_dim3_rank4
#print axioms kRankDiv_dim1_symbolic_witness
#print axioms kRankDiv_dim2_symbolic_witness
#print axioms kRankDiv_dim3_symbolic_witness

end

end TrainVerify.Denote.RelationCompiler
