import denote.KRankSoftmaxGather

namespace TrainVerify.Denote.RelationCompiler

section

variable {full : Tensor} {shards : List Tensor}
variable {d0 d1 d2 d3 : Nat}

/-- Symbolic dim-1 witness: the rank count remains `shards.length`. -/
theorem kRankSoftmax_dim1_symbolic_witness
    (hd3 : 0 < d3)
    (h : ShardedRel full shards 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3]) :
    ShardedRel (fw_softmax full) (shards.map fw_softmax) 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3] :=
  h.fw_softmax_dim1_rank4 hd3

/-- Symbolic dim-2 witness: no fixed rank count, extent, or tensor id occurs. -/
theorem kRankSoftmax_dim2_symbolic_witness
    (hd3 : 0 < d3)
    (h : ShardedRel full shards 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3]) :
    ShardedRel (fw_softmax full) (shards.map fw_softmax) 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3] :=
  h.fw_softmax_dim2_rank4 hd3

#print axioms fw_softmax_allGatherPrimDimN_dim1_rank4
#print axioms fw_softmax_allGatherPrimDimN_dim2_rank4
#print axioms ShardedRel.fw_softmax_dim1_rank4
#print axioms ShardedRel.fw_softmax_dim2_rank4
#print axioms kRankSoftmax_dim1_symbolic_witness
#print axioms kRankSoftmax_dim2_symbolic_witness

end

end TrainVerify.Denote.RelationCompiler
