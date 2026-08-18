import denote.KRankTranspose23Extra

namespace TrainVerify.Denote
open RelationCompiler

/-- Symbolic dynamic-rank witness for `transposeAxes 2 3`: the ordered shard
list determines `K = shards.length`, and a dim-3 gather is transported to dim 2. -/
theorem kRankTranspose23Dim3ToDim2SymbolicWitness
    {full : Tensor} {shards : List Tensor} {b h q k : Nat}
    (hin : ShardedRel full shards 3
      [b, h, q, k * shards.length] [b, h, q, k]) :
    ShardedRel (transposeAxes 2 3 full) (shards.map (transposeAxes 2 3)) 2
      [b, h, k * shards.length, q] [b, h, k, q] := by
  exact ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4 hin

/-- Symbolic dynamic-rank witness for `transposeAxes 2 3`: the ordered shard
list determines `K = shards.length`, and dim-1 sharding is preserved. -/
theorem kRankTranspose23Dim1SymbolicWitness
    {full : Tensor} {shards : List Tensor} {b h q k : Nat}
    (hin : ShardedRel full shards 1
      [b, h * shards.length, q, k] [b, h, q, k]) :
    ShardedRel (transposeAxes 2 3 full) (shards.map (transposeAxes 2 3)) 1
      [b, h * shards.length, k, q] [b, h, k, q] := by
  exact ShardedRel.fw_transposeAxes_2_3_dim1_rank4 hin

#print axioms transposeAxes_2_3_allGather_dim3_to_dim2_rank4
#print axioms transposeAxes_2_3_allGather_dim1_rank4
#print axioms ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4
#print axioms ShardedRel.fw_transposeAxes_2_3_dim1_rank4
#print axioms kRankTranspose23Dim3ToDim2SymbolicWitness
#print axioms kRankTranspose23Dim1SymbolicWitness

end TrainVerify.Denote
