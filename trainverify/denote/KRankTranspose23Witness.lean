import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler

/-- Symbolic dynamic-rank witness for `transposeAxes 2 3`: the ordered shard
list determines `K = shards.length`, and a dim-2 gather is transported to dim 3. -/
theorem kRankTranspose23Dim2ToDim3SymbolicWitness
    {full : Tensor} {shards : List Tensor} {b h q k : Nat}
    (hin : ShardedRel full shards 2
      [b, h, q * shards.length, k] [b, h, q, k]) :
    ShardedRel (transposeAxes 2 3 full) (shards.map (transposeAxes 2 3)) 3
      [b, h, k, q * shards.length] [b, h, k, q] := by
  exact ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4 hin

#print axioms transposeAxes_2_3_allGather_dim2_to_dim3_rank4
#print axioms ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4
#print axioms kRankTranspose23Dim2ToDim3SymbolicWitness

end TrainVerify.Denote
