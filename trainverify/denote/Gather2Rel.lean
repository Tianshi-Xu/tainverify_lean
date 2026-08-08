import denote.Denote

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

/-- A value and shape package for a dim-0 reconstruction from exactly two shards. -/
structure Gather2Rel (full shard0 shard1 : Tensor) (fullShape shardShape : Shape) : Prop where
  value : full = allGatherPrimDimN 0 2 0 [shard0, shard1]
  full_shape : full.shape = fullShape
  shard0_shape : shard0.shape = shardShape
  shard1_shape : shard1.shape = shardShape
  nonscalar : shardShape ≠ [1]

end TrainVerify.Denote.GeneratedPatterns
