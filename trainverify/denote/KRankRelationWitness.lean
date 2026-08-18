import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

#check RelationFact.sharded
#check ShardedRel.full_value
#check ShardedRel.shards_nonempty
#check ShardedRel.shard_shapes

example (sm pm : Store) (smTid : Tid) (pmTids : List Tid)
    (dim : Nat) (fullShape shardShape : Shape) :
    RelationFact.Holds
      (.sharded smTid pmTids dim fullShape shardShape) sm pm =
      ShardedRel (sm smTid) (pmTids.map pm) dim fullShape shardShape := by
  rfl
