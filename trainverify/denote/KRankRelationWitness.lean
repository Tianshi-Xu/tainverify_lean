import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

#check RelationFact.sharded
#check RelationFact.joined
#check RelationFact.replicated
#check ReplicatedRel.replica_values
#check ShardedRel.full_value
#check ShardedRel.shards_nonempty
#check ShardedRel.gather_dim_lt
#check ShardedRel.shape_contract
#check ShardedRel.of_init_goal
#print axioms ShardedRel.of_init_goal
#check ShardedRel.shard_shapes

example (sm pm : Store) (smTid : Tid) (pmTids : List Tid)
    (dim : Nat) (fullShape shardShape : Shape) :
    RelationFact.Holds (.sharded smTid pmTids dim fullShape shardShape) sm pm =
      ShardedRel (sm smTid) (pmTids.map pm) dim fullShape shardShape := by
  rfl

example (sm pm : Store) (smTid pmTid : Tid) (shape : Shape) :
    RelationFact.Holds (.joined smTid pmTid shape) sm pm =
      (sm smTid = pm pmTid ∧
       (sm smTid).shape = shape ∧
       (pm pmTid).shape = shape) := by
  rfl

example (sm pm : Store) (smTid : Tid) (pmTids : List Tid) (shape : Shape) :
    RelationFact.Holds (.replicated smTid pmTids shape) sm pm =
      ReplicatedRel (sm smTid) (pmTids.map pm) shape := by
  rfl
