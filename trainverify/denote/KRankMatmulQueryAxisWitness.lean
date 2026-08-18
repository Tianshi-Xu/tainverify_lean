import denote.KRankMatmulQueryAxis

namespace TrainVerify.Denote.RelationCompiler

/-- A concrete three-rank use of the dynamic query-axis wrapper, with the
right operand shared by actual value equality. -/
theorem fw_matmul_query_axis_rank4_K3_witness
    {x y : Tensor} {xs : List Tensor} {b h q k m : Nat}
    (hrel : ShardedRel x xs 2 [b, h, q * 3, k] [b, h, q, k])
    (hy : y.shape = [b, h, k, m])
    (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hlen : xs.length = 3) :
    ShardedRel (fw_matmul x y)
      (xs.map (fun shard => fw_matmul shard y)) 2
      [b, h, q * 3, m] [b, h, q, m] := by
  exact ShardedRel.fw_matmul_query_axis_rank4 hrel ⟨rfl, hy, hy⟩
    (by decide) hq hk hm hlen

end TrainVerify.Denote.RelationCompiler

#print axioms TrainVerify.Denote.RelationCompiler.fw_matmul_query_axis_rank4_K3_witness
