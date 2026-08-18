import denote.KRankMatmulContractionReduction

namespace TrainVerify.Denote.RelationCompiler

/-- Export witness: the family-D contraction-axis theorem remains rank-count
polymorphic and preserves the input-list order through `List.zipWith`. -/
example
    {x y : Tensor} {xs ys : List Tensor} {K b h q k m : Nat}
    (hxrel : ShardedRel x xs 3 [b, h, q, k * K] [b, h, q, k])
    (hyrel : ShardedRel y ys 2 [b, h, k * K, m] [b, h, k, m])
    (hK : 0 < K) (hq : 0 < q) (hk : 0 < k) (hm : 0 < m)
    (hxslen : xs.length = K) (hyslen : ys.length = K) :
    ReductionRel (fw_matmul x y) (List.zipWith fw_matmul xs ys)
      [b, h, q, m] :=
  ShardedRel.fw_matmul_contraction_axis_rank4
    hxrel hyrel hK hq hk hm hxslen hyslen

#print axioms TrainVerify.Denote.fw_matmul_allGather_contraction_eq_allReduce_zipWith_rank4
#print axioms ShardedRel.fw_matmul_contraction_axis_rank4

end TrainVerify.Denote.RelationCompiler
