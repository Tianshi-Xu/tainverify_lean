import denote.ZigzagKAttentionRefinement
import denote.ZigzagKAttentionWitness

open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
open TrainVerify.Denote.ZigzagCollective TrainVerify.Denote.ZigzagAttentionSource

namespace TrainVerify.Denote.ZigzagKAttentionRefinementWitness
noncomputable section
open ZigzagKAttentionWitness

def sourceRank (rank : Nat) : Tensor :=
  sourceOutput (qs.getD rank (zeroTensor []))
    (allGatherPrimDimN 0 3 0 (sources k)) (allGatherPrimDimN 0 3 0 (sources v))
    3 rank 2 2 1 2 2

/-- Every rank of the inhabited GQA source model equals the actual collective. -/
theorem source_rank (rank : Nat) (hr : rank < 3) :
    sourceRank rank = fw_attn_zigzag_collective_sharded_kv
      qs (sources k) (sources v) cu cu 2 1 2 2 true 0 3 rank := by
  exact ZigzagKRel.sourceOutput_eq_collective q k v cu qs (sources k) (sources v)
    3 rank 2 2 1 2 2 entry k_sharded v_sharded
    (by simp only [qs, List.length_map, List.length_range])
    (by simp only [sources, List.length_map, List.length_range])
    (by simp only [sources, List.length_map, List.length_range])
    ZigzagAttentionSourceWitness.decode_cu (by decide) hr
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Complete ordered Tensor-list equality, not selected scalar observations. -/
theorem source_outputs : (List.range 3).map sourceRank = outputs := by
  apply List.map_congr_left
  intro r hr
  exact source_rank r (List.mem_range.mp hr)

/-- Exit reconstruction of the source branch tensors keeps the full attention
shape and every ordinary output shape, with no external row-equality assumption. -/
theorem source_exit : ShardedRel fullOut
    ((List.range 3).map (fun r => fw_maybe_unshuffle_collective
      ((List.range 3).map sourceRank) (decodeCuSeqlens cu) 3 r))
    0 [12, 2, 2] [4, 2, 2] := by
  rw [source_outputs]
  exact attention_exit

end
end TrainVerify.Denote.ZigzagKAttentionRefinementWitness
