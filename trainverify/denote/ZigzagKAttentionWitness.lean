import denote.ZigzagKAttention
import denote.ZigzagKAttentionSourceWitness

/-! Inhabited attention input, complete attention-output relation, and ordinary
exit over the actual collectives. This is not a generated graph/public theorem. -/

open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.ZigzagKAttentionWitness
noncomputable section

abbrev q := ZigzagAttentionSourceWitness.q
abbrev k := ZigzagAttentionSourceWitness.k
abbrev v := ZigzagAttentionSourceWitness.v
abbrev cu := ZigzagAttentionSourceWitness.cu

def sources (x : Tensor) : List Tensor :=
  (List.range 3).map (fun r => chunkPrimDimN 0 3 r x)
def qs : List Tensor := (List.range 3).map
  (fw_maybe_shuffle_collective (sources q) (decodeCuSeqlens cu) 3)
def outputs : List Tensor := (List.range 3).map (fun r =>
  fw_attn_zigzag_collective_sharded_kv qs (sources k) (sources v) cu cu 2 1 2 2 true 0 3 r)
def fullOut : Tensor := fw_attn_varlen q k v cu cu 2 1 2 2 true 0

theorem q_sharded : ShardedRel q (sources q) 0 [12, 2, 2] [4, 2, 2] :=
  ShardedRel.attention_chunks q 3 2 2 2 (by decide) rfl

theorem k_sharded : ShardedRel k (sources k) 0 [12, 1, 2] [4, 1, 2] :=
  ShardedRel.attention_chunks k 3 2 1 2 (by decide) rfl

theorem v_sharded : ShardedRel v (sources v) 0 [12, 1, 2] [4, 1, 2] :=
  ShardedRel.attention_chunks v 3 2 1 2 (by decide) rfl

theorem q_metadata : ZigzagCuWF (decodeCuSeqlens cu) (sources q) (sources q).length := by
  rw [ZigzagAttentionSourceWitness.decode_cu]
  have hlen : (sources q).length = 3 := by simp only [sources, List.length_map, List.length_range]
  rw [hlen]
  have hfirst : ((sources q).getD 0 (zeroTensor [])).shape = [4, 2, 2] := rfl
  refine ⟨by decide, hlen, rfl, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have : s = 0 := by simp only [List.length_cons, List.length_nil] at hs; omega
    subst s
    decide
  · intro s hs
    have : s = 0 := by simp only [List.length_cons, List.length_nil] at hs; omega
    subst s
    decide
  · intro x hx
    rw [q_sharded.shard_shapes x hx]
    decide
  · intro x hx
    rw [q_sharded.shard_shapes x hx, hfirst]
  · rw [hfirst]
    rfl

theorem entry : ZigzagKRel q qs cu [12, 2, 2] [4, 2, 2] :=
  ZigzagKRel.of_sharded q_sharded q_metadata

/-- No caller assumptions: the explicit asymmetric Q/K/V satisfy the relation. -/
theorem attention : ZigzagKRel fullOut outputs cu [12, 2, 2] [4, 2, 2] := by
  exact ZigzagKRel.attn_zigzag_sharded_kv_single q k v cu cu qs (sources k) (sources v)
    3 2 2 1 2 2 entry k_sharded v_sharded
    (by simp only [qs, List.length_map, List.length_range])
    (by simp only [sources, List.length_map, List.length_range])
    (by simp only [sources, List.length_map, List.length_range])
    ZigzagAttentionSourceWitness.decode_cu
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The ordinary exit reconstructs the actual full attention tensor, not Q. -/
theorem attention_exit : ShardedRel fullOut
    ((List.range 3).map (fun r => fw_maybe_unshuffle_collective outputs
      (decodeCuSeqlens cu) 3 r)) 0 [12, 2, 2] [4, 2, 2] := by
  have h := attention.to_sharded_unshuffle_single (d := 2) (by decide)
    (by simpa only [outputs, List.length_map, List.length_range] using
      ZigzagAttentionSourceWitness.decode_cu)
  exact h

end
end TrainVerify.Denote.ZigzagKAttentionWitness
