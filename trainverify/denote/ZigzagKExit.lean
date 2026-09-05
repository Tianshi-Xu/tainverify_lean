import denote.RelationCompiler
import denote.KRankZigzagSingle

/-! Single-sequence exits from the arbitrary-rank zigzag relation through the
actual ordered collectives. No compiler acceptance or graph semantics change. -/

namespace TrainVerify.Denote.RelationCompiler

/-- The complete ordered unshuffle list recovers the original ordinary sources.
The tail may have zero volume; only the half-shard token count is positive. -/
theorem unshuffle_shuffle_single_list
    (sources : List Tensor) (K d : Nat) (tail : Shape)
    (hK : 0 < K) (hd : 0 < d) (hlen : sources.length = K)
    (hshapes : ∀ x ∈ sources, x.shape = (2 * d) :: tail) :
    ((List.range K).map (fun rank =>
      ZigzagCollective.fw_maybe_unshuffle_collective
        ((List.range K).map
          (ZigzagCollective.fw_maybe_shuffle_collective sources [0, K * (2 * d)] K))
        [0, K * (2 * d)] K rank)) = sources := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hlen]
  · intro rank hleft hright
    have hrank : rank < K := by
      simpa only [List.length_map, List.length_range] using hleft
    rw [List.getElem_map, List.getElem_range,
      ZigzagCollective.fw_maybe_unshuffle_shuffle_collective_single
        sources K d rank tail hK hd hrank hlen hshapes]
    unfold List.getD
    rw [List.getElem?_eq_getElem hright, Option.getD_some]

/-- Restore the hidden ordinary sources, preserving their full value and every
shape field. Single-sequence decoding is explicit, not inferred from metadata WF. -/
theorem ZigzagKRel.to_sharded_unshuffle_single
    {full cu : Tensor} {outputs : List Tensor}
    {fullShape tail : Shape} {d : Nat}
    (h : ZigzagKRel full outputs cu fullShape ((2 * d) :: tail))
    (hd : 0 < d)
    (hdecode : decodeCuSeqlens cu = [0, outputs.length * (2 * d)]) :
    ShardedRel full
      ((List.range outputs.length).map (fun rank =>
        ZigzagCollective.fw_maybe_unshuffle_collective outputs
          (decodeCuSeqlens cu) outputs.length rank))
      0 fullShape ((2 * d) :: tail) := by
  rcases h with ⟨sources, hsource, hlen, hcu, houtputs⟩
  have hexit := unshuffle_shuffle_single_list sources outputs.length d tail
    hcu.cp_pos hd hlen hsource.shard_shapes
  rw [← hdecode, ← houtputs] at hexit
  rw [hexit]
  exact hsource

/-- Backward shuffle is the actual forward-unshuffle collective alias, so it
restores the same ordinary relation without a separate inverse model. -/
theorem ZigzagKRel.to_sharded_bw_shuffle_single
    {full cu : Tensor} {outputs : List Tensor}
    {fullShape tail : Shape} {d : Nat}
    (h : ZigzagKRel full outputs cu fullShape ((2 * d) :: tail))
    (hd : 0 < d)
    (hdecode : decodeCuSeqlens cu = [0, outputs.length * (2 * d)]) :
    ShardedRel full
      ((List.range outputs.length).map (fun rank =>
        bw_maybe_shuffle_collective outputs
          (decodeCuSeqlens cu) outputs.length rank))
      0 fullShape ((2 * d) :: tail) := by
  simp only [ZigzagCollective.bw_maybe_shuffle_collective_eq_fw_unshuffle]
  exact h.to_sharded_unshuffle_single hd hdecode

end TrainVerify.Denote.RelationCompiler
