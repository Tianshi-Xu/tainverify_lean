import denote.RelationCompiler
import denote.SourceScopedEval

/-! Initial parameter bridges over the same `Store := Tid → Tensor` consumed
by `SourceScopedEval`. A caller supplies exact mathematical tensor equations,
not digests, observations, or the desired relation. Each `pmTids` is ONE ordered
DP unit; replica units must be instantiated separately, never concatenated.
The runtime-to-`Tensor` refinement is deliberately not asserted here. -/

namespace TrainVerify.Denote.SourceInitialParameters
open RelationCompiler
set_option maxHeartbeats 500000
noncomputable section

/-- Exact ordered slices imply the existing strong typed relation for arbitrary
positive K and any valid tensor dimension. Only reconstruction mathematics from
`allGatherPrimDimN_chunks_ofFn` is used. -/
theorem chunked_of_exact_slices
    (initSM initPM : Store) (smTid : Tid) (pmTids : List Tid)
    (dim K : Nat) (fullShape shardShape : Shape)
    (hK : 0 < K) (hdim : dim < shardShape.length)
    (hfull : (initSM smTid).shape = fullShape)
    (hcontract : fullShape = shardShape.set dim (shardShape.getD dim 0 * K))
    (hSlices : pmTids.map initPM = List.ofFn (fun r : Fin K =>
      chunkPrimDimN dim K r.val (initSM smTid))) :
    RelationFact.Holds (.chunked smTid pmTids dim fullShape shardShape) initSM initPM := by
  have hlen : (pmTids.map initPM).length = K := by
    rw [hSlices, List.length_ofFn]
  have hget : fullShape.getD dim 0 = shardShape.getD dim 0 * K := by
    rw [hcontract]
    simp [List.getD, List.set, hdim]
  have hdimFull : dim < (initSM smTid).shape.length := by
    rw [hfull, hcontract, List.length_set]
    exact hdim
  have hdiv : (initSM smTid).shape.getD dim 0 % K = 0 := by
    rw [hfull, hget]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
  have hchunkShape (r : Fin K) :
      (chunkPrimDimN dim K r.val (initSM smTid)).shape = shardShape := by
    rw [chunkPrimDimN_shape dim K r.val (initSM smTid) fullShape hfull
      (Nat.ne_of_gt hK), hget, Nat.mul_div_cancel _ hK, hcontract,
      List.set_set]
    exact List.set_getD_self shardShape dim
  change ChunkedRel (initSM smTid) (pmTids.map initPM) dim fullShape shardShape
  refine {
    full_value := ?_
    full_shape := hfull
    shards_nonempty := ?_
    gather_dim_lt := hdim
    shard_shapes := ?_
    shape_contract := ?_
    chunk_values := ?_
  }
  · rw [hlen, hSlices]
    exact (allGatherPrimDimN_chunks_ofFn dim K (initSM smTid) hK hdimFull hdiv).symm
  · intro he
    rw [he] at hlen
    have : K = 0 := hlen.symm
    omega
  · intro shard hs
    rw [hSlices] at hs
    rcases List.mem_ofFn.mp hs with ⟨r, hr⟩
    rw [← hr]
    exact hchunkShape r
  · rw [hlen]
    exact hcontract
  · intro r hr
    rw [hlen] at hr
    rw [hlen, hSlices, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hr),
      List.getElem_ofFn]
    rfl

/-- The ordinary typed initial relation is the existing chunked projection. -/
theorem sharded_of_exact_slices
    (initSM initPM : Store) (smTid : Tid) (pmTids : List Tid)
    (dim K : Nat) (fullShape shardShape : Shape)
    (hK : 0 < K) (hdim : dim < shardShape.length)
    (hfull : (initSM smTid).shape = fullShape)
    (hcontract : fullShape = shardShape.set dim (shardShape.getD dim 0 * K))
    (hSlices : pmTids.map initPM = List.ofFn (fun r : Fin K =>
      chunkPrimDimN dim K r.val (initSM smTid))) :
    RelationFact.Holds (.sharded smTid pmTids dim fullShape shardShape) initSM initPM :=
  (chunked_of_exact_slices initSM initPM smTid pmTids dim K fullShape shardShape
    hK hdim hfull hcontract hSlices).toShardedRel

/-- Exact replicas use no collective and likewise remain within one DP unit. -/
theorem replicated_of_exact_values
    (initSM initPM : Store) (smTid : Tid) (pmTids : List Tid) (shape : Shape)
    (hne : pmTids ≠ []) (hfull : (initSM smTid).shape = shape)
    (hValues : ∀ tid ∈ pmTids, initPM tid = initSM smTid) :
    RelationFact.Holds (.replicated smTid pmTids shape) initSM initPM := by
  change ReplicatedRel (initSM smTid) (pmTids.map initPM) shape
  refine ⟨?_, hfull, ?_, ?_⟩
  · exact fun h => hne (List.map_eq_nil_iff.mp h)
  · intro replica hr
    rcases List.mem_map.mp hr with ⟨tid, ht, he⟩
    rw [← he]
    exact hValues tid ht
  · intro replica hr
    rcases List.mem_map.mp hr with ⟨tid, ht, he⟩
    rw [← he, hValues tid ht]
    exact hfull


end
end TrainVerify.Denote.SourceInitialParameters
