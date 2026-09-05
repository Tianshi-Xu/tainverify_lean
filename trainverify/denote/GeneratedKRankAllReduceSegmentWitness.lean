/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedKRankAllReduceSegmentWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_reduction : RelationFact :=
  .reduction 20 [200, 201, 202] [2, 5, 7]

private def fact_joined_reduce : RelationFact :=
  .joined 20 901 [2, 5, 7]

private def anchor : RelationFact :=
  .tensorShape .sm 77 [1]

private def reduce_pre : RelationState where
  facts := [anchor, fact_reduction]
  nonempty := by decide

private def reduce_post : RelationState where
  facts := [anchor, fact_joined_reduce]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedKRankAllReduceSegmentWitness

namespace TrainVerify.Denote.GeneratedKRankAllReduceSegmentWitness
noncomputable section
private def sm_graph : GraphDecl := { numRanks := 1, nodes := [] }
private def pm_graph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [], outs := [200] }, { rank := 1, op := "OpName.FW_linear", ins := [], outs := [201] }, { rank := 2, op := "OpName.FW_linear", ins := [], outs := [202] }, { rank := 0, op := "OpName.AllReducePrim", ins := [200, 201, 202], outs := [901] }] }
private def segment_reduce_smNodes : List NodeDecl := []
private def segment_reduce_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.AllReducePrim", ins := [200, 201, 202], outs := [901] }]
@[irreducible] private def segment_reduce_smFinal (smStore : Store) : Store :=
  segment_reduce_smNodes.foldl (applyNodeDistributedFaithful sm_graph) smStore
@[irreducible] private def segment_reduce_pmFinal (pmStore : Store) : Store :=
  segment_reduce_pmNodes.foldl (applyNodeDistributedFaithful pm_graph) pmStore

private theorem segment_reduce_ordered_inputs_preserved (pmStore : Store) :
    [200, 201, 202].map (segment_reduce_pmFinal pmStore) = [200, 201, 202].map pmStore := by
  have hFinalRead00 : (segment_reduce_pmFinal pmStore) 200 = pmStore 200 := by
    unfold segment_reduce_pmFinal
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_graph segment_reduce_pmNodes pmStore 200
      (by native_decide) (by native_decide)
  have hFinalRead01 : (segment_reduce_pmFinal pmStore) 201 = pmStore 201 := by
    unfold segment_reduce_pmFinal
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_graph segment_reduce_pmNodes pmStore 201
      (by native_decide) (by native_decide)
  have hFinalRead02 : (segment_reduce_pmFinal pmStore) 202 = pmStore 202 := by
    unfold segment_reduce_pmFinal
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_graph segment_reduce_pmNodes pmStore 202
      (by native_decide) (by native_decide)
  simp only [List.map]
  rw [hFinalRead00, hFinalRead01, hFinalRead02]

private theorem segment_reduce_prefix_inputs_preserved (pmStore : Store) :
    [200, 201, 202].map ((segment_reduce_pmNodes.take 0).foldl
      (applyNodeDistributedFaithful pm_graph) pmStore) = [200, 201, 202].map pmStore := by
  have hPrefixRead00 : ((segment_reduce_pmNodes.take 0).foldl
      (applyNodeDistributedFaithful pm_graph) pmStore) 200 = pmStore 200 := by
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_graph
      (segment_reduce_pmNodes.take 0) pmStore 200
      (by native_decide) (by native_decide)
  have hPrefixRead01 : ((segment_reduce_pmNodes.take 0).foldl
      (applyNodeDistributedFaithful pm_graph) pmStore) 201 = pmStore 201 := by
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_graph
      (segment_reduce_pmNodes.take 0) pmStore 201
      (by native_decide) (by native_decide)
  have hPrefixRead02 : ((segment_reduce_pmNodes.take 0).foldl
      (applyNodeDistributedFaithful pm_graph) pmStore) 202 = pmStore 202 := by
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_graph
      (segment_reduce_pmNodes.take 0) pmStore 202
      (by native_decide) (by native_decide)
  simp only [List.map]
  rw [hPrefixRead00, hPrefixRead01, hPrefixRead02]

private theorem segment_reduce_writer_value (pmStore : Store) :
    (segment_reduce_pmFinal pmStore) 901 =
      allReducePrim 3 0 ([200, 201, 202].map (segment_reduce_pmFinal pmStore)) := by
  have hSplit : segment_reduce_pmNodes = (segment_reduce_pmNodes.take 0) ++
      [{ rank := 0, op := "OpName.AllReducePrim", ins := [200, 201, 202], outs := [901] }] ++ (segment_reduce_pmNodes.drop 1) := by native_decide
  have hWriter : (segment_reduce_pmFinal pmStore) 901 =
      allReducePrim 3 0 ([200, 201, 202].map ((segment_reduce_pmNodes.take 0).foldl
        (applyNodeDistributedFaithful pm_graph) pmStore)) := by
    unfold segment_reduce_pmFinal
    rw [hSplit]
    apply foldl_faithful_middle_writer pm_graph pmStore (segment_reduce_pmNodes.take 0)
      (segment_reduce_pmNodes.drop 1) { rank := 0, op := "OpName.AllReducePrim", ins := [200, 201, 202], outs := [901] } 901
      (fun t => allReducePrim 3 0 ([200, 201, 202].map t))
    · intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring]
      · exact applyNode_allReducePrim_out pm_graph t 0 [200, 201, 202] 901
      · decide
      · decide
    · native_decide
    · native_decide
  rw [segment_reduce_prefix_inputs_preserved pmStore] at hWriter
  rw [← segment_reduce_ordered_inputs_preserved pmStore] at hWriter
  exact hWriter

private theorem segment_reduce_publish_state (smStore pmStore : Store)
    (hstate : reduce_pre.Holds smStore pmStore) :
    reduce_post.Holds (segment_reduce_smFinal smStore) (segment_reduce_pmFinal pmStore) := by
  have hframe : reduce_pre.Holds (segment_reduce_smFinal smStore) (segment_reduce_pmFinal pmStore) := by
    unfold segment_reduce_smFinal segment_reduce_pmFinal
    apply RelationState.Holds.fold_frame segment_reduce_smNodes segment_reduce_pmNodes smStore pmStore hstate
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  have hin : fact_reduction.Holds (segment_reduce_smFinal smStore) (segment_reduce_pmFinal pmStore) :=
    hframe fact_reduction (by native_decide)
  change ReductionRel ((segment_reduce_smFinal smStore) 20) ([200, 201, 202].map (segment_reduce_pmFinal pmStore))
    [2, 5, 7] at hin
  have hWriter := segment_reduce_writer_value pmStore
  have hJoined : (segment_reduce_smFinal smStore) 20 = (segment_reduce_pmFinal pmStore) 901 :=
    (ReductionRel.to_joined_allReduce hin).trans hWriter.symm
  have hout : fact_joined_reduce.Holds (segment_reduce_smFinal smStore) (segment_reduce_pmFinal pmStore) := by
    change (segment_reduce_smFinal smStore) 20 = (segment_reduce_pmFinal pmStore) 901 ∧
      ((segment_reduce_smFinal smStore) 20).shape = [2, 5, 7] ∧
      ((segment_reduce_pmFinal pmStore) 901).shape = [2, 5, 7]
    refine ⟨hJoined, hin.full_shape, ?_⟩
    rw [← hJoined]
    exact hin.full_shape
  exact RelationState.Holds.mono_insert hframe hout (by native_decide)

private def segment_reduce :
    ClosedDepSegmentCertificate sm_graph pm_graph reduce_pre reduce_post where
  smNodes := segment_reduce_smNodes
  pmNodes := segment_reduce_pmNodes
  sound := by
    intro smStore pmStore hstate
    simpa [segment_reduce_smFinal, segment_reduce_pmFinal] using
      (segment_reduce_publish_state smStore pmStore hstate)

#print axioms segment_reduce
end
end TrainVerify.Denote.GeneratedKRankAllReduceSegmentWitness
