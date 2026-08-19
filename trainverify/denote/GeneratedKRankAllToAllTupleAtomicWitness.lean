/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def pre_0 : RelationFact :=
  .sharded 10 [1000, 1001, 1002] 1 [2, 9, 15] [2, 3, 15]

private def post_0 : RelationFact :=
  .sharded 10 [2000, 2001, 2002] 2 [2, 9, 15] [2, 9, 5]

private def pre_1 : RelationFact :=
  .sharded 11 [1100, 1101, 1102] 1 [2, 9, 15] [2, 3, 15]

private def post_1 : RelationFact :=
  .sharded 11 [2100, 2101, 2102] 2 [2, 9, 15] [2, 9, 5]

private def anchor : RelationFact :=
  .tensorShape .sm 777 [1]

private def state_pre : RelationState where
  facts := [anchor, pre_0, pre_1]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, post_0, post_1]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness

namespace TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2000], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2100], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2001], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2101], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2002], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2102], params := [1, 2] }] }
private def segment_generic :
    ClosedDepSegmentCertificate TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.smGraph TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph state_pre state_post where
  smNodes := []
  pmNodes := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2000], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2100], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2001], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2101], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2002], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2102], params := [1, 2] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := []
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2000], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2100], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2001], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2101], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2002], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2102], params := [1, 2] }]
    let pmTids : List Tid := [2000, 2001, 2002]
    let rankCount := pmTids.length
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph.numRanks := by rfl
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    let inputTids0 : List Tid := [1000, 1001, 1002]
    let outputTids0 : List Tid := [2000, 2001, 2002]
    let xs0 := inputTids0.map pmStore
    have hRankCountXs0 : rankCount = xs0.length := by simp [pmTids, inputTids0, outputTids0, xs0, rankCount]
    have hin0 : pre_0.Holds smStore pmStore := hstate pre_0 (by native_decide)
    change ShardedRel (smStore 10) xs0 1 [2, 9, 15] [2, 3, 15] at hin0
    have hHead0 : ((xs0.head?.map (fun t => t.shape)).getD []) = [2, 3, 15] := by
      simp only [xs0, inputTids0, List.map, List.head?, Option.map, Option.getD]
      exact hin0.shard_shapes _ (by simp [xs0, inputTids0])
    have hInputs0_0 : inputTids0.map (((pmNodes.take 0)).foldl
        (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 0) pmStore 1000 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 0) pmStore 1001 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 0) pmStore 1002 (by native_decide) (by native_decide)
    have hAllToAll0_0 : pmFinal 2000 = allToAllPrimWithDims rankCount 0 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) 2000 = _
      rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2000], params := [1, 2] }] ++ (pmNodes.drop 1) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2000], params := [1, 2] } 2000 (fun t => allToAllPrimWithDims rankCount 0 (inputTids0.map t) 1 2)]
      · rw [hInputs0_0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph t 0 inputTids0 2000 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_0 : (pmFinal 2000).shape = [2, 9, 5] := by
      rw [hAllToAll0_0, allToAllPrimWithDims_shape rankCount 0 xs0 1 2 [2, 3, 15] hHead0 (by native_decide)]
      native_decide
    have hInputs0_1 : inputTids0.map (((pmNodes.take 2)).foldl
        (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 2) pmStore 1000 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 2) pmStore 1001 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 2) pmStore 1002 (by native_decide) (by native_decide)
    have hAllToAll0_1 : pmFinal 2001 = allToAllPrimWithDims rankCount 1 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) 2001 = _
      rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2001], params := [1, 2] }] ++ (pmNodes.drop 3) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 1, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2001], params := [1, 2] } 2001 (fun t => allToAllPrimWithDims rankCount 1 (inputTids0.map t) 1 2)]
      · rw [hInputs0_1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph t 1 inputTids0 2001 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_1 : (pmFinal 2001).shape = [2, 9, 5] := by
      rw [hAllToAll0_1, allToAllPrimWithDims_shape rankCount 1 xs0 1 2 [2, 3, 15] hHead0 (by native_decide)]
      native_decide
    have hInputs0_2 : inputTids0.map (((pmNodes.take 4)).foldl
        (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 4) pmStore 1000 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 4) pmStore 1001 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 4) pmStore 1002 (by native_decide) (by native_decide)
    have hAllToAll0_2 : pmFinal 2002 = allToAllPrimWithDims rankCount 2 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) 2002 = _
      rw [show pmNodes = (pmNodes.take 4) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2002], params := [1, 2] }] ++ (pmNodes.drop 5) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
        { rank := 2, op := "OpName.AllToAllPrim", ins := [1000, 1001, 1002], outs := [2002], params := [1, 2] } 2002 (fun t => allToAllPrimWithDims rankCount 2 (inputTids0.map t) 1 2)]
      · rw [hInputs0_2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph t 2 inputTids0 2002 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_2 : (pmFinal 2002).shape = [2, 9, 5] := by
      rw [hAllToAll0_2, allToAllPrimWithDims_shape rankCount 2 xs0 1 2 [2, 3, 15] hHead0 (by native_decide)]
      native_decide
    have hOrdered0 : outputTids0.map pmFinal = List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 xs0 1 2) := by
      simp only [outputTids0, rankCount, List.map]
      rw [hAllToAll0_0, hAllToAll0_1, hAllToAll0_2]
      rfl
    have hGatherShape0 : (allGatherPrimDimN 1 rankCount 0 xs0).shape = [2, 9, 15] := by
      rw [hRankCountXs0, ← hin0.full_value]
      exact hin0.full_shape
    have hOdim0 : 2 < (allGatherPrimDimN 1 rankCount 0 xs0).shape.length := by rw [hGatherShape0]; native_decide
    have hDiv0 : (allGatherPrimDimN 1 rankCount 0 xs0).shape.getD 2 0 % rankCount = 0 := by rw [hGatherShape0]; native_decide
    have houtAllToAll0 : post_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 10) (outputTids0.map pmFinal) 2 [2, 9, 15] [2, 9, 5]
      refine {
        full_value := ?_
        full_shape := ?_
        shards_nonempty := by simp [outputTids0]
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp [outputTids0]
      }
      · change smStore _ = _
        rw [hOrdered0, List.length_ofFn, hRankCountXs0]
        rw [TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs0 (by simp [xs0, inputTids0]) hOdim0 hDiv0]
        exact hin0.full_value
      · exact hin0.full_shape
      · intro shard hmem
        simp only [outputTids0, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          exact hAllToAllShape0_0
        · subst shard
          exact hAllToAllShape0_1
        · subst shard
          exact hAllToAllShape0_2
    let inputTids1 : List Tid := [1100, 1101, 1102]
    let outputTids1 : List Tid := [2100, 2101, 2102]
    let xs1 := inputTids1.map pmStore
    have hRankCountXs1 : rankCount = xs1.length := by simp [pmTids, inputTids1, outputTids1, xs1, rankCount]
    have hin1 : pre_1.Holds smStore pmStore := hstate pre_1 (by native_decide)
    change ShardedRel (smStore 11) xs1 1 [2, 9, 15] [2, 3, 15] at hin1
    have hHead1 : ((xs1.head?.map (fun t => t.shape)).getD []) = [2, 3, 15] := by
      simp only [xs1, inputTids1, List.map, List.head?, Option.map, Option.getD]
      exact hin1.shard_shapes _ (by simp [xs1, inputTids1])
    have hInputs1_0 : inputTids1.map (((pmNodes.take 1)).foldl
        (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs1 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids1, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 1) pmStore 1100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 1) pmStore 1101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 1) pmStore 1102 (by native_decide) (by native_decide)
    have hAllToAll1_0 : pmFinal 2100 = allToAllPrimWithDims rankCount 0 xs1 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) 2100 = _
      rw [show pmNodes = (pmNodes.take 1) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2100], params := [1, 2] }] ++ (pmNodes.drop 2) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 0, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2100], params := [1, 2] } 2100 (fun t => allToAllPrimWithDims rankCount 0 (inputTids1.map t) 1 2)]
      · rw [hInputs1_0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids1] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph t 0 inputTids1 2100 1 2
      · native_decide
      · native_decide
    have hAllToAllShape1_0 : (pmFinal 2100).shape = [2, 9, 5] := by
      rw [hAllToAll1_0, allToAllPrimWithDims_shape rankCount 0 xs1 1 2 [2, 3, 15] hHead1 (by native_decide)]
      native_decide
    have hInputs1_1 : inputTids1.map (((pmNodes.take 3)).foldl
        (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs1 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids1, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 3) pmStore 1100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 3) pmStore 1101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 3) pmStore 1102 (by native_decide) (by native_decide)
    have hAllToAll1_1 : pmFinal 2101 = allToAllPrimWithDims rankCount 1 xs1 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) 2101 = _
      rw [show pmNodes = (pmNodes.take 3) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2101], params := [1, 2] }] ++ (pmNodes.drop 4) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 1, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2101], params := [1, 2] } 2101 (fun t => allToAllPrimWithDims rankCount 1 (inputTids1.map t) 1 2)]
      · rw [hInputs1_1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids1] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph t 1 inputTids1 2101 1 2
      · native_decide
      · native_decide
    have hAllToAllShape1_1 : (pmFinal 2101).shape = [2, 9, 5] := by
      rw [hAllToAll1_1, allToAllPrimWithDims_shape rankCount 1 xs1 1 2 [2, 3, 15] hHead1 (by native_decide)]
      native_decide
    have hInputs1_2 : inputTids1.map (((pmNodes.take 5)).foldl
        (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs1 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids1, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 5) pmStore 1100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 5) pmStore 1101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph
          (pmNodes.take 5) pmStore 1102 (by native_decide) (by native_decide)
    have hAllToAll1_2 : pmFinal 2102 = allToAllPrimWithDims rankCount 2 xs1 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph) pmStore) 2102 = _
      rw [show pmNodes = (pmNodes.take 5) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2102], params := [1, 2] }] ++ (pmNodes.drop 6) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 5) (pmNodes.drop 6)
        { rank := 2, op := "OpName.AllToAllPrim", ins := [1100, 1101, 1102], outs := [2102], params := [1, 2] } 2102 (fun t => allToAllPrimWithDims rankCount 2 (inputTids1.map t) 1 2)]
      · rw [hInputs1_2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids1] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness.pmGraph t 2 inputTids1 2102 1 2
      · native_decide
      · native_decide
    have hAllToAllShape1_2 : (pmFinal 2102).shape = [2, 9, 5] := by
      rw [hAllToAll1_2, allToAllPrimWithDims_shape rankCount 2 xs1 1 2 [2, 3, 15] hHead1 (by native_decide)]
      native_decide
    have hOrdered1 : outputTids1.map pmFinal = List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 xs1 1 2) := by
      simp only [outputTids1, rankCount, List.map]
      rw [hAllToAll1_0, hAllToAll1_1, hAllToAll1_2]
      rfl
    have hGatherShape1 : (allGatherPrimDimN 1 rankCount 0 xs1).shape = [2, 9, 15] := by
      rw [hRankCountXs1, ← hin1.full_value]
      exact hin1.full_shape
    have hOdim1 : 2 < (allGatherPrimDimN 1 rankCount 0 xs1).shape.length := by rw [hGatherShape1]; native_decide
    have hDiv1 : (allGatherPrimDimN 1 rankCount 0 xs1).shape.getD 2 0 % rankCount = 0 := by rw [hGatherShape1]; native_decide
    have houtAllToAll1 : post_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 11) (outputTids1.map pmFinal) 2 [2, 9, 15] [2, 9, 5]
      refine {
        full_value := ?_
        full_shape := ?_
        shards_nonempty := by simp [outputTids1]
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp [outputTids1]
      }
      · change smStore _ = _
        rw [hOrdered1, List.length_ofFn, hRankCountXs1]
        rw [TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs1 (by simp [xs1, inputTids1]) hOdim1 hDiv1]
        exact hin1.full_value
      · exact hin1.full_shape
      · intro shard hmem
        simp only [outputTids1, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          exact hAllToAllShape1_0
        · subst shard
          exact hAllToAllShape1_1
        · subst shard
          exact hAllToAllShape1_2
    intro fact hfact
    have covered : fact ∈ [post_0, post_1] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [post_0, post_1] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with new | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
      rcases new with h0 | h1
      · subst fact
        exact houtAllToAll0
      · subst fact
        exact houtAllToAll1
    · exact hframe fact old

#print axioms segment_generic
end
end TrainVerify.Denote.GeneratedKRankAllToAllTupleAtomicWitness
