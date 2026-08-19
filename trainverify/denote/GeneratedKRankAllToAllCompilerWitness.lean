/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SyntheticKRank

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_pre : RelationFact :=
  .sharded 10 [20, 21, 22, 23] 0 [8, 4] [2, 4]

private def fact_post : RelationFact :=
  .sharded 10 [30, 31, 32, 33] 1 [8, 4] [8, 1]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_pre : RelationState where
  facts := [anchor, fact_pre]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, fact_post]
  nonempty := by decide

end
end TrainVerify.Denote.SyntheticKRank

namespace TrainVerify.Denote.SyntheticKRank
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [] }
private def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [30], params := [0, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [31], params := [0, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [32], params := [0, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [33], params := [0, 1] }] }
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticKRank.smGraph SyntheticKRank.pmGraph state_pre state_post where
  smNodes := []
  pmNodes := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [30], params := [0, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [31], params := [0, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [32], params := [0, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [33], params := [0, 1] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := []
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [30], params := [0, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [31], params := [0, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [32], params := [0, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [33], params := [0, 1] }]
    let pmTids : List Tid := [30, 31, 32, 33]
    let rankCount := pmTids.length
    have hRankCount : rankCount = SyntheticKRank.pmGraph.numRanks := by rfl
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    let inputTids0 : List Tid := [20, 21, 22, 23]
    let outputTids0 : List Tid := [30, 31, 32, 33]
    let xs0 := inputTids0.map pmStore
    have hRankCountXs0 : rankCount = xs0.length := by simp [pmTids, inputTids0, outputTids0, xs0, rankCount]
    have hin0 : fact_pre.Holds smStore pmStore := hstate fact_pre (by native_decide)
    change ShardedRel (smStore 10) xs0 0 [8, 4] [2, 4] at hin0
    have hHead0 : ((xs0.head?.map (fun t => t.shape)).getD []) = [2, 4] := by
      simp only [xs0, inputTids0, List.map, List.head?, Option.map, Option.getD]
      exact hin0.shard_shapes _ (by simp [xs0, inputTids0])
    have hInputs0_0 : inputTids0.map (((pmNodes.take 0)).foldl
        (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 0) pmStore 20 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 0) pmStore 21 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 0) pmStore 22 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 0) pmStore 23 (by native_decide) (by native_decide)
    have hAllToAll0_0 : pmFinal 30 = allToAllPrimWithDims rankCount 0 xs0 0 1 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 30 = _
      rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [30], params := [0, 1] }] ++ (pmNodes.drop 1) by native_decide]
      rw [foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [30], params := [0, 1] } 30 (fun t => allToAllPrimWithDims rankCount 0 (inputTids0.map t) 0 1)]
      · rw [hInputs0_0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out SyntheticKRank.pmGraph t 0 inputTids0 30 0 1
      · native_decide
      · native_decide
    have hAllToAllShape0_0 : (pmFinal 30).shape = [8, 1] := by
      rw [hAllToAll0_0, allToAllPrimWithDims_shape rankCount 0 xs0 0 1 [2, 4] hHead0 (by native_decide)]
      native_decide
    have hInputs0_1 : inputTids0.map (((pmNodes.take 1)).foldl
        (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 1) pmStore 20 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 1) pmStore 21 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 1) pmStore 22 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 1) pmStore 23 (by native_decide) (by native_decide)
    have hAllToAll0_1 : pmFinal 31 = allToAllPrimWithDims rankCount 1 xs0 0 1 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 31 = _
      rw [show pmNodes = (pmNodes.take 1) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [31], params := [0, 1] }] ++ (pmNodes.drop 2) by native_decide]
      rw [foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 1, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [31], params := [0, 1] } 31 (fun t => allToAllPrimWithDims rankCount 1 (inputTids0.map t) 0 1)]
      · rw [hInputs0_1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out SyntheticKRank.pmGraph t 1 inputTids0 31 0 1
      · native_decide
      · native_decide
    have hAllToAllShape0_1 : (pmFinal 31).shape = [8, 1] := by
      rw [hAllToAll0_1, allToAllPrimWithDims_shape rankCount 1 xs0 0 1 [2, 4] hHead0 (by native_decide)]
      native_decide
    have hInputs0_2 : inputTids0.map (((pmNodes.take 2)).foldl
        (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 2) pmStore 20 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 2) pmStore 21 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 2) pmStore 22 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 2) pmStore 23 (by native_decide) (by native_decide)
    have hAllToAll0_2 : pmFinal 32 = allToAllPrimWithDims rankCount 2 xs0 0 1 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 32 = _
      rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [32], params := [0, 1] }] ++ (pmNodes.drop 3) by native_decide]
      rw [foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 2, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [32], params := [0, 1] } 32 (fun t => allToAllPrimWithDims rankCount 2 (inputTids0.map t) 0 1)]
      · rw [hInputs0_2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out SyntheticKRank.pmGraph t 2 inputTids0 32 0 1
      · native_decide
      · native_decide
    have hAllToAllShape0_2 : (pmFinal 32).shape = [8, 1] := by
      rw [hAllToAll0_2, allToAllPrimWithDims_shape rankCount 2 xs0 0 1 [2, 4] hHead0 (by native_decide)]
      native_decide
    have hInputs0_3 : inputTids0.map (((pmNodes.take 3)).foldl
        (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 3) pmStore 20 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 3) pmStore 21 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 3) pmStore 22 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
          (pmNodes.take 3) pmStore 23 (by native_decide) (by native_decide)
    have hAllToAll0_3 : pmFinal 33 = allToAllPrimWithDims rankCount 3 xs0 0 1 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 33 = _
      rw [show pmNodes = (pmNodes.take 3) ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [33], params := [0, 1] }] ++ (pmNodes.drop 4) by native_decide]
      rw [foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 3, op := "OpName.AllToAllPrim", ins := [20, 21, 22, 23], outs := [33], params := [0, 1] } 33 (fun t => allToAllPrimWithDims rankCount 3 (inputTids0.map t) 0 1)]
      · rw [hInputs0_3]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out SyntheticKRank.pmGraph t 3 inputTids0 33 0 1
      · native_decide
      · native_decide
    have hAllToAllShape0_3 : (pmFinal 33).shape = [8, 1] := by
      rw [hAllToAll0_3, allToAllPrimWithDims_shape rankCount 3 xs0 0 1 [2, 4] hHead0 (by native_decide)]
      native_decide
    have hOrdered0 : outputTids0.map pmFinal = List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 xs0 0 1) := by
      simp only [outputTids0, rankCount, List.map]
      rw [hAllToAll0_0, hAllToAll0_1, hAllToAll0_2, hAllToAll0_3]
      rfl
    have hGatherShape0 : (allGatherPrimDimN 0 rankCount 0 xs0).shape = [8, 4] := by
      rw [hRankCountXs0, ← hin0.full_value]
      exact hin0.full_shape
    have hOdim0 : 1 < (allGatherPrimDimN 0 rankCount 0 xs0).shape.length := by rw [hGatherShape0]; native_decide
    have hDiv0 : (allGatherPrimDimN 0 rankCount 0 xs0).shape.getD 1 0 % rankCount = 0 := by rw [hGatherShape0]; native_decide
    have houtAllToAll0 : fact_post.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 10) (outputTids0.map pmFinal) 1 [8, 4] [8, 1]
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
        rw [TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 0 1 xs0 (by simp [xs0, inputTids0]) hOdim0 hDiv0]
        exact hin0.full_value
      · exact hin0.full_shape
      · intro shard hmem
        simp only [outputTids0, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst shard
          exact hAllToAllShape0_0
        · subst shard
          exact hAllToAllShape0_1
        · subst shard
          exact hAllToAllShape0_2
        · subst shard
          exact hAllToAllShape0_3
    intro fact hfact
    have covered : fact ∈ [fact_post] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_post] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with new | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
      rcases new with h0
      · subst fact
        exact houtAllToAll0
    · exact hframe fact old

#print axioms segment_000000
end
end TrainVerify.Denote.SyntheticKRank
