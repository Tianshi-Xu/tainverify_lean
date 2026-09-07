import denote.RelationCompiler
import denote.KRankAllToAll
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace AllToAllReduceScatter
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [300], params := [1, 2] }, { rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [301], params := [1, 2] }, { rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [302], params := [1, 2] }, { rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [303], params := [1, 2] }, { rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] }] }
def a_in : RelationFact := .sharded 10 [100, 101, 102, 103] 1 [2, 12, 20] [2, 3, 20]
def a_out : RelationFact := .sharded 10 [300, 301, 302, 303] 2 [2, 12, 20] [2, 12, 5]
def r_in : RelationFact := .reduction 20 [200, 201, 202, 203] [2, 12, 20]
def r_out : RelationFact := .sharded 20 [400, 401, 402, 403] 2 [2, 12, 20] [2, 12, 5]
def before : RelationState where
  facts := [a_in, r_in]
  nonempty := by decide
def after : RelationState where
  facts := [a_out, r_out]
  nonempty := by decide
private def segment_000000 :
    ClosedDepSegmentCertificate AllToAllReduceScatter.smGraph AllToAllReduceScatter.pmGraph before after where
  smNodes := []
  pmNodes := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [300], params := [1, 2] }, { rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [301], params := [1, 2] }, { rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [302], params := [1, 2] }, { rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [303], params := [1, 2] }, { rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := []
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [300], params := [1, 2] }, { rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [301], params := [1, 2] }, { rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [302], params := [1, 2] }, { rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [303], params := [1, 2] }, { rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] }]
    let pmTids : List Tid := [300, 301, 302, 303]
    let rankCount := pmTids.length
    have hRankCount : rankCount = AllToAllReduceScatter.pmGraph.numRanks := by rfl
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore
    have hframe : before.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    let inputTids0 : List Tid := [100, 101, 102, 103]
    let outputTids0 : List Tid := [300, 301, 302, 303]
    let xs0 := inputTids0.map pmStore
    have hRankCountXs0 : rankCount = xs0.length := by simp [pmTids, inputTids0, outputTids0, xs0, rankCount]
    have hin0 : a_in.Holds smStore pmStore := hstate a_in (by native_decide)
    change ShardedRel (smStore 10) xs0 1 [2, 12, 20] [2, 3, 20] at hin0
    have hHead0 : ((xs0.head?.map (fun t => t.shape)).getD []) = [2, 3, 20] := by
      simp only [xs0, inputTids0, List.map, List.head?, Option.map, Option.getD]
      exact hin0.shard_shapes _ (by simp [xs0, inputTids0])
    have hInputs0_0 : inputTids0.map (((pmNodes.take 0)).foldl
        (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 0) pmStore 100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 0) pmStore 101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 0) pmStore 102 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 0) pmStore 103 (by native_decide) (by native_decide)
    have hAllToAll0_0 : pmFinal 300 = allToAllPrimWithDims rankCount 0 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) 300 = _
      rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [300], params := [1, 2] }] ++ (pmNodes.drop 1) by native_decide]
      rw [foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [300], params := [1, 2] } 300 (fun t => allToAllPrimWithDims rankCount 0 (inputTids0.map t) 1 2)]
      · rw [hInputs0_0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out AllToAllReduceScatter.pmGraph t 0 inputTids0 300 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_0 : (pmFinal 300).shape = [2, 12, 5] := by
      rw [hAllToAll0_0, allToAllPrimWithDims_shape rankCount 0 xs0 1 2 [2, 3, 20] hHead0 (by native_decide)]
      native_decide
    have hInputs0_1 : inputTids0.map (((pmNodes.take 2)).foldl
        (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 2) pmStore 100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 2) pmStore 101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 2) pmStore 102 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 2) pmStore 103 (by native_decide) (by native_decide)
    have hAllToAll0_1 : pmFinal 301 = allToAllPrimWithDims rankCount 1 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) 301 = _
      rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [301], params := [1, 2] }] ++ (pmNodes.drop 3) by native_decide]
      rw [foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 1, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [301], params := [1, 2] } 301 (fun t => allToAllPrimWithDims rankCount 1 (inputTids0.map t) 1 2)]
      · rw [hInputs0_1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out AllToAllReduceScatter.pmGraph t 1 inputTids0 301 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_1 : (pmFinal 301).shape = [2, 12, 5] := by
      rw [hAllToAll0_1, allToAllPrimWithDims_shape rankCount 1 xs0 1 2 [2, 3, 20] hHead0 (by native_decide)]
      native_decide
    have hInputs0_2 : inputTids0.map (((pmNodes.take 4)).foldl
        (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 4) pmStore 100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 4) pmStore 101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 4) pmStore 102 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 4) pmStore 103 (by native_decide) (by native_decide)
    have hAllToAll0_2 : pmFinal 302 = allToAllPrimWithDims rankCount 2 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) 302 = _
      rw [show pmNodes = (pmNodes.take 4) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [302], params := [1, 2] }] ++ (pmNodes.drop 5) by native_decide]
      rw [foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
        { rank := 2, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [302], params := [1, 2] } 302 (fun t => allToAllPrimWithDims rankCount 2 (inputTids0.map t) 1 2)]
      · rw [hInputs0_2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out AllToAllReduceScatter.pmGraph t 2 inputTids0 302 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_2 : (pmFinal 302).shape = [2, 12, 5] := by
      rw [hAllToAll0_2, allToAllPrimWithDims_shape rankCount 2 xs0 1 2 [2, 3, 20] hHead0 (by native_decide)]
      native_decide
    have hInputs0_3 : inputTids0.map (((pmNodes.take 6)).foldl
        (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) = xs0 := by
      apply List.map_congr_left
      intro tid htid
      simp only [inputTids0, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2 | h3
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 6) pmStore 100 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 6) pmStore 101 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 6) pmStore 102 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written AllToAllReduceScatter.pmGraph
          (pmNodes.take 6) pmStore 103 (by native_decide) (by native_decide)
    have hAllToAll0_3 : pmFinal 303 = allToAllPrimWithDims rankCount 3 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore) 303 = _
      rw [show pmNodes = (pmNodes.take 6) ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [303], params := [1, 2] }] ++ (pmNodes.drop 7) by native_decide]
      rw [foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore (pmNodes.take 6) (pmNodes.drop 7)
        { rank := 3, op := "OpName.AllToAllPrim", ins := [100, 101, 102, 103], outs := [303], params := [1, 2] } 303 (fun t => allToAllPrimWithDims rankCount 3 (inputTids0.map t) 1 2)]
      · rw [hInputs0_3]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out AllToAllReduceScatter.pmGraph t 3 inputTids0 303 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0_3 : (pmFinal 303).shape = [2, 12, 5] := by
      rw [hAllToAll0_3, allToAllPrimWithDims_shape rankCount 3 xs0 1 2 [2, 3, 20] hHead0 (by native_decide)]
      native_decide
    have hOrdered0 : outputTids0.map pmFinal = List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 xs0 1 2) := by
      simp only [outputTids0, rankCount, List.map]
      rw [hAllToAll0_0, hAllToAll0_1, hAllToAll0_2, hAllToAll0_3]
      rfl
    have hGatherShape0 : (allGatherPrimDimN 1 rankCount 0 xs0).shape = [2, 12, 20] := by
      rw [hRankCountXs0, ← hin0.full_value]
      exact hin0.full_shape
    have hOdim0 : 2 < (allGatherPrimDimN 1 rankCount 0 xs0).shape.length := by rw [hGatherShape0]; native_decide
    have hDiv0 : (allGatherPrimDimN 1 rankCount 0 xs0).shape.getD 2 0 % rankCount = 0 := by rw [hGatherShape0]; native_decide
    have houtAllToAll0 : a_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 10) (outputTids0.map pmFinal) 2 [2, 12, 20] [2, 12, 5]
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
        rcases hmem with h0 | h1 | h2 | h3
        · subst shard
          exact hAllToAllShape0_0
        · subst shard
          exact hAllToAllShape0_1
        · subst shard
          exact hAllToAllShape0_2
        · subst shard
          exact hAllToAllShape0_3
    have hfinal : pmFinal = pmNodes.foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore := rfl
    have hred : r_in.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ReductionRel (smStore 20) [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] [2, 12, 20] at hred
    have hw0_nodes : pmNodes = (pmNodes.take 1) ++ [{ rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] }] ++ (pmNodes.drop 2) := by
      native_decide
    have hw0_prefix : pmFinal 400 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 0 [((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := by
      rw [hfinal, hw0_nodes]
      exact foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] } 400
        (fun t => reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 0 [t 200, t 201, t 202, t 203]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_reduceScatterPrim_out AllToAllReduceScatter.pmGraph t 0 2 [200, 201, 202, 203] 400
        ) (by native_decide) (by native_decide)
    have hw0_read_0 : ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200 = pmFinal 200 := by
      rw [hfinal, hw0_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 1) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] } :: (pmNodes.drop 2)) 200
        (by native_decide) (by native_decide)
    have hw0_read_1 : ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201 = pmFinal 201 := by
      rw [hfinal, hw0_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 1) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] } :: (pmNodes.drop 2)) 201
        (by native_decide) (by native_decide)
    have hw0_read_2 : ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202 = pmFinal 202 := by
      rw [hfinal, hw0_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 1) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] } :: (pmNodes.drop 2)) 202
        (by native_decide) (by native_decide)
    have hw0_read_3 : ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203 = pmFinal 203 := by
      rw [hfinal, hw0_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 1) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [400], params := [2] } :: (pmNodes.drop 2)) 203
        (by native_decide) (by native_decide)
    have hw0 : pmFinal 400 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 0 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by
      calc
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 0 [((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 1)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := hw0_prefix
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 0 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by rw [hw0_read_0, hw0_read_1, hw0_read_2, hw0_read_3]
    change pmFinal 400 = reduceScatterPrimDimN 2 4 0 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] at hw0
    have hredValue0 : smStore 20 = allReducePrim 4 0 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc0 : pmFinal 400 = chunkPrimDimN 2 4 0 (smStore 20) := by rw [hw0]; unfold reduceScatterPrimDimN; rw [← hredValue0]
    have hw1_nodes : pmNodes = (pmNodes.take 3) ++ [{ rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] }] ++ (pmNodes.drop 4) := by
      native_decide
    have hw1_prefix : pmFinal 401 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 1 [((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := by
      rw [hfinal, hw1_nodes]
      exact foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] } 401
        (fun t => reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 1 [t 200, t 201, t 202, t 203]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_reduceScatterPrim_out AllToAllReduceScatter.pmGraph t 1 2 [200, 201, 202, 203] 401
        ) (by native_decide) (by native_decide)
    have hw1_read_0 : ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200 = pmFinal 200 := by
      rw [hfinal, hw1_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] } :: (pmNodes.drop 4)) 200
        (by native_decide) (by native_decide)
    have hw1_read_1 : ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201 = pmFinal 201 := by
      rw [hfinal, hw1_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] } :: (pmNodes.drop 4)) 201
        (by native_decide) (by native_decide)
    have hw1_read_2 : ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202 = pmFinal 202 := by
      rw [hfinal, hw1_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] } :: (pmNodes.drop 4)) 202
        (by native_decide) (by native_decide)
    have hw1_read_3 : ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203 = pmFinal 203 := by
      rw [hfinal, hw1_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [401], params := [2] } :: (pmNodes.drop 4)) 203
        (by native_decide) (by native_decide)
    have hw1 : pmFinal 401 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 1 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by
      calc
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 1 [((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 3)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := hw1_prefix
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 1 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by rw [hw1_read_0, hw1_read_1, hw1_read_2, hw1_read_3]
    change pmFinal 401 = reduceScatterPrimDimN 2 4 1 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] at hw1
    have hredValue1 : smStore 20 = allReducePrim 4 1 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc1 : pmFinal 401 = chunkPrimDimN 2 4 1 (smStore 20) := by rw [hw1]; unfold reduceScatterPrimDimN; rw [← hredValue1]
    have hw2_nodes : pmNodes = (pmNodes.take 5) ++ [{ rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] }] ++ (pmNodes.drop 6) := by
      native_decide
    have hw2_prefix : pmFinal 402 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 2 [((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := by
      rw [hfinal, hw2_nodes]
      exact foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 5) (pmNodes.drop 6)
        { rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] } 402
        (fun t => reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 2 [t 200, t 201, t 202, t 203]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_reduceScatterPrim_out AllToAllReduceScatter.pmGraph t 2 2 [200, 201, 202, 203] 402
        ) (by native_decide) (by native_decide)
    have hw2_read_0 : ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200 = pmFinal 200 := by
      rw [hfinal, hw2_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 5) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] } :: (pmNodes.drop 6)) 200
        (by native_decide) (by native_decide)
    have hw2_read_1 : ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201 = pmFinal 201 := by
      rw [hfinal, hw2_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 5) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] } :: (pmNodes.drop 6)) 201
        (by native_decide) (by native_decide)
    have hw2_read_2 : ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202 = pmFinal 202 := by
      rw [hfinal, hw2_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 5) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] } :: (pmNodes.drop 6)) 202
        (by native_decide) (by native_decide)
    have hw2_read_3 : ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203 = pmFinal 203 := by
      rw [hfinal, hw2_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 5) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [402], params := [2] } :: (pmNodes.drop 6)) 203
        (by native_decide) (by native_decide)
    have hw2 : pmFinal 402 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 2 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by
      calc
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 2 [((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 5)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := hw2_prefix
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 2 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by rw [hw2_read_0, hw2_read_1, hw2_read_2, hw2_read_3]
    change pmFinal 402 = reduceScatterPrimDimN 2 4 2 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] at hw2
    have hredValue2 : smStore 20 = allReducePrim 4 2 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc2 : pmFinal 402 = chunkPrimDimN 2 4 2 (smStore 20) := by rw [hw2]; unfold reduceScatterPrimDimN; rw [← hredValue2]
    have hw3_nodes : pmNodes = (pmNodes.take 7) ++ [{ rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] }] ++ (pmNodes.drop 8) := by
      native_decide
    have hw3_prefix : pmFinal 403 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 3 [((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := by
      rw [hfinal, hw3_nodes]
      exact foldl_faithful_middle_writer AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 7) (pmNodes.drop 8)
        { rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] } 403
        (fun t => reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 3 [t 200, t 201, t 202, t 203]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_reduceScatterPrim_out AllToAllReduceScatter.pmGraph t 3 2 [200, 201, 202, 203] 403
        ) (by native_decide) (by native_decide)
    have hw3_read_0 : ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200 = pmFinal 200 := by
      rw [hfinal, hw3_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 7) ({ rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] } :: (pmNodes.drop 8)) 200
        (by native_decide) (by native_decide)
    have hw3_read_1 : ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201 = pmFinal 201 := by
      rw [hfinal, hw3_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 7) ({ rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] } :: (pmNodes.drop 8)) 201
        (by native_decide) (by native_decide)
    have hw3_read_2 : ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202 = pmFinal 202 := by
      rw [hfinal, hw3_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 7) ({ rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] } :: (pmNodes.drop 8)) 202
        (by native_decide) (by native_decide)
    have hw3_read_3 : ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203 = pmFinal 203 := by
      rw [hfinal, hw3_nodes]
      exact foldl_faithful_prefix_read_eq_final AllToAllReduceScatter.pmGraph pmStore
        (pmNodes.take 7) ({ rank := 3, op := "OpName.ReduceScatterPrim", ins := [200, 201, 202, 203], outs := [403], params := [2] } :: (pmNodes.drop 8)) 203
        (by native_decide) (by native_decide)
    have hw3 : pmFinal 403 = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 3 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by
      calc
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 3 [((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 200, ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 201, ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 202, ((pmNodes.take 7)).foldl (applyNodeDistributedFaithful AllToAllReduceScatter.pmGraph) pmStore 203] := hw3_prefix
        _ = reduceScatterPrimDimN 2 AllToAllReduceScatter.pmGraph.numRanks 3 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by rw [hw3_read_0, hw3_read_1, hw3_read_2, hw3_read_3]
    change pmFinal 403 = reduceScatterPrimDimN 2 4 3 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] at hw3
    have hredValue3 : smStore 20 = allReducePrim 4 3 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc3 : pmFinal 403 = chunkPrimDimN 2 4 3 (smStore 20) := by rw [hw3]; unfold reduceScatterPrimDimN; rw [← hredValue3]
    have hordered : [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403] = List.ofFn (fun r : Fin 4 => chunkPrimDimN 2 4 r.1 (smStore 20)) := by
      change [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403] = [chunkPrimDimN 2 4 0 (smStore 20), chunkPrimDimN 2 4 1 (smStore 20), chunkPrimDimN 2 4 2 (smStore 20), chunkPrimDimN 2 4 3 (smStore 20)]
      rw [hc0, hc1, hc2, hc3]
    have hvalue : smStore 20 = allGatherPrimDimN 2 [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403].length 0 [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403] := by
      rw [hordered]
      simp only [List.length_ofFn]
      symm
      exact allGatherPrimDimN_chunks_ofFn 2 4 (smStore 20) (by omega) (by rw [hred.full_shape]; native_decide) (by rw [hred.full_shape]; native_decide)
    have hs0 : (pmFinal 400).shape = [2, 12, 5] := by
      rw [hc0, chunkPrimDimN_shape 2 4 0 (smStore 20) [2, 12, 20] hred.full_shape (by omega)]
      native_decide
    have hs1 : (pmFinal 401).shape = [2, 12, 5] := by
      rw [hc1, chunkPrimDimN_shape 2 4 1 (smStore 20) [2, 12, 20] hred.full_shape (by omega)]
      native_decide
    have hs2 : (pmFinal 402).shape = [2, 12, 5] := by
      rw [hc2, chunkPrimDimN_shape 2 4 2 (smStore 20) [2, 12, 20] hred.full_shape (by omega)]
      native_decide
    have hs3 : (pmFinal 403).shape = [2, 12, 5] := by
      rw [hc3, chunkPrimDimN_shape 2 4 3 (smStore 20) [2, 12, 20] hred.full_shape (by omega)]
      native_decide
    have hout : r_out.Holds smStore pmFinal := by
      change ShardedRel (smStore 20) [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403] 2 [2, 12, 20] [2, 12, 5]
      refine { full_value := hvalue, full_shape := hred.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl   | rfl   | rfl   | rfl
      · exact hs0
      · exact hs1
      · exact hs2
      · exact hs3
    intro fact hfact
    have covered : fact ∈ [a_out, r_out] ++ before.facts := by
      exact (show after.facts ⊆ [a_out, r_out] ++ before.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with new | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
      rcases new with h0 | h1
      · subst fact
        exact houtAllToAll0
      · subst fact
        exact hout
    · exact hframe fact old

#print axioms segment_000000
end
end AllToAllReduceScatter
