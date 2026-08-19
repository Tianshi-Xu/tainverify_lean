/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SyntheticKRank

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_pre : RelationFact :=
  .joined 10 20 [2, 8]

private def fact_post : RelationFact :=
  .sharded 10 [30, 31, 32, 33] 1 [2, 8] [2, 2]

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
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [1], outs := [10] }] }
private def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [2], outs := [20] }, { rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [30], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [31], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [32], params := [1] }, { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [33], params := [1] }] }
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticKRank.smGraph SyntheticKRank.pmGraph state_pre state_post where
  smNodes := []
  pmNodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [30], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [31], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [32], params := [1] }, { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [33], params := [1] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := []
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [30], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [31], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [32], params := [1] }, { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [33], params := [1] }]
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
    have hin : fact_pre.Holds smStore pmStore := hstate fact_pre (by native_decide)
    change smStore 10 = pmStore 20 ∧
      (smStore 10).shape = [2, 8] ∧
      (pmStore 20).shape = [2, 8] at hin
    have hChunk0 : pmFinal 30 =
        chunkPrimDimN 1 rankCount 0 (pmStore 20) := by
      calc
        pmFinal 30 = chunkPrimDimN 1 rankCount 0
            (((pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 20) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 30 = _
          rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [30], params := [1] }] ++ (pmNodes.drop 1) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
            { rank := 0, op := "OpName.ChunkPrim", ins := [20], outs := [30], params := [1] } 30
            (fun t => chunkPrimDimN 1 rankCount 0 (t 20))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
            rw [hRankCount]
            simpa using applyNode_chunkPrimDimN_out SyntheticKRank.pmGraph t 0 20 30 1
          · native_decide
          · native_decide
        _ = chunkPrimDimN 1 rankCount 0 (pmStore 20) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 0) pmStore 20 (by native_decide) (by native_decide)]
    have hChunkShape0 : (pmFinal 30).shape = [2, 2] := by
      rw [hChunk0, chunkPrimDimN_shape 1 rankCount 0 (pmStore 20)
        [2, 8] hin.2.2 (by native_decide)]
      native_decide
    have hChunk1 : pmFinal 31 =
        chunkPrimDimN 1 rankCount 1 (pmStore 20) := by
      calc
        pmFinal 31 = chunkPrimDimN 1 rankCount 1
            (((pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 20) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 31 = _
          rw [show pmNodes = (pmNodes.take 1) ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [31], params := [1] }] ++ (pmNodes.drop 2) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
            { rank := 1, op := "OpName.ChunkPrim", ins := [20], outs := [31], params := [1] } 31
            (fun t => chunkPrimDimN 1 rankCount 1 (t 20))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
            rw [hRankCount]
            simpa using applyNode_chunkPrimDimN_out SyntheticKRank.pmGraph t 1 20 31 1
          · native_decide
          · native_decide
        _ = chunkPrimDimN 1 rankCount 1 (pmStore 20) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 1) pmStore 20 (by native_decide) (by native_decide)]
    have hChunkShape1 : (pmFinal 31).shape = [2, 2] := by
      rw [hChunk1, chunkPrimDimN_shape 1 rankCount 1 (pmStore 20)
        [2, 8] hin.2.2 (by native_decide)]
      native_decide
    have hChunk2 : pmFinal 32 =
        chunkPrimDimN 1 rankCount 2 (pmStore 20) := by
      calc
        pmFinal 32 = chunkPrimDimN 1 rankCount 2
            (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 20) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 32 = _
          rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [32], params := [1] }] ++ (pmNodes.drop 3) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
            { rank := 2, op := "OpName.ChunkPrim", ins := [20], outs := [32], params := [1] } 32
            (fun t => chunkPrimDimN 1 rankCount 2 (t 20))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
            rw [hRankCount]
            simpa using applyNode_chunkPrimDimN_out SyntheticKRank.pmGraph t 2 20 32 1
          · native_decide
          · native_decide
        _ = chunkPrimDimN 1 rankCount 2 (pmStore 20) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 2) pmStore 20 (by native_decide) (by native_decide)]
    have hChunkShape2 : (pmFinal 32).shape = [2, 2] := by
      rw [hChunk2, chunkPrimDimN_shape 1 rankCount 2 (pmStore 20)
        [2, 8] hin.2.2 (by native_decide)]
      native_decide
    have hChunk3 : pmFinal 33 =
        chunkPrimDimN 1 rankCount 3 (pmStore 20) := by
      calc
        pmFinal 33 = chunkPrimDimN 1 rankCount 3
            (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 20) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 33 = _
          rw [show pmNodes = (pmNodes.take 3) ++ [{ rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [33], params := [1] }] ++ (pmNodes.drop 4) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
            { rank := 3, op := "OpName.ChunkPrim", ins := [20], outs := [33], params := [1] } 33
            (fun t => chunkPrimDimN 1 rankCount 3 (t 20))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
            rw [hRankCount]
            simpa using applyNode_chunkPrimDimN_out SyntheticKRank.pmGraph t 3 20 33 1
          · native_decide
          · native_decide
        _ = chunkPrimDimN 1 rankCount 3 (pmStore 20) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 3) pmStore 20 (by native_decide) (by native_decide)]
    have hChunkShape3 : (pmFinal 33).shape = [2, 2] := by
      rw [hChunk3, chunkPrimDimN_shape 1 rankCount 3 (pmStore 20)
        [2, 8] hin.2.2 (by native_decide)]
      native_decide
    have hOrderedChunks : pmTids.map pmFinal =
        List.ofFn (fun r : Fin rankCount => chunkPrimDimN 1 rankCount r.1 (pmStore 20)) := by
      simp only [pmTids, rankCount, List.map]
      rw [hChunk0, hChunk1, hChunk2, hChunk3]
      rfl
    have hout : fact_post.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 10) (pmTids.map pmFinal) 1 [2, 8] [2, 2]
      refine {
        full_value := ?_
        full_shape := ?_
        shards_nonempty := by simp [pmTids]
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp [pmTids]
      }
      · change smStore _ = _
        rw [hOrderedChunks, List.length_ofFn]
        rw [TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn 1 rankCount (pmStore 20)
          (by native_decide) (by rw [hin.2.2]; native_decide)
          (by simp only [rankCount, pmTids, List.length_cons, List.length_nil]; rw [hin.2.2]; native_decide)]
        exact hin.1
      · exact hin.2.1
      · intro shard hmem
        simp only [pmTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst shard
          exact hChunkShape0
        · subst shard
          exact hChunkShape1
        · subst shard
          exact hChunkShape2
        · subst shard
          exact hChunkShape3
    exact RelationState.Holds.mono_insert hframe hout (by native_decide)

#print axioms segment_000000
end
end TrainVerify.Denote.SyntheticKRank
