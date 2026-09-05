/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SyntheticKRank

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_pre : RelationFact :=
  .sharded 10 [20, 21, 22, 23] 1 [1, 8, 3] [1, 2, 3]

private def fact_post : RelationFact :=
  .reduction 11 [30, 31, 32, 33] [1]

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
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [1], outs := [10] }, { rank := 0, op := "OpName.FW_identity", ins := [700], outs := [701] }, { rank := 0, op := "OpName.FW_sum", ins := [10], outs := [11] }, { rank := 0, op := "OpName.FW_identity", ins := [702], outs := [703] }, { rank := 0, op := "OpName.FW_identity", ins := [704], outs := [705] }] }
private def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [2], outs := [20] }, { rank := 1, op := "OpName.FW_identity", ins := [3], outs := [21] }, { rank := 2, op := "OpName.FW_identity", ins := [4], outs := [22] }, { rank := 3, op := "OpName.FW_identity", ins := [5], outs := [23] }, { rank := 0, op := "OpName.FW_sum", ins := [20], outs := [30] }, { rank := 0, op := "OpName.FW_identity", ins := [800], outs := [900] }, { rank := 1, op := "OpName.FW_sum", ins := [21], outs := [31] }, { rank := 1, op := "OpName.FW_identity", ins := [801], outs := [901] }, { rank := 2, op := "OpName.FW_sum", ins := [22], outs := [32] }, { rank := 2, op := "OpName.FW_identity", ins := [802], outs := [902] }, { rank := 3, op := "OpName.FW_sum", ins := [23], outs := [33] }] }
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticKRank.smGraph SyntheticKRank.pmGraph state_pre state_post where
  smNodes := [{ rank := 0, op := "OpName.FW_identity", ins := [700], outs := [701] }, { rank := 0, op := "OpName.FW_sum", ins := [10], outs := [11] }, { rank := 0, op := "OpName.FW_identity", ins := [702], outs := [703] }, { rank := 0, op := "OpName.FW_identity", ins := [704], outs := [705] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_sum", ins := [20], outs := [30] }, { rank := 0, op := "OpName.FW_identity", ins := [800], outs := [900] }, { rank := 1, op := "OpName.FW_sum", ins := [21], outs := [31] }, { rank := 1, op := "OpName.FW_identity", ins := [801], outs := [901] }, { rank := 2, op := "OpName.FW_sum", ins := [22], outs := [32] }, { rank := 2, op := "OpName.FW_identity", ins := [802], outs := [902] }, { rank := 3, op := "OpName.FW_sum", ins := [23], outs := [33] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_identity", ins := [700], outs := [701] }, { rank := 0, op := "OpName.FW_sum", ins := [10], outs := [11] }, { rank := 0, op := "OpName.FW_identity", ins := [702], outs := [703] }, { rank := 0, op := "OpName.FW_identity", ins := [704], outs := [705] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_sum", ins := [20], outs := [30] }, { rank := 0, op := "OpName.FW_identity", ins := [800], outs := [900] }, { rank := 1, op := "OpName.FW_sum", ins := [21], outs := [31] }, { rank := 1, op := "OpName.FW_identity", ins := [801], outs := [901] }, { rank := 2, op := "OpName.FW_sum", ins := [22], outs := [32] }, { rank := 2, op := "OpName.FW_identity", ins := [802], outs := [902] }, { rank := 3, op := "OpName.FW_sum", ins := [23], outs := [33] }]
    let pmInputTids : List Tid := [20, 21, 22, 23]
    let pmOutputTids : List Tid := [30, 31, 32, 33]
    let rankCount := pmInputTids.length
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_pre.Holds smStore pmStore := hstate fact_pre (by native_decide)
    change ShardedRel (smStore 10) (pmInputTids.map pmStore) 1 [1, 8, 3] [1, 2, 3] at hin
    have hSmWriter : smFinal 11 = fw_sum (smStore 10) := by
      calc
        smFinal 11 = fw_sum (((smNodes.take 1).foldl
            (applyNodeDistributedFaithful SyntheticKRank.smGraph) smStore) 10) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.smGraph) smStore) 11 = _
          rw [show smNodes = (smNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_sum", ins := [10], outs := [11] }] ++ (smNodes.drop 2) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.smGraph smStore (smNodes.take 1) (smNodes.drop 2)
            { rank := 0, op := "OpName.FW_sum", ins := [10], outs := [11] } 11 (fun t => fw_sum (t 10))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide),
              if_neg (by decide), if_neg (by decide),
              if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_sum_out SyntheticKRank.smGraph t 0 10 11
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_sum (smStore 10) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.smGraph
            (smNodes.take 1) smStore 10 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 30 = fw_sum (pmStore 20) := by
      calc
        pmFinal 30 = fw_sum (((pmNodes.take 0)).foldl
            (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 20) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 30 = _
          rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_sum", ins := [20], outs := [30] }] ++ (pmNodes.drop 1) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
            { rank := 0, op := "OpName.FW_sum", ins := [20], outs := [30] } 30 (fun t => fw_sum (t 20))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide),
              if_neg (by decide), if_neg (by decide),
              if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_sum_out SyntheticKRank.pmGraph t 0 20 30
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_sum (pmStore 20) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 0) pmStore 20 (by native_decide) (by native_decide)]
    have hPmShape0 : (pmFinal 30).shape = [1] := by
      rw [hPmWriter0]
      exact fw_sum_shape _
    have hPmWriter1 : pmFinal 31 = fw_sum (pmStore 21) := by
      calc
        pmFinal 31 = fw_sum (((pmNodes.take 2)).foldl
            (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 21) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 31 = _
          rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 1, op := "OpName.FW_sum", ins := [21], outs := [31] }] ++ (pmNodes.drop 3) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
            { rank := 1, op := "OpName.FW_sum", ins := [21], outs := [31] } 31 (fun t => fw_sum (t 21))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide),
              if_neg (by decide), if_neg (by decide),
              if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_sum_out SyntheticKRank.pmGraph t 1 21 31
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_sum (pmStore 21) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 2) pmStore 21 (by native_decide) (by native_decide)]
    have hPmShape1 : (pmFinal 31).shape = [1] := by
      rw [hPmWriter1]
      exact fw_sum_shape _
    have hPmWriter2 : pmFinal 32 = fw_sum (pmStore 22) := by
      calc
        pmFinal 32 = fw_sum (((pmNodes.take 4)).foldl
            (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 22) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 32 = _
          rw [show pmNodes = (pmNodes.take 4) ++ [{ rank := 2, op := "OpName.FW_sum", ins := [22], outs := [32] }] ++ (pmNodes.drop 5) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
            { rank := 2, op := "OpName.FW_sum", ins := [22], outs := [32] } 32 (fun t => fw_sum (t 22))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide),
              if_neg (by decide), if_neg (by decide),
              if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_sum_out SyntheticKRank.pmGraph t 2 22 32
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_sum (pmStore 22) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 4) pmStore 22 (by native_decide) (by native_decide)]
    have hPmShape2 : (pmFinal 32).shape = [1] := by
      rw [hPmWriter2]
      exact fw_sum_shape _
    have hPmWriter3 : pmFinal 33 = fw_sum (pmStore 23) := by
      calc
        pmFinal 33 = fw_sum (((pmNodes.take 6)).foldl
            (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore 23) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticKRank.pmGraph) pmStore) 33 = _
          rw [show pmNodes = (pmNodes.take 6) ++ [{ rank := 3, op := "OpName.FW_sum", ins := [23], outs := [33] }] ++ (pmNodes.drop 7) by native_decide]
          apply foldl_faithful_middle_writer SyntheticKRank.pmGraph pmStore (pmNodes.take 6) (pmNodes.drop 7)
            { rank := 3, op := "OpName.FW_sum", ins := [23], outs := [33] } 33 (fun t => fw_sum (t 23))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide),
              if_neg (by decide), if_neg (by decide),
              if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_sum_out SyntheticKRank.pmGraph t 3 23 33
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_sum (pmStore 23) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticKRank.pmGraph
            (pmNodes.take 6) pmStore 23 (by native_decide) (by native_decide)]
    have hPmShape3 : (pmFinal 33).shape = [1] := by
      rw [hPmWriter3]
      exact fw_sum_shape _
    have hFullShape : (smFinal 11).shape = [1] := by
      rw [hSmWriter]
      exact fw_sum_shape _
    have hOutValue : smFinal 11 =
        allReducePrim (pmOutputTids.map pmFinal).length 0 (pmOutputTids.map pmFinal) := by
      rw [hSmWriter, hin.full_value]
      have hComm := TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum 1 rankCount (pmInputTids.map pmStore) rfl
        (by simp [rankCount, pmInputTids])
        [1, 2, 3]
        (by simp only [pmInputTids, List.map, List.head?, Option.map, Option.getD];
            exact hin.shard_shapes _ (by simp [pmInputTids]))
        hin.shard_shapes hin.gather_dim_lt (by native_decide) (by native_decide)
      simp only [pmInputTids, pmOutputTids, rankCount, List.map, List.length_cons, List.length_nil] at hComm ⊢
      rw [hComm]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
    have hout : fact_post.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 11) (pmOutputTids.map pmFinal) [1]
      refine {
        full_value := hOutValue
        full_shape := hFullShape
        contributions_nonempty := by simp [pmOutputTids]
        contribution_shapes := ?_
        reduced_shape := ?_
      }
      · intro shard hmem
        simp only [pmOutputTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst shard
          exact hPmShape0
        · subst shard
          exact hPmShape1
        · subst shard
          exact hPmShape2
        · subst shard
          exact hPmShape3
      · rw [← hOutValue]
        exact hFullShape
    exact RelationState.Holds.mono_insert hframe hout (by native_decide)

#print axioms segment_000000
end
end TrainVerify.Denote.SyntheticKRank
