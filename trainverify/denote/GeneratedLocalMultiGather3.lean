/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def input_0 : RelationFact :=
  .sharded 100 [200, 201] 1 [2, 6, 5] [2, 3, 5]

private def output_0 : RelationFact :=
  .sharded 300 [400, 401] 1 [2, 6, 7] [2, 3, 7]

private def joined_0 : RelationFact :=
  .joined 300 900 [2, 6, 7]

private def gather_input_1 : RelationFact :=
  .sharded 102 [220, 221] 1 [2, 6, 5] [2, 3, 5]

private def joined_1 : RelationFact :=
  .joined 102 901 [2, 6, 5]

private def weight_eq_0 : RelationFact :=
  .tensorEq .sm 500 .pm 500

private def weight_shape_0 : RelationFact :=
  .tensorShape .pm 500 [7, 5]

private def anchor : RelationFact :=
  .tensorShape .sm 100 [2, 6, 5]

private def state_pre : RelationState where
  facts := [input_0, weight_eq_0, weight_shape_0, gather_input_1]
  nonempty := by decide

private def state_post : RelationState where
  facts := [output_0, joined_0, joined_1]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness

namespace TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_multiref", ins := [90], outs := [100, 101, 102] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] }
private def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_multiref", ins := [190], outs := [200, 210, 220] }, { rank := 1, op := "OpName.FW_multiref", ins := [191], outs := [201, 211, 221] }, { rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401], outs := [900], params := [1] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221], outs := [901], params := [1] }] }
private def segment_generic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }]
private def segment_generic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401], outs := [900], params := [1] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221], outs := [901], params := [1] }]

private def segment_generic :
    ClosedDepSegmentCertificate TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph state_pre state_post where
  smNodes := segment_generic_sm_nodes
  pmNodes := segment_generic_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_generic_sm_nodes
    let pmNodes : List NodeDecl := segment_generic_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hIn0 : input_0.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201] 1 [2, 6, 5] [2, 3, 5] at hIn0
    have hWeightEq0 : weight_eq_0.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 500 = pmStore 500 at hWeightEq0
    have hWeightShape0 : weight_shape_0.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 500).shape = [7, 5] at hWeightShape0
    have hLocalSm0 : smFinal 300 = fw_linear (smStore 100) (smStore 500) := by
      change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph) smStore) 300 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph smStore (smNodes.take 0) (smNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] } 300 (fun t => fw_linear (t 100) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph t 0 100 500 300
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph (smNodes.take 0) smStore 100 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph (smNodes.take 0) smStore 500 (by native_decide) (by native_decide)]
    have hLocalPm0_0 : pmFinal 400 = fw_linear (pmStore 200) (pmStore 500) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400 = _
      rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] } 400 (fun t => fw_linear (t 200) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 0 200 500 400
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 0) pmStore 500 (by native_decide) (by native_decide)]
    have hLocalPm0_1 : pmFinal 401 = fw_linear (pmStore 201) (pmStore 500) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] } 401 (fun t => fw_linear (t 201) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 1 201 500 401
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 1) pmStore 500 (by native_decide) (by native_decide)]
    have hGather0_Raw : pmFinal 900 = allGatherPrimDimN 1 2 0 [(((pmNodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400, (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401] := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 900 = _
      conv_lhs =>
        rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401], outs := [900], params := [1] }] ++ (pmNodes.drop 3) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401], outs := [900], params := [1] } 900 (fun t => allGatherPrimDimN 1 2 0 [t 400, t 401]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_allGatherPrimDimN_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 0 [400, 401] 900 1
        ) (by native_decide) (by native_decide)]
    have hGather0_InputFinal0 : (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400 = pmFinal 400 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 2) (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 2) ++ pmNodes.drop 2 = pmNodes by exact List.take_append_drop 2 pmNodes] at h
      exact h.symm
    have hGather0_InputFinal1 : (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401 = pmFinal 401 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 2) (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 2) ++ pmNodes.drop 2 = pmNodes by exact List.take_append_drop 2 pmNodes] at h
      exact h.symm
    have hGather0_Writer : pmFinal 900 = allGatherPrimDimN 1 2 0 [pmFinal 400, pmFinal 401] := by
      rw [hGather0_Raw]
      rw [hGather0_InputFinal0, hGather0_InputFinal1]
    have hGather1_Raw : pmFinal 901 = allGatherPrimDimN 1 2 0 [(((pmNodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 220, (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 221] := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 901 = _
      conv_lhs =>
        rw [show pmNodes = (pmNodes.take 3) ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221], outs := [901], params := [1] }] ++ (pmNodes.drop 4) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221], outs := [901], params := [1] } 901 (fun t => allGatherPrimDimN 1 2 0 [t 220, t 221]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_allGatherPrimDimN_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 0 [220, 221] 901 1
        ) (by native_decide) (by native_decide)]
    have hGather1_InputFinal0 : (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 220 = pmFinal 220 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 3) (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 220 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 3) ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
      exact h.symm
    have hGather1_InputFinal1 : (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 221 = pmFinal 221 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 3) (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 221 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 3) ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
      exact h.symm
    have hGather1_Writer : pmFinal 901 = allGatherPrimDimN 1 2 0 [pmFinal 220, pmFinal 221] := by
      rw [hGather1_Raw]
      rw [hGather1_InputFinal0, hGather1_InputFinal1]
    have hComm0 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 200, pmStore 201].length) (b := 2) (s := 3) (i := 5) (o := 7) (xs := [pmStore 200, pmStore 201]) (w := pmStore 500) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn0.shard_shapes x hx) hWeightShape0)
    have hLocalValue0 : smFinal 300 = allGatherPrimDimN 1 [pmFinal 400, pmFinal 401].length 0 [pmFinal 400, pmFinal 401] := by
      rw [hLocalSm0, hWeightEq0, hIn0.full_value, hComm0]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm0_0, ← hLocalPm0_1]
    have hLocalShape0_0 : (pmFinal 400).shape = [2, 3, 7] := by
      rw [hLocalPm0_0]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalShape0_1 : (pmFinal 401).shape = [2, 3, 7] := by
      rw [hLocalPm0_1]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalOut0 : output_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401] 1 [2, 6, 7] [2, 3, 7]
      refine { full_value := hLocalValue0, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue0, allGatherPrimDimN_shape 1 [pmFinal 400, pmFinal 401].length [pmFinal 400, pmFinal 401] [2, 3, 7]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape0_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact hLocalShape0_0
        · exact hLocalShape0_1
    have hGather0_Final : output_0.Holds smFinal pmFinal := hLocalOut0
    change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401] 1 [2, 6, 7] [2, 3, 7] at hGather0_Final
    have hJoined0_Value : smFinal 300 = pmFinal 900 := by
      rw [TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather hGather0_Final]
      simp only [List.length_cons, List.length_nil]
      exact hGather0_Writer.symm
    have hJoined0_Out : joined_0.Holds smFinal pmFinal := by
      change smFinal 300 = pmFinal 900 ∧ (smFinal 300).shape = [2, 6, 7] ∧ (pmFinal 900).shape = [2, 6, 7]
      refine ⟨hJoined0_Value, hGather0_Final.full_shape, ?_⟩
      rw [← hJoined0_Value]
      exact hGather0_Final.full_shape
    have hGather1_Final : gather_input_1.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 102) [pmFinal 220, pmFinal 221] 1 [2, 6, 5] [2, 3, 5] at hGather1_Final
    have hJoined1_Value : smFinal 102 = pmFinal 901 := by
      rw [TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather hGather1_Final]
      simp only [List.length_cons, List.length_nil]
      exact hGather1_Writer.symm
    have hJoined1_Out : joined_1.Holds smFinal pmFinal := by
      change smFinal 102 = pmFinal 901 ∧ (smFinal 102).shape = [2, 6, 5] ∧ (pmFinal 901).shape = [2, 6, 5]
      refine ⟨hJoined1_Value, hGather1_Final.full_shape, ?_⟩
      rw [← hJoined1_Value]
      exact hGather1_Final.full_shape
    intro fact hfact
    have covered : fact ∈ [output_0, joined_0, joined_1] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [output_0, joined_0, joined_1] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl
      · exact hLocalOut0
      · exact hJoined0_Out
      · exact hJoined1_Out
    · exact hframe fact old

#print axioms segment_generic
end
end TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness
