/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def local_in_0 : RelationFact :=
  .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]

private def local_out_0 : RelationFact :=
  .sharded 300 [400, 401, 402] 1 [2, 9, 21] [2, 3, 21]

private def local_in_1 : RelationFact :=
  .sharded 101 [210, 211, 212] 1 [2, 9, 5] [2, 3, 5]

private def local_out_1 : RelationFact :=
  .sharded 301 [410, 411, 412] 1 [2, 9, 21] [2, 3, 21]

private def a2a_out_0 : RelationFact :=
  .sharded 300 [800, 801, 802] 2 [2, 9, 21] [2, 9, 7]

private def a2a_out_1 : RelationFact :=
  .sharded 301 [810, 811, 812] 2 [2, 9, 21] [2, 9, 7]

private def weight_eq_0 : RelationFact :=
  .tensorEq .sm 500 .pm 500

private def weight_shape_0 : RelationFact :=
  .tensorShape .pm 500 [21, 5]

private def weight_eq_1 : RelationFact :=
  .tensorEq .sm 501 .pm 501

private def weight_shape_1 : RelationFact :=
  .tensorShape .pm 501 [21, 5]

private def anchor : RelationFact :=
  .tensorShape .sm 100 [2, 9, 5]

private def state_pre : RelationState where
  facts := [local_in_0, local_in_1, weight_eq_0, weight_shape_0, weight_eq_1, weight_shape_1]
  nonempty := by decide

private def state_post : RelationState where
  facts := [local_out_0, local_out_1, a2a_out_0, a2a_out_1]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness

namespace TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [800], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [810], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [801], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [811], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [802], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [812], params := [1, 2] }] }
private def segment_generic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }]
private def segment_generic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [800], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [810], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [801], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [811], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [802], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [812], params := [1, 2] }]

private def segment_generic :
    ClosedDepSegmentCertificate TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph state_pre state_post where
  smNodes := segment_generic_sm_nodes
  pmNodes := segment_generic_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_generic_sm_nodes
    let pmNodes : List NodeDecl := segment_generic_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hIn0 : local_in_1.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 101) [pmStore 210, pmStore 211, pmStore 212] 1 [2, 9, 5] [2, 3, 5] at hIn0
    have hWeightEq0 : weight_eq_1.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 501 = pmStore 501 at hWeightEq0
    have hWeightShape0 : weight_shape_1.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 501).shape = [21, 5] at hWeightShape0
    have hIn1 : local_in_0.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 9, 5] [2, 3, 5] at hIn1
    have hWeightEq1 : weight_eq_0.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 500 = pmStore 500 at hWeightEq1
    have hWeightShape1 : weight_shape_0.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 500).shape = [21, 5] at hWeightShape1
    have hLocalSm0 : smFinal 301 = fw_linear (smStore 101) (smStore 501) := by
      change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph) smStore) 301 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph smStore (smNodes.take 0) (smNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] } 301 (fun t => fw_linear (t 101) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph t 0 101 501 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph (smNodes.take 0) smStore 101 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph (smNodes.take 0) smStore 501 (by native_decide) (by native_decide)]
    have hLocalPm0_0 : pmFinal 410 = fw_linear (pmStore 210) (pmStore 501) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] } 410 (fun t => fw_linear (t 210) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 0 210 501 410
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 1) pmStore 210 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 1) pmStore 501 (by native_decide) (by native_decide)]
    have hLocalPm0_1 : pmFinal 411 = fw_linear (pmStore 211) (pmStore 501) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 = _
      rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }] ++ pmNodes.drop 4 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] } 411 (fun t => fw_linear (t 211) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 1 211 501 411
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 3) pmStore 211 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 3) pmStore 501 (by native_decide) (by native_decide)]
    have hLocalPm0_2 : pmFinal 412 = fw_linear (pmStore 212) (pmStore 501) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 = _
      rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }] ++ pmNodes.drop 6 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 5) (pmNodes.drop 6)
        { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] } 412 (fun t => fw_linear (t 212) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 2 212 501 412
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 5) pmStore 212 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 5) pmStore 501 (by native_decide) (by native_decide)]
    have hLocalSm1 : smFinal 300 = fw_linear (smStore 100) (smStore 500) := by
      change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph) smStore) 300 = _
      rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] ++ smNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph smStore (smNodes.take 1) (smNodes.drop 2)
        { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] } 300 (fun t => fw_linear (t 100) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph t 0 100 500 300
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph (smNodes.take 1) smStore 100 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.smGraph (smNodes.take 1) smStore 500 (by native_decide) (by native_decide)]
    have hLocalPm1_0 : pmFinal 400 = fw_linear (pmStore 200) (pmStore 500) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 = _
      rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] } 400 (fun t => fw_linear (t 200) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 0 200 500 400
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 0) pmStore 500 (by native_decide) (by native_decide)]
    have hLocalPm1_1 : pmFinal 401 = fw_linear (pmStore 201) (pmStore 500) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 = _
      rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] } 401 (fun t => fw_linear (t 201) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 1 201 500 401
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 2) pmStore 201 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 2) pmStore 500 (by native_decide) (by native_decide)]
    have hLocalPm1_2 : pmFinal 402 = fw_linear (pmStore 202) (pmStore 500) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 = _
      rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }] ++ pmNodes.drop 5 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
        { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] } 402 (fun t => fw_linear (t 202) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 2 202 500 402
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 4) pmStore 202 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.take 4) pmStore 500 (by native_decide) (by native_decide)]
    have hComm0 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 210, pmStore 211, pmStore 212].length) (b := 2) (s := 3) (i := 5) (o := 21) (xs := [pmStore 210, pmStore 211, pmStore 212]) (w := pmStore 501) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn0.shard_shapes x hx) hWeightShape0)
    have hLocalValue0 : smFinal 301 = allGatherPrimDimN 1 [pmFinal 410, pmFinal 411, pmFinal 412].length 0 [pmFinal 410, pmFinal 411, pmFinal 412] := by
      rw [hLocalSm0, hWeightEq0, hIn0.full_value, hComm0]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm0_0, ← hLocalPm0_1, ← hLocalPm0_2]
    have hLocalShape0_0 : (pmFinal 410).shape = [2, 3, 21] := by
      rw [hLocalPm0_0]
      exact fw_linear_3d_shape 2 3 5 21 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalShape0_1 : (pmFinal 411).shape = [2, 3, 21] := by
      rw [hLocalPm0_1]
      exact fw_linear_3d_shape 2 3 5 21 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalShape0_2 : (pmFinal 412).shape = [2, 3, 21] := by
      rw [hLocalPm0_2]
      exact fw_linear_3d_shape 2 3 5 21 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalOut0 : local_out_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 301) [pmFinal 410, pmFinal 411, pmFinal 412] 1 [2, 9, 21] [2, 3, 21]
      refine { full_value := hLocalValue0, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue0, allGatherPrimDimN_shape 1 [pmFinal 410, pmFinal 411, pmFinal 412].length [pmFinal 410, pmFinal 411, pmFinal 412] [2, 3, 21]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape0_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShape0_0
        · exact hLocalShape0_1
        · exact hLocalShape0_2
    have hComm1 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 200, pmStore 201, pmStore 202].length) (b := 2) (s := 3) (i := 5) (o := 21) (xs := [pmStore 200, pmStore 201, pmStore 202]) (w := pmStore 500) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn1.shard_shapes x hx) hWeightShape1)
    have hLocalValue1 : smFinal 300 = allGatherPrimDimN 1 [pmFinal 400, pmFinal 401, pmFinal 402].length 0 [pmFinal 400, pmFinal 401, pmFinal 402] := by
      rw [hLocalSm1, hWeightEq1, hIn1.full_value, hComm1]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm1_0, ← hLocalPm1_1, ← hLocalPm1_2]
    have hLocalShape1_0 : (pmFinal 400).shape = [2, 3, 21] := by
      rw [hLocalPm1_0]
      exact fw_linear_3d_shape 2 3 5 21 _ _ (hIn1.shard_shapes _ (by simp)) hWeightShape1
    have hLocalShape1_1 : (pmFinal 401).shape = [2, 3, 21] := by
      rw [hLocalPm1_1]
      exact fw_linear_3d_shape 2 3 5 21 _ _ (hIn1.shard_shapes _ (by simp)) hWeightShape1
    have hLocalShape1_2 : (pmFinal 402).shape = [2, 3, 21] := by
      rw [hLocalPm1_2]
      exact fw_linear_3d_shape 2 3 5 21 _ _ (hIn1.shard_shapes _ (by simp)) hWeightShape1
    have hLocalOut1 : local_out_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401, pmFinal 402] 1 [2, 9, 21] [2, 3, 21]
      refine { full_value := hLocalValue1, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue1, allGatherPrimDimN_shape 1 [pmFinal 400, pmFinal 401, pmFinal 402].length [pmFinal 400, pmFinal 401, pmFinal 402] [2, 3, 21]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape1_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShape1_0
        · exact hLocalShape1_1
        · exact hLocalShape1_2
    have hA2AIn0 : local_out_1.Holds smFinal pmFinal := hLocalOut0
    change ShardedRel (smFinal 301) [pmFinal 410, pmFinal 411, pmFinal 412] 1 [2, 9, 21] [2, 3, 21] at hA2AIn0
    let inputTids0 : List Tid := [410, 411, 412]
    let outputTids0 : List Tid := [810, 811, 812]
    let rankCount0 := outputTids0.length
    have hRankCount0 : rankCount0 = TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph.numRanks := by rfl
    let xs0 := inputTids0.map pmFinal
    have hHead0 : ((xs0.head?.map (fun t => t.shape)).getD []) = [2, 3, 21] := by
      simp only [xs0, inputTids0, List.map, List.head?, Option.map, Option.getD]
      exact hA2AIn0.shard_shapes (pmFinal 410) (by simp)
    have hRankXs0 : rankCount0 = xs0.length := by simp [rankCount0, outputTids0, xs0, inputTids0]
    have hA2APrefix0_0_0 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 = pmFinal 410 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hA2APrefix0_0_1 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 = pmFinal 411 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hA2APrefix0_0_2 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 = pmFinal 412 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hA2AInputs0_0 : inputTids0.map ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs0 := by
      simp only [inputTids0, xs0, List.map]
      rw [hA2APrefix0_0_0, hA2APrefix0_0_1, hA2APrefix0_0_2]
    have hA2AWriter0_0 : pmFinal 810 = allToAllPrimWithDims rankCount0 0 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 810 = _
      rw [show pmNodes = pmNodes.take 7 ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [810], params := [1, 2] }] ++ pmNodes.drop 8 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 7) (pmNodes.drop 8)
        { rank := 0, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [810], params := [1, 2] } 810 (fun t => allToAllPrimWithDims rankCount0 0 (inputTids0.map t) 1 2)]
      · rw [hA2AInputs0_0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount0]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 0 inputTids0 810 1 2
      · native_decide
      · native_decide
    have hA2AShape0_0 : (pmFinal 810).shape = [2, 9, 7] := by
      rw [hA2AWriter0_0, allToAllPrimWithDims_shape rankCount0 0 xs0 1 2 [2, 3, 21] hHead0 (by native_decide)]
      native_decide
    have hA2APrefix0_1_0 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 = pmFinal 410 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
      exact h.symm
    have hA2APrefix0_1_1 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 = pmFinal 411 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
      exact h.symm
    have hA2APrefix0_1_2 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 = pmFinal 412 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
      exact h.symm
    have hA2AInputs0_1 : inputTids0.map ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs0 := by
      simp only [inputTids0, xs0, List.map]
      rw [hA2APrefix0_1_0, hA2APrefix0_1_1, hA2APrefix0_1_2]
    have hA2AWriter0_1 : pmFinal 811 = allToAllPrimWithDims rankCount0 1 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 811 = _
      rw [show pmNodes = pmNodes.take 9 ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [811], params := [1, 2] }] ++ pmNodes.drop 10 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 9) (pmNodes.drop 10)
        { rank := 1, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [811], params := [1, 2] } 811 (fun t => allToAllPrimWithDims rankCount0 1 (inputTids0.map t) 1 2)]
      · rw [hA2AInputs0_1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount0]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 1 inputTids0 811 1 2
      · native_decide
      · native_decide
    have hA2AShape0_1 : (pmFinal 811).shape = [2, 9, 7] := by
      rw [hA2AWriter0_1, allToAllPrimWithDims_shape rankCount0 1 xs0 1 2 [2, 3, 21] hHead0 (by native_decide)]
      native_decide
    have hA2APrefix0_2_0 : ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 = pmFinal 410 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 11) ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 410 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 11 ++ pmNodes.drop 11 = pmNodes by exact List.take_append_drop 11 pmNodes] at h
      exact h.symm
    have hA2APrefix0_2_1 : ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 = pmFinal 411 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 11) ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 411 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 11 ++ pmNodes.drop 11 = pmNodes by exact List.take_append_drop 11 pmNodes] at h
      exact h.symm
    have hA2APrefix0_2_2 : ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 = pmFinal 412 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 11) ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 412 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 11 ++ pmNodes.drop 11 = pmNodes by exact List.take_append_drop 11 pmNodes] at h
      exact h.symm
    have hA2AInputs0_2 : inputTids0.map ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs0 := by
      simp only [inputTids0, xs0, List.map]
      rw [hA2APrefix0_2_0, hA2APrefix0_2_1, hA2APrefix0_2_2]
    have hA2AWriter0_2 : pmFinal 812 = allToAllPrimWithDims rankCount0 2 xs0 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 812 = _
      rw [show pmNodes = pmNodes.take 11 ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [812], params := [1, 2] }] ++ pmNodes.drop 12 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 11) (pmNodes.drop 12)
        { rank := 2, op := "OpName.AllToAllPrim", ins := [410, 411, 412], outs := [812], params := [1, 2] } 812 (fun t => allToAllPrimWithDims rankCount0 2 (inputTids0.map t) 1 2)]
      · rw [hA2AInputs0_2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount0]
        simpa [inputTids0] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 2 inputTids0 812 1 2
      · native_decide
      · native_decide
    have hA2AShape0_2 : (pmFinal 812).shape = [2, 9, 7] := by
      rw [hA2AWriter0_2, allToAllPrimWithDims_shape rankCount0 2 xs0 1 2 [2, 3, 21] hHead0 (by native_decide)]
      native_decide
    have hOrdered0 : outputTids0.map pmFinal = List.ofFn (fun r : Fin rankCount0 => allToAllPrimWithDims rankCount0 r.1 xs0 1 2) := by
      simp only [outputTids0, rankCount0, List.map]
      rw [hA2AWriter0_0, hA2AWriter0_1, hA2AWriter0_2]
      rfl
    have hGatherShape0 : (allGatherPrimDimN 1 rankCount0 0 xs0).shape = [2, 9, 21] := by
      rw [hRankXs0]
      calc _ = (smFinal 301).shape := congrArg (fun t => t.shape) hA2AIn0.full_value.symm
           _ = _ := hA2AIn0.full_shape
    have hOdim0 : 2 < (allGatherPrimDimN 1 rankCount0 0 xs0).shape.length := by rw [hGatherShape0]; native_decide
    have hDiv0 : (allGatherPrimDimN 1 rankCount0 0 xs0).shape.getD 2 0 % rankCount0 = 0 := by rw [hGatherShape0]; native_decide
    have hOdimXs0 := hOdim0
    have hDivXs0 := hDiv0
    rw [hRankXs0] at hOdimXs0 hDivXs0
    have hA2AOut0 : a2a_out_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 301) [pmFinal 810, pmFinal 811, pmFinal 812] 2 [2, 9, 21] [2, 9, 7]
      refine { full_value := ?_, full_shape := hA2AIn0.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [show [pmFinal 810, pmFinal 811, pmFinal 812] = outputTids0.map pmFinal by rfl, hOrdered0, List.length_ofFn]
        rw [hRankXs0, TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs0 (by simp [xs0, inputTids0]) hOdimXs0 hDivXs0]
        simp only [rankCount0, outputTids0, xs0, inputTids0, List.map, List.length_cons, List.length_nil]
        exact hA2AIn0.full_value
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hA2AShape0_0
        · exact hA2AShape0_1
        · exact hA2AShape0_2
    have hA2AIn1 : local_out_0.Holds smFinal pmFinal := hLocalOut1
    change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401, pmFinal 402] 1 [2, 9, 21] [2, 3, 21] at hA2AIn1
    let inputTids1 : List Tid := [400, 401, 402]
    let outputTids1 : List Tid := [800, 801, 802]
    let rankCount1 := outputTids1.length
    have hRankCount1 : rankCount1 = TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph.numRanks := by rfl
    let xs1 := inputTids1.map pmFinal
    have hHead1 : ((xs1.head?.map (fun t => t.shape)).getD []) = [2, 3, 21] := by
      simp only [xs1, inputTids1, List.map, List.head?, Option.map, Option.getD]
      exact hA2AIn1.shard_shapes (pmFinal 400) (by simp)
    have hRankXs1 : rankCount1 = xs1.length := by simp [rankCount1, outputTids1, xs1, inputTids1]
    have hA2APrefix1_0_0 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 = pmFinal 400 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
      exact h.symm
    have hA2APrefix1_0_1 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 = pmFinal 401 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
      exact h.symm
    have hA2APrefix1_0_2 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 = pmFinal 402 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
      exact h.symm
    have hA2AInputs1_0 : inputTids1.map ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs1 := by
      simp only [inputTids1, xs1, List.map]
      rw [hA2APrefix1_0_0, hA2APrefix1_0_1, hA2APrefix1_0_2]
    have hA2AWriter1_0 : pmFinal 800 = allToAllPrimWithDims rankCount1 0 xs1 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 800 = _
      rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [800], params := [1, 2] }] ++ pmNodes.drop 7 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 6) (pmNodes.drop 7)
        { rank := 0, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [800], params := [1, 2] } 800 (fun t => allToAllPrimWithDims rankCount1 0 (inputTids1.map t) 1 2)]
      · rw [hA2AInputs1_0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount1]
        simpa [inputTids1] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 0 inputTids1 800 1 2
      · native_decide
      · native_decide
    have hA2AShape1_0 : (pmFinal 800).shape = [2, 9, 7] := by
      rw [hA2AWriter1_0, allToAllPrimWithDims_shape rankCount1 0 xs1 1 2 [2, 3, 21] hHead1 (by native_decide)]
      native_decide
    have hA2APrefix1_1_0 : ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 = pmFinal 400 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 8) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 8 ++ pmNodes.drop 8 = pmNodes by exact List.take_append_drop 8 pmNodes] at h
      exact h.symm
    have hA2APrefix1_1_1 : ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 = pmFinal 401 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 8) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 8 ++ pmNodes.drop 8 = pmNodes by exact List.take_append_drop 8 pmNodes] at h
      exact h.symm
    have hA2APrefix1_1_2 : ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 = pmFinal 402 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 8) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 8 ++ pmNodes.drop 8 = pmNodes by exact List.take_append_drop 8 pmNodes] at h
      exact h.symm
    have hA2AInputs1_1 : inputTids1.map ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs1 := by
      simp only [inputTids1, xs1, List.map]
      rw [hA2APrefix1_1_0, hA2APrefix1_1_1, hA2APrefix1_1_2]
    have hA2AWriter1_1 : pmFinal 801 = allToAllPrimWithDims rankCount1 1 xs1 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 801 = _
      rw [show pmNodes = pmNodes.take 8 ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [801], params := [1, 2] }] ++ pmNodes.drop 9 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 8) (pmNodes.drop 9)
        { rank := 1, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [801], params := [1, 2] } 801 (fun t => allToAllPrimWithDims rankCount1 1 (inputTids1.map t) 1 2)]
      · rw [hA2AInputs1_1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount1]
        simpa [inputTids1] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 1 inputTids1 801 1 2
      · native_decide
      · native_decide
    have hA2AShape1_1 : (pmFinal 801).shape = [2, 9, 7] := by
      rw [hA2AWriter1_1, allToAllPrimWithDims_shape rankCount1 1 xs1 1 2 [2, 3, 21] hHead1 (by native_decide)]
      native_decide
    have hA2APrefix1_2_0 : ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 = pmFinal 400 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 10) ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 400 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 10 ++ pmNodes.drop 10 = pmNodes by exact List.take_append_drop 10 pmNodes] at h
      exact h.symm
    have hA2APrefix1_2_1 : ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 = pmFinal 401 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 10) ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 401 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 10 ++ pmNodes.drop 10 = pmNodes by exact List.take_append_drop 10 pmNodes] at h
      exact h.symm
    have hA2APrefix1_2_2 : ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 = pmFinal 402 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph (pmNodes.drop 10) ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 402 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 10 ++ pmNodes.drop 10 = pmNodes by exact List.take_append_drop 10 pmNodes] at h
      exact h.symm
    have hA2AInputs1_2 : inputTids1.map ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) = xs1 := by
      simp only [inputTids1, xs1, List.map]
      rw [hA2APrefix1_2_0, hA2APrefix1_2_1, hA2APrefix1_2_2]
    have hA2AWriter1_2 : pmFinal 802 = allToAllPrimWithDims rankCount1 2 xs1 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph) pmStore) 802 = _
      rw [show pmNodes = pmNodes.take 10 ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [802], params := [1, 2] }] ++ pmNodes.drop 11 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph pmStore (pmNodes.take 10) (pmNodes.drop 11)
        { rank := 2, op := "OpName.AllToAllPrim", ins := [400, 401, 402], outs := [802], params := [1, 2] } 802 (fun t => allToAllPrimWithDims rankCount1 2 (inputTids1.map t) 1 2)]
      · rw [hA2AInputs1_2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount1]
        simpa [inputTids1] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness.pmGraph t 2 inputTids1 802 1 2
      · native_decide
      · native_decide
    have hA2AShape1_2 : (pmFinal 802).shape = [2, 9, 7] := by
      rw [hA2AWriter1_2, allToAllPrimWithDims_shape rankCount1 2 xs1 1 2 [2, 3, 21] hHead1 (by native_decide)]
      native_decide
    have hOrdered1 : outputTids1.map pmFinal = List.ofFn (fun r : Fin rankCount1 => allToAllPrimWithDims rankCount1 r.1 xs1 1 2) := by
      simp only [outputTids1, rankCount1, List.map]
      rw [hA2AWriter1_0, hA2AWriter1_1, hA2AWriter1_2]
      rfl
    have hGatherShape1 : (allGatherPrimDimN 1 rankCount1 0 xs1).shape = [2, 9, 21] := by
      rw [hRankXs1]
      calc _ = (smFinal 300).shape := congrArg (fun t => t.shape) hA2AIn1.full_value.symm
           _ = _ := hA2AIn1.full_shape
    have hOdim1 : 2 < (allGatherPrimDimN 1 rankCount1 0 xs1).shape.length := by rw [hGatherShape1]; native_decide
    have hDiv1 : (allGatherPrimDimN 1 rankCount1 0 xs1).shape.getD 2 0 % rankCount1 = 0 := by rw [hGatherShape1]; native_decide
    have hOdimXs1 := hOdim1
    have hDivXs1 := hDiv1
    rw [hRankXs1] at hOdimXs1 hDivXs1
    have hA2AOut1 : a2a_out_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 800, pmFinal 801, pmFinal 802] 2 [2, 9, 21] [2, 9, 7]
      refine { full_value := ?_, full_shape := hA2AIn1.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [show [pmFinal 800, pmFinal 801, pmFinal 802] = outputTids1.map pmFinal by rfl, hOrdered1, List.length_ofFn]
        rw [hRankXs1, TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs1 (by simp [xs1, inputTids1]) hOdimXs1 hDivXs1]
        simp only [rankCount1, outputTids1, xs1, inputTids1, List.map, List.length_cons, List.length_nil]
        exact hA2AIn1.full_value
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hA2AShape1_0
        · exact hA2AShape1_1
        · exact hA2AShape1_2
    intro fact hfact
    have covered : fact ∈ [local_out_1, local_out_0, a2a_out_1, a2a_out_0] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [local_out_1, local_out_0, a2a_out_1, a2a_out_0] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl | rfl
      · exact hLocalOut0
      · exact hLocalOut1
      · exact hA2AOut0
      · exact hA2AOut1
    · exact hframe fact old

#print axioms segment_generic
end
end TrainVerify.Denote.GeneratedLocalLinearAllToAllTupleAtomicWitness
