/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def input_0 : RelationFact :=
  .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]

private def output_0 : RelationFact :=
  .sharded 300 [400, 401, 402] 1 [2, 9, 7] [2, 3, 7]

private def input_1 : RelationFact :=
  .sharded 101 [210, 211, 212] 1 [2, 9, 5] [2, 3, 5]

private def output_1 : RelationFact :=
  .sharded 301 [410, 411, 412] 1 [2, 9, 7] [2, 3, 7]

private def joined_0 : RelationFact :=
  .joined 300 900 [2, 9, 7]

private def weight_eq_0 : RelationFact :=
  .tensorEq .sm 500 .pm 500

private def weight_shape_0 : RelationFact :=
  .tensorShape .pm 500 [7, 5]

private def weight_eq_1 : RelationFact :=
  .tensorEq .sm 501 .pm 501

private def weight_shape_1 : RelationFact :=
  .tensorShape .pm 501 [7, 5]

private def anchor : RelationFact :=
  .tensorShape .sm 100 [2, 9, 5]

private def state_pre : RelationState where
  facts := [input_0, input_1, weight_eq_0, weight_shape_0, weight_eq_1, weight_shape_1]
  nonempty := by decide

private def state_post : RelationState where
  facts := [output_0, output_1, joined_0]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness

namespace TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_multiref", ins := [90], outs := [100, 101, 102] }, { rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_multiref", ins := [190], outs := [200, 210, 220] }, { rank := 1, op := "OpName.FW_multiref", ins := [191], outs := [201, 211, 221] }, { rank := 2, op := "OpName.FW_multiref", ins := [192], outs := [202, 212, 222] }, { rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] }] }
private def segment_generic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }]
private def segment_generic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] }]

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
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 9, 5] [2, 3, 5] at hIn0
    have hWeightEq0 : weight_eq_0.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 500 = pmStore 500 at hWeightEq0
    have hWeightShape0 : weight_shape_0.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 500).shape = [7, 5] at hWeightShape0
    have hIn1 : input_1.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 101) [pmStore 210, pmStore 211, pmStore 212] 1 [2, 9, 5] [2, 3, 5] at hIn1
    have hWeightEq1 : weight_eq_1.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 501 = pmStore 501 at hWeightEq1
    have hWeightShape1 : weight_shape_1.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 501).shape = [7, 5] at hWeightShape1
    have hLocalSm0 : smFinal 300 = fw_linear (smStore 100) (smStore 500) := by
      change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph) smStore) 300 = _
      rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] ++ smNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph smStore (smNodes.take 1) (smNodes.drop 2)
        { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] } 300 (fun t => fw_linear (t 100) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph t 0 100 500 300
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph (smNodes.take 1) smStore 100 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph (smNodes.take 1) smStore 500 (by native_decide) (by native_decide)]
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
      rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] } 401 (fun t => fw_linear (t 201) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 1 201 500 401
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 2) pmStore 201 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 2) pmStore 500 (by native_decide) (by native_decide)]
    have hLocalPm0_2 : pmFinal 402 = fw_linear (pmStore 202) (pmStore 500) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 402 = _
      rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }] ++ pmNodes.drop 5 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
        { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] } 402 (fun t => fw_linear (t 202) (t 500)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 2 202 500 402
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 4) pmStore 202 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 4) pmStore 500 (by native_decide) (by native_decide)]
    have hLocalSm1 : smFinal 301 = fw_linear (smStore 101) (smStore 501) := by
      change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph) smStore) 301 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph smStore (smNodes.take 0) (smNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] } 301 (fun t => fw_linear (t 101) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph t 0 101 501 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph (smNodes.take 0) smStore 101 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.smGraph (smNodes.take 0) smStore 501 (by native_decide) (by native_decide)]
    have hLocalPm1_0 : pmFinal 410 = fw_linear (pmStore 210) (pmStore 501) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 410 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] } 410 (fun t => fw_linear (t 210) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 0 210 501 410
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 1) pmStore 210 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 1) pmStore 501 (by native_decide) (by native_decide)]
    have hLocalPm1_1 : pmFinal 411 = fw_linear (pmStore 211) (pmStore 501) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 411 = _
      rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }] ++ pmNodes.drop 4 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] } 411 (fun t => fw_linear (t 211) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 1 211 501 411
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 3) pmStore 211 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 3) pmStore 501 (by native_decide) (by native_decide)]
    have hLocalPm1_2 : pmFinal 412 = fw_linear (pmStore 212) (pmStore 501) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 412 = _
      rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }] ++ pmNodes.drop 6 by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 5) (pmNodes.drop 6)
        { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] } 412 (fun t => fw_linear (t 212) (t 501)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 2 212 501 412
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 5) pmStore 212 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.take 5) pmStore 501 (by native_decide) (by native_decide)]
    have hGatherRaw : pmFinal 900 = allGatherPrimDimN 1 3 0 [(((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400, (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401, (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 402] := by
      change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 900 = _
      conv_lhs =>
        rw [show pmNodes = (pmNodes.take 6) ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] }] ++ (pmNodes.drop 7) by native_decide]
      rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph pmStore (pmNodes.take 6) (pmNodes.drop 7)
        { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] } 900 (fun t => allGatherPrimDimN 1 3 0 [t 400, t 401, t 402]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_allGatherPrimDimN_out TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph t 0 [400, 401, 402] 900 1
        ) (by native_decide) (by native_decide)]
    have hGatherInputFinal0 : (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400 = pmFinal 400 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 6) (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 400 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 6) ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
      exact h.symm
    have hGatherInputFinal1 : (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401 = pmFinal 401 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 6) (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 401 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 6) ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
      exact h.symm
    have hGatherInputFinal2 : (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 402 = pmFinal 402 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph (pmNodes.drop 6) (((pmNodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness.pmGraph) pmStore) 402 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show (pmNodes.take 6) ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
      exact h.symm
    have hGatherWriter : pmFinal 900 = allGatherPrimDimN 1 3 0 [pmFinal 400, pmFinal 401, pmFinal 402] := by
      rw [hGatherRaw]
      rw [hGatherInputFinal0, hGatherInputFinal1, hGatherInputFinal2]
    have hComm0 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 200, pmStore 201, pmStore 202].length) (b := 2) (s := 3) (i := 5) (o := 7) (xs := [pmStore 200, pmStore 201, pmStore 202]) (w := pmStore 500) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn0.shard_shapes x hx) hWeightShape0)
    have hLocalValue0 : smFinal 300 = allGatherPrimDimN 1 [pmFinal 400, pmFinal 401, pmFinal 402].length 0 [pmFinal 400, pmFinal 401, pmFinal 402] := by
      rw [hLocalSm0, hWeightEq0, hIn0.full_value, hComm0]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm0_0, ← hLocalPm0_1, ← hLocalPm0_2]
    have hLocalShape0_0 : (pmFinal 400).shape = [2, 3, 7] := by
      rw [hLocalPm0_0]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalShape0_1 : (pmFinal 401).shape = [2, 3, 7] := by
      rw [hLocalPm0_1]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalShape0_2 : (pmFinal 402).shape = [2, 3, 7] := by
      rw [hLocalPm0_2]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes _ (by simp)) hWeightShape0
    have hLocalOut0 : output_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401, pmFinal 402] 1 [2, 9, 7] [2, 3, 7]
      refine { full_value := hLocalValue0, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue0, allGatherPrimDimN_shape 1 [pmFinal 400, pmFinal 401, pmFinal 402].length [pmFinal 400, pmFinal 401, pmFinal 402] [2, 3, 7]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape0_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShape0_0
        · exact hLocalShape0_1
        · exact hLocalShape0_2
    have hComm1 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 210, pmStore 211, pmStore 212].length) (b := 2) (s := 3) (i := 5) (o := 7) (xs := [pmStore 210, pmStore 211, pmStore 212]) (w := pmStore 501) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn1.shard_shapes x hx) hWeightShape1)
    have hLocalValue1 : smFinal 301 = allGatherPrimDimN 1 [pmFinal 410, pmFinal 411, pmFinal 412].length 0 [pmFinal 410, pmFinal 411, pmFinal 412] := by
      rw [hLocalSm1, hWeightEq1, hIn1.full_value, hComm1]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm1_0, ← hLocalPm1_1, ← hLocalPm1_2]
    have hLocalShape1_0 : (pmFinal 410).shape = [2, 3, 7] := by
      rw [hLocalPm1_0]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn1.shard_shapes _ (by simp)) hWeightShape1
    have hLocalShape1_1 : (pmFinal 411).shape = [2, 3, 7] := by
      rw [hLocalPm1_1]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn1.shard_shapes _ (by simp)) hWeightShape1
    have hLocalShape1_2 : (pmFinal 412).shape = [2, 3, 7] := by
      rw [hLocalPm1_2]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn1.shard_shapes _ (by simp)) hWeightShape1
    have hLocalOut1 : output_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 301) [pmFinal 410, pmFinal 411, pmFinal 412] 1 [2, 9, 7] [2, 3, 7]
      refine { full_value := hLocalValue1, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue1, allGatherPrimDimN_shape 1 [pmFinal 410, pmFinal 411, pmFinal 412].length [pmFinal 410, pmFinal 411, pmFinal 412] [2, 3, 7]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape1_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShape1_0
        · exact hLocalShape1_1
        · exact hLocalShape1_2
    have hGatherFinal : output_0.Holds smFinal pmFinal := hLocalOut0
    change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401, pmFinal 402] 1 [2, 9, 7] [2, 3, 7] at hGatherFinal
    have hJoinedValue : smFinal 300 = pmFinal 900 := by
      rw [TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather hGatherFinal]
      simp only [List.length_cons, List.length_nil]
      exact hGatherWriter.symm
    have hJoinedOut : joined_0.Holds smFinal pmFinal := by
      change smFinal 300 = pmFinal 900 ∧ (smFinal 300).shape = [2, 9, 7] ∧ (pmFinal 900).shape = [2, 9, 7]
      refine ⟨hJoinedValue, hGatherFinal.full_shape, ?_⟩
      rw [← hJoinedValue]
      exact hGatherFinal.full_shape
    intro fact hfact
    have covered : fact ∈ [output_0, output_1, joined_0] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [output_0, output_1, joined_0] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl
      · exact hLocalOut0
      · exact hLocalOut1
      · exact hJoinedOut
    · exact hframe fact old

#print axioms segment_generic
end
end TrainVerify.Denote.GeneratedLocalLinearMultiGatherWitness
