import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticLinearOutput
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] }, { rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] }, { rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] }] }

def fact_activation : RelationFact := .joined 100 200 [1, 5, 7]
def fact_weight : RelationFact := .sharded 101 [201, 202, 203] 0 [33, 7] [11, 7]
def fact_output : RelationFact := .sharded 110 [301, 302, 303] 2 [1, 5, 33] [1, 5, 11]
def state_pre : RelationState where
  facts := [fact_activation, fact_weight]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_output]
  nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticLinearOutput.gSM SyntheticLinearOutput.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hActivation : fact_activation.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 100 = pmStore 200 ∧ (smStore 100).shape = [1, 5, 7] ∧ (pmStore 200).shape = [1, 5, 7] at hActivation
    have hWeight : fact_weight.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 101) [pmStore 201, pmStore 202, pmStore 203] 0 [33, 7] [11, 7] at hWeight
    have hSmWriter : smFinal 110 = fw_linear (smStore 100) (smStore 101) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinearOutput.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => fw_linear (t 100) (t 101)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinearOutput.gSM t 0 100 101 110
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gSM (smNodes.take 0) smStore 101 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 301 = fw_linear (pmStore 200) (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinearOutput.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 301 (fun t => fw_linear (t 200) (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinearOutput.gPM t 0 200 201 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gPM (pmNodes.take 0) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 302 = fw_linear (pmStore 200) (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinearOutput.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 302 (fun t => fw_linear (t 200) (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinearOutput.gPM t 1 200 202 302
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gPM (pmNodes.take 1) pmStore 200 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gPM (pmNodes.take 1) pmStore 202 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 303 = fw_linear (pmStore 200) (pmStore 203) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore) 303 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinearOutput.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 303 (fun t => fw_linear (t 200) (t 203)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinearOutput.gPM t 2 200 203 303
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gPM (pmNodes.take 2) pmStore 200 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinearOutput.gPM (pmNodes.take 2) pmStore 203 (by native_decide) (by native_decide)]
    have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
      (K := [pmStore 201, pmStore 202, pmStore 203].length) (b := 1) (s := 5) (i := 7) (o := 11)
      (x := pmStore 200) (ws := [pmStore 201, pmStore 202, pmStore 203])
      (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
    have hOutValue : smFinal 110 = allGatherPrimDimN 2 [pmFinal 301, pmFinal 302, pmFinal 303].length 0 [pmFinal 301, pmFinal 302, pmFinal 303] := by
      rw [hSmWriter, hActivation.1, hWeight.full_value, hComm]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutShape0 : (pmFinal 301).shape = [1, 5, 11] := by
      rw [hPmWriter0]
      exact fw_linear_3d_shape 1 5 7 11 _ _ hActivation.2.2
        (hWeight.shard_shapes (pmStore 201) (by simp))
    have hOutShape1 : (pmFinal 302).shape = [1, 5, 11] := by
      rw [hPmWriter1]
      exact fw_linear_3d_shape 1 5 7 11 _ _ hActivation.2.2
        (hWeight.shard_shapes (pmStore 202) (by simp))
    have hOutShape2 : (pmFinal 303).shape = [1, 5, 11] := by
      rw [hPmWriter2]
      exact fw_linear_3d_shape 1 5 7 11 _ _ hActivation.2.2
        (hWeight.shard_shapes (pmStore 203) (by simp))
    have hout : fact_output.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 301, pmFinal 302, pmFinal 303] 2 [1, 5, 33] [1, 5, 11]
      refine {
        full_value := hOutValue
        full_shape := ?_
        shards_nonempty := by simp
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
      }
      · rw [hOutValue]
        rw [allGatherPrimDimN_shape 2 [pmFinal 301, pmFinal 302, pmFinal 303].length [pmFinal 301, pmFinal 302, pmFinal 303] [1, 5, 11]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]
          exact hOutShape0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hOutShape0
        · exact hOutShape1
        · exact hOutShape2
    intro fact hfact
    have covered : fact ∈ [fact_output] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_output] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#print axioms segment_000000
end
end SyntheticLinearOutput
end TrainVerify.Denote
