import denote.KRankSoftmaxGather

namespace TrainVerify.Denote
open RelationCompiler

namespace SyntheticSoftmaxDim1
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_softmax", ins := [100], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_softmax", ins := [201], outs := [301] }, { rank := 1, op := "OpName.FW_softmax", ins := [202], outs := [302] }, { rank := 2, op := "OpName.FW_softmax", ins := [203], outs := [303] }] }
def fact_in : RelationFact := .sharded 100 [201, 202, 203] 1 [2, 15, 7, 11] [2, 5, 7, 11]
def fact_out : RelationFact := .sharded 110 [301, 302, 303] 1 [2, 15, 7, 11] [2, 5, 7, 11]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_softmax", ins := [100], outs := [110] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_softmax", ins := [201], outs := [301] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_softmax", ins := [202], outs := [302] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_softmax", ins := [203], outs := [303] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticSoftmaxDim1.gSM SyntheticSoftmaxDim1.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim1.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim1.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hInput : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 201, pmStore 202, pmStore 203] 1 [2, 15, 7, 11] [2, 5, 7, 11] at hInput
    have hSmWriter : smFinal 110 = fw_softmax (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim1.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim1.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => fw_softmax (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim1.gSM t 0 100 110 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim1.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 301 = fw_softmax (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim1.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim1.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 301 (fun t => fw_softmax (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim1.gPM t 0 201 301 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim1.gPM (pmNodes.take 0) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 302 = fw_softmax (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim1.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim1.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 302 (fun t => fw_softmax (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim1.gPM t 1 202 302 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim1.gPM (pmNodes.take 1) pmStore 202 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 303 = fw_softmax (pmStore 203) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim1.gPM) pmStore) 303 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim1.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 303 (fun t => fw_softmax (t 203)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim1.gPM t 2 203 303 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim1.gPM (pmNodes.take 2) pmStore 203 (by native_decide) (by native_decide)]
    have htransport := ShardedRel.fw_softmax_dim1_rank4
      (d0 := 2) (d1 := 5) (d2 := 7) (d3 := 11)
      hInput (by native_decide)
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 301, pmFinal 302, pmFinal 303] 1 [2, 15, 7, 11] [2, 5, 7, 11]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa only [List.map, List.length_cons, List.length_nil] using htransport
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#print axioms segment_000000
end
end SyntheticSoftmaxDim1

namespace SyntheticSoftmaxDim2
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_softmax", ins := [100], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_softmax", ins := [201], outs := [301] }, { rank := 1, op := "OpName.FW_softmax", ins := [202], outs := [302] }, { rank := 2, op := "OpName.FW_softmax", ins := [203], outs := [303] }] }
def fact_in : RelationFact := .sharded 100 [201, 202, 203] 2 [2, 5, 21, 11] [2, 5, 7, 11]
def fact_out : RelationFact := .sharded 110 [301, 302, 303] 2 [2, 5, 21, 11] [2, 5, 7, 11]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_softmax", ins := [100], outs := [110] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_softmax", ins := [201], outs := [301] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_softmax", ins := [202], outs := [302] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_softmax", ins := [203], outs := [303] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticSoftmaxDim2.gSM SyntheticSoftmaxDim2.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim2.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim2.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hInput : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 201, pmStore 202, pmStore 203] 2 [2, 5, 21, 11] [2, 5, 7, 11] at hInput
    have hSmWriter : smFinal 110 = fw_softmax (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim2.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim2.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => fw_softmax (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim2.gSM t 0 100 110 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim2.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 301 = fw_softmax (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim2.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim2.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 301 (fun t => fw_softmax (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim2.gPM t 0 201 301 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim2.gPM (pmNodes.take 0) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 302 = fw_softmax (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim2.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim2.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 302 (fun t => fw_softmax (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim2.gPM t 1 202 302 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim2.gPM (pmNodes.take 1) pmStore 202 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 303 = fw_softmax (pmStore 203) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticSoftmaxDim2.gPM) pmStore) 303 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticSoftmaxDim2.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 303 (fun t => fw_softmax (t 203)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_softmax_out_g43 SyntheticSoftmaxDim2.gPM t 2 203 303 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticSoftmaxDim2.gPM (pmNodes.take 2) pmStore 203 (by native_decide) (by native_decide)]
    have htransport := ShardedRel.fw_softmax_dim2_rank4
      (d0 := 2) (d1 := 5) (d2 := 7) (d3 := 11)
      hInput (by native_decide)
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 301, pmFinal 302, pmFinal 303] 2 [2, 5, 21, 11] [2, 5, 7, 11]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa only [List.map, List.length_cons, List.length_nil] using htransport
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#print axioms segment_000000
end
end SyntheticSoftmaxDim2

end TrainVerify.Denote
