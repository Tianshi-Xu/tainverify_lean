import denote.KRankTranspose23Extra

namespace TrainVerify.Denote
open RelationCompiler

namespace SyntheticTranspose23Dim2To3
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }, { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }, { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 2 [2, 4, 9, 5] [2, 4, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 3 [2, 4, 5, 9] [2, 4, 5, 3]
def state_pre : RelationState where
  facts := [fact_in]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

-- One ordered SM fold and one ordered PM fold for an atomic tuple of FW_transpose transitions.
private def segment_000000_sm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node_0]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticTranspose23Dim2To3.gSM SyntheticTranspose23Dim2To3.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin0 : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 2 [2, 4, 3 * [pmStore 200, pmStore 201, pmStore 202].length, 5] [2, 4, 3, 5] at hin0
    have hSmWriter0 : smFinal 110 = transposeAxes 2 3 (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node_0] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim2To3.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node_0 110 (fun t => transposeAxes 2 3 (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim2To3.gSM t 0 100 110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim2To3.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0_0 : pmFinal 300 = transposeAxes 2 3 (pmStore 200) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim2To3.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 300 (fun t => transposeAxes 2 3 (t 200)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim2To3.gPM t 0 200 300 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim2To3.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
    have hPmWriter0_1 : pmFinal 301 = transposeAxes 2 3 (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim2To3.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 301 (fun t => transposeAxes 2 3 (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim2To3.gPM t 1 201 301 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim2To3.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter0_2 : pmFinal 302 = transposeAxes 2 3 (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim2To3.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 302 (fun t => transposeAxes 2 3 (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim2To3.gPM t 2 202 302 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim2To3.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide)]
    have htransport0 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4 hin0
    have hout0 : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 3 [2, 4, 5, 9] [2, 4, 5, 3]
      rw [hSmWriter0, hPmWriter0_0, hPmWriter0_1, hPmWriter0_2]
      simpa using htransport0
    exact RelationState.Holds.mono_insert hframe hout0 (by native_decide)

#print axioms segment_000000
end
end SyntheticTranspose23Dim2To3

namespace SyntheticTranspose23Dim3To2
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }, { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }, { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 3 [2, 4, 3, 15] [2, 4, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 2 [2, 4, 15, 3] [2, 4, 5, 3]
def state_pre : RelationState where
  facts := [fact_in]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

-- One ordered SM fold and one ordered PM fold for an atomic tuple of FW_transpose transitions.
private def segment_000000_sm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node_0]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticTranspose23Dim3To2.gSM SyntheticTranspose23Dim3To2.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin0 : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 3 [2, 4, 3, 5 * [pmStore 200, pmStore 201, pmStore 202].length] [2, 4, 3, 5] at hin0
    have hSmWriter0 : smFinal 110 = transposeAxes 2 3 (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node_0] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim3To2.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node_0 110 (fun t => transposeAxes 2 3 (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim3To2.gSM t 0 100 110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim3To2.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0_0 : pmFinal 300 = transposeAxes 2 3 (pmStore 200) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim3To2.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 300 (fun t => transposeAxes 2 3 (t 200)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim3To2.gPM t 0 200 300 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim3To2.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
    have hPmWriter0_1 : pmFinal 301 = transposeAxes 2 3 (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim3To2.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 301 (fun t => transposeAxes 2 3 (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim3To2.gPM t 1 201 301 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim3To2.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter0_2 : pmFinal 302 = transposeAxes 2 3 (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim3To2.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 302 (fun t => transposeAxes 2 3 (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim3To2.gPM t 2 202 302 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim3To2.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide)]
    have htransport0 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4 hin0
    have hout0 : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 2 [2, 4, 15, 3] [2, 4, 5, 3]
      rw [hSmWriter0, hPmWriter0_0, hPmWriter0_1, hPmWriter0_2]
      simpa using htransport0
    exact RelationState.Holds.mono_insert hframe hout0 (by native_decide)

#print axioms segment_000000
end
end SyntheticTranspose23Dim3To2

namespace SyntheticTranspose23Dim1
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }, { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }, { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 7, 5] [2, 4, 7, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 12, 5, 7] [2, 4, 5, 7]
def state_pre : RelationState where
  facts := [fact_in]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

-- One ordered SM fold and one ordered PM fold for an atomic tuple of FW_transpose transitions.
private def segment_000000_sm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node_0]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticTranspose23Dim1.gSM SyntheticTranspose23Dim1.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin0 : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 4 * [pmStore 200, pmStore 201, pmStore 202].length, 7, 5] [2, 4, 7, 5] at hin0
    have hSmWriter0 : smFinal 110 = transposeAxes 2 3 (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node_0] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim1.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node_0 110 (fun t => transposeAxes 2 3 (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim1.gSM t 0 100 110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim1.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0_0 : pmFinal 300 = transposeAxes 2 3 (pmStore 200) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim1.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 300 (fun t => transposeAxes 2 3 (t 200)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim1.gPM t 0 200 300 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim1.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
    have hPmWriter0_1 : pmFinal 301 = transposeAxes 2 3 (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim1.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 301 (fun t => transposeAxes 2 3 (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim1.gPM t 1 201 301 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim1.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter0_2 : pmFinal 302 = transposeAxes 2 3 (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim1.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 302 (fun t => transposeAxes 2 3 (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim1.gPM t 2 202 302 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim1.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide)]
    have htransport0 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4 hin0
    have hout0 : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 12, 5, 7] [2, 4, 5, 7]
      rw [hSmWriter0, hPmWriter0_0, hPmWriter0_1, hPmWriter0_2]
      simpa using htransport0
    exact RelationState.Holds.mono_insert hframe hout0 (by native_decide)

#print axioms segment_000000
end
end SyntheticTranspose23Dim1
namespace SyntheticTransposeRealSegment69
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [1000], outs := [1010], params := [1, 2] }, { rank := 0, op := "OpName.FW_transpose", ins := [1100], outs := [1110], params := [1, 2] }] }
def gPM : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [2000], outs := [3000], params := [1, 2] }, { rank := 1, op := "OpName.FW_transpose", ins := [2001], outs := [3001], params := [1, 2] }, { rank := 2, op := "OpName.FW_transpose", ins := [2002], outs := [3002], params := [1, 2] }, { rank := 3, op := "OpName.FW_transpose", ins := [2003], outs := [3003], params := [1, 2] }, { rank := 0, op := "OpName.FW_transpose", ins := [2100], outs := [3100], params := [1, 2] }, { rank := 1, op := "OpName.FW_transpose", ins := [2101], outs := [3101], params := [1, 2] }, { rank := 2, op := "OpName.FW_transpose", ins := [2102], outs := [3102], params := [1, 2] }, { rank := 3, op := "OpName.FW_transpose", ins := [2103], outs := [3103], params := [1, 2] }] }

def fact_in_0 : RelationFact := .sharded 1000 [2000, 2001, 2002, 2003] 3 [1, 12, 1024, 64] [1, 12, 1024, 16]
def fact_out_0 : RelationFact := .sharded 1010 [3000, 3001, 3002, 3003] 3 [1, 1024, 12, 64] [1, 1024, 12, 16]
def fact_in_1 : RelationFact := .sharded 1100 [2100, 2101, 2102, 2103] 2 [1, 12, 1024, 64] [1, 12, 256, 64]
def fact_out_1 : RelationFact := .sharded 1110 [3100, 3101, 3102, 3103] 1 [1, 1024, 12, 64] [1, 256, 12, 64]
def state_pre : RelationState where
  facts := [fact_in_0, fact_in_1]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out_0, fact_out_1]
  nonempty := by decide

-- One ordered SM fold and one ordered PM fold for an atomic tuple of FW_transpose transitions.
private def segment_000069_sm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [1000], outs := [1010], params := [1, 2] }
private def segment_000069_sm_node_1 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [1100], outs := [1110], params := [1, 2] }
private def segment_000069_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [2000], outs := [3000], params := [1, 2] }
private def segment_000069_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [2001], outs := [3001], params := [1, 2] }
private def segment_000069_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [2002], outs := [3002], params := [1, 2] }
private def segment_000069_pm_node_3 : NodeDecl := { rank := 3, op := "OpName.FW_transpose", ins := [2003], outs := [3003], params := [1, 2] }
private def segment_000069_pm_node_4 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [2100], outs := [3100], params := [1, 2] }
private def segment_000069_pm_node_5 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [2101], outs := [3101], params := [1, 2] }
private def segment_000069_pm_node_6 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [2102], outs := [3102], params := [1, 2] }
private def segment_000069_pm_node_7 : NodeDecl := { rank := 3, op := "OpName.FW_transpose", ins := [2103], outs := [3103], params := [1, 2] }
private def segment_000069_sm_nodes : List NodeDecl := [segment_000069_sm_node_0, segment_000069_sm_node_1]
private def segment_000069_pm_nodes : List NodeDecl := [segment_000069_pm_node_0, segment_000069_pm_node_1, segment_000069_pm_node_2, segment_000069_pm_node_3, segment_000069_pm_node_4, segment_000069_pm_node_5, segment_000069_pm_node_6, segment_000069_pm_node_7]

private def segment_000069 :
    ClosedDepSegmentCertificate SyntheticTransposeRealSegment69.gSM SyntheticTransposeRealSegment69.gPM state_pre state_post where
  smNodes := segment_000069_sm_nodes
  pmNodes := segment_000069_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000069_sm_nodes
    let pmNodes : List NodeDecl := segment_000069_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin0 : fact_in_0.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 1000) [pmStore 2000, pmStore 2001, pmStore 2002, pmStore 2003] 3 [1, 12, 1024, 16 * [pmStore 2000, pmStore 2001, pmStore 2002, pmStore 2003].length] [1, 12, 1024, 16] at hin0
    have hin1 : fact_in_1.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 1100) [pmStore 2100, pmStore 2101, pmStore 2102, pmStore 2103] 2 [1, 12, 256 * [pmStore 2100, pmStore 2101, pmStore 2102, pmStore 2103].length, 64] [1, 12, 256, 64] at hin1
    have hSmWriter0 : smFinal 1010 = transposeAxes 1 2 (smStore 1000) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gSM) smStore) 1010 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000069_sm_node_0] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000069_sm_node_0 1010 (fun t => transposeAxes 1 2 (t 1000)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gSM t 0 1000 1010 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gSM (smNodes.take 0) smStore 1000 (by native_decide) (by native_decide)]
    have hPmWriter0_0 : pmFinal 3000 = transposeAxes 1 2 (pmStore 2000) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3000 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000069_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000069_pm_node_0 3000 (fun t => transposeAxes 1 2 (t 2000)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 0 2000 3000 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 0) pmStore 2000 (by native_decide) (by native_decide)]
    have hPmWriter0_1 : pmFinal 3001 = transposeAxes 1 2 (pmStore 2001) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3001 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000069_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000069_pm_node_1 3001 (fun t => transposeAxes 1 2 (t 2001)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 1 2001 3001 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 1) pmStore 2001 (by native_decide) (by native_decide)]
    have hPmWriter0_2 : pmFinal 3002 = transposeAxes 1 2 (pmStore 2002) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3002 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000069_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000069_pm_node_2 3002 (fun t => transposeAxes 1 2 (t 2002)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 2 2002 3002 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 2) pmStore 2002 (by native_decide) (by native_decide)]
    have hPmWriter0_3 : pmFinal 3003 = transposeAxes 1 2 (pmStore 2003) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3003 = _
      rw [show pmNodes = pmNodes.take 3 ++ [segment_000069_pm_node_3] ++ pmNodes.drop 4 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 3) (pmNodes.drop 4)
        segment_000069_pm_node_3 3003 (fun t => transposeAxes 1 2 (t 2003)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 3 2003 3003 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 3) pmStore 2003 (by native_decide) (by native_decide)]
    have hSmWriter1 : smFinal 1110 = transposeAxes 1 2 (smStore 1100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gSM) smStore) 1110 = _
      rw [show smNodes = smNodes.take 1 ++ [segment_000069_sm_node_1] ++ smNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gSM smStore (smNodes.take 1) (smNodes.drop 2)
        segment_000069_sm_node_1 1110 (fun t => transposeAxes 1 2 (t 1100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gSM t 0 1100 1110 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gSM (smNodes.take 1) smStore 1100 (by native_decide) (by native_decide)]
    have hPmWriter1_0 : pmFinal 3100 = transposeAxes 1 2 (pmStore 2100) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3100 = _
      rw [show pmNodes = pmNodes.take 4 ++ [segment_000069_pm_node_4] ++ pmNodes.drop 5 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 4) (pmNodes.drop 5)
        segment_000069_pm_node_4 3100 (fun t => transposeAxes 1 2 (t 2100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 0 2100 3100 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 4) pmStore 2100 (by native_decide) (by native_decide)]
    have hPmWriter1_1 : pmFinal 3101 = transposeAxes 1 2 (pmStore 2101) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3101 = _
      rw [show pmNodes = pmNodes.take 5 ++ [segment_000069_pm_node_5] ++ pmNodes.drop 6 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 5) (pmNodes.drop 6)
        segment_000069_pm_node_5 3101 (fun t => transposeAxes 1 2 (t 2101)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 1 2101 3101 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 5) pmStore 2101 (by native_decide) (by native_decide)]
    have hPmWriter1_2 : pmFinal 3102 = transposeAxes 1 2 (pmStore 2102) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3102 = _
      rw [show pmNodes = pmNodes.take 6 ++ [segment_000069_pm_node_6] ++ pmNodes.drop 7 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 6) (pmNodes.drop 7)
        segment_000069_pm_node_6 3102 (fun t => transposeAxes 1 2 (t 2102)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 2 2102 3102 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 6) pmStore 2102 (by native_decide) (by native_decide)]
    have hPmWriter1_3 : pmFinal 3103 = transposeAxes 1 2 (pmStore 2103) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment69.gPM) pmStore) 3103 = _
      rw [show pmNodes = pmNodes.take 7 ++ [segment_000069_pm_node_7] ++ pmNodes.drop 8 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment69.gPM pmStore (pmNodes.take 7) (pmNodes.drop 8)
        segment_000069_pm_node_7 3103 (fun t => transposeAxes 1 2 (t 2103)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment69.gPM t 3 2103 3103 1 2
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment69.gPM (pmNodes.take 7) pmStore 2103 (by native_decide) (by native_decide)]
    have htransport0 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4 hin0
    have hout0 : fact_out_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 1010) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 3 [1, 1024, 12, 64] [1, 1024, 12, 16]
      rw [hSmWriter0, hPmWriter0_0, hPmWriter0_1, hPmWriter0_2, hPmWriter0_3]
      simpa using htransport0
    have htransport1 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4 hin1
    have hout1 : fact_out_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 1110) [pmFinal 3100, pmFinal 3101, pmFinal 3102, pmFinal 3103] 1 [1, 1024, 12, 64] [1, 256, 12, 64]
      rw [hSmWriter1, hPmWriter1_0, hPmWriter1_1, hPmWriter1_2, hPmWriter1_3]
      simpa using htransport1
    let segment_000069_publish_1 : RelationState := { facts := fact_out_0 :: state_pre.facts, nonempty := by simp }
    have hpublished1 : segment_000069_publish_1.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert hframe hout0 (by native_decide)
    exact RelationState.Holds.mono_insert hpublished1 hout1 (by native_decide)

#print axioms segment_000069
end
end SyntheticTransposeRealSegment69
namespace SyntheticTransposeRealSegment113
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [1000], outs := [1010], params := [2, 3] }, { rank := 0, op := "OpName.FW_transpose", ins := [1100], outs := [1110], params := [2, 3] }, { rank := 0, op := "OpName.FW_transpose", ins := [1200], outs := [1210], params := [2, 3] }] }
def gPM : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_transpose", ins := [2000], outs := [3000], params := [2, 3] }, { rank := 1, op := "OpName.FW_transpose", ins := [2001], outs := [3001], params := [2, 3] }, { rank := 2, op := "OpName.FW_transpose", ins := [2002], outs := [3002], params := [2, 3] }, { rank := 3, op := "OpName.FW_transpose", ins := [2003], outs := [3003], params := [2, 3] }, { rank := 0, op := "OpName.FW_transpose", ins := [2100], outs := [3100], params := [2, 3] }, { rank := 1, op := "OpName.FW_transpose", ins := [2101], outs := [3101], params := [2, 3] }, { rank := 2, op := "OpName.FW_transpose", ins := [2102], outs := [3102], params := [2, 3] }, { rank := 3, op := "OpName.FW_transpose", ins := [2103], outs := [3103], params := [2, 3] }, { rank := 0, op := "OpName.FW_transpose", ins := [2200], outs := [3200], params := [2, 3] }, { rank := 1, op := "OpName.FW_transpose", ins := [2201], outs := [3201], params := [2, 3] }, { rank := 2, op := "OpName.FW_transpose", ins := [2202], outs := [3202], params := [2, 3] }, { rank := 3, op := "OpName.FW_transpose", ins := [2203], outs := [3203], params := [2, 3] }] }

def fact_in_0 : RelationFact := .sharded 1000 [2000, 2001, 2002, 2003] 2 [2, 4, 12, 5] [2, 4, 3, 5]
def fact_out_0 : RelationFact := .sharded 1010 [3000, 3001, 3002, 3003] 3 [2, 4, 5, 12] [2, 4, 5, 3]
def fact_in_1 : RelationFact := .sharded 1100 [2100, 2101, 2102, 2103] 3 [2, 4, 3, 20] [2, 4, 3, 5]
def fact_out_1 : RelationFact := .sharded 1110 [3100, 3101, 3102, 3103] 2 [2, 4, 20, 3] [2, 4, 5, 3]
def fact_in_2 : RelationFact := .sharded 1200 [2200, 2201, 2202, 2203] 1 [2, 16, 7, 5] [2, 4, 7, 5]
def fact_out_2 : RelationFact := .sharded 1210 [3200, 3201, 3202, 3203] 1 [2, 16, 5, 7] [2, 4, 5, 7]
def state_pre : RelationState where
  facts := [fact_in_0, fact_in_1, fact_in_2]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out_0, fact_out_1, fact_out_2]
  nonempty := by decide

-- One ordered SM fold and one ordered PM fold for an atomic tuple of FW_transpose transitions.
private def segment_000113_sm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [1000], outs := [1010], params := [2, 3] }
private def segment_000113_sm_node_1 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [1100], outs := [1110], params := [2, 3] }
private def segment_000113_sm_node_2 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [1200], outs := [1210], params := [2, 3] }
private def segment_000113_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [2000], outs := [3000], params := [2, 3] }
private def segment_000113_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [2001], outs := [3001], params := [2, 3] }
private def segment_000113_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [2002], outs := [3002], params := [2, 3] }
private def segment_000113_pm_node_3 : NodeDecl := { rank := 3, op := "OpName.FW_transpose", ins := [2003], outs := [3003], params := [2, 3] }
private def segment_000113_pm_node_4 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [2100], outs := [3100], params := [2, 3] }
private def segment_000113_pm_node_5 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [2101], outs := [3101], params := [2, 3] }
private def segment_000113_pm_node_6 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [2102], outs := [3102], params := [2, 3] }
private def segment_000113_pm_node_7 : NodeDecl := { rank := 3, op := "OpName.FW_transpose", ins := [2103], outs := [3103], params := [2, 3] }
private def segment_000113_pm_node_8 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [2200], outs := [3200], params := [2, 3] }
private def segment_000113_pm_node_9 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [2201], outs := [3201], params := [2, 3] }
private def segment_000113_pm_node_10 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [2202], outs := [3202], params := [2, 3] }
private def segment_000113_pm_node_11 : NodeDecl := { rank := 3, op := "OpName.FW_transpose", ins := [2203], outs := [3203], params := [2, 3] }
private def segment_000113_sm_nodes : List NodeDecl := [segment_000113_sm_node_0, segment_000113_sm_node_1, segment_000113_sm_node_2]
private def segment_000113_pm_nodes : List NodeDecl := [segment_000113_pm_node_0, segment_000113_pm_node_1, segment_000113_pm_node_2, segment_000113_pm_node_3, segment_000113_pm_node_4, segment_000113_pm_node_5, segment_000113_pm_node_6, segment_000113_pm_node_7, segment_000113_pm_node_8, segment_000113_pm_node_9, segment_000113_pm_node_10, segment_000113_pm_node_11]

private def segment_000113 :
    ClosedDepSegmentCertificate SyntheticTransposeRealSegment113.gSM SyntheticTransposeRealSegment113.gPM state_pre state_post where
  smNodes := segment_000113_sm_nodes
  pmNodes := segment_000113_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000113_sm_nodes
    let pmNodes : List NodeDecl := segment_000113_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin0 : fact_in_0.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 1000) [pmStore 2000, pmStore 2001, pmStore 2002, pmStore 2003] 2 [2, 4, 3 * [pmStore 2000, pmStore 2001, pmStore 2002, pmStore 2003].length, 5] [2, 4, 3, 5] at hin0
    have hin1 : fact_in_1.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 1100) [pmStore 2100, pmStore 2101, pmStore 2102, pmStore 2103] 3 [2, 4, 3, 5 * [pmStore 2100, pmStore 2101, pmStore 2102, pmStore 2103].length] [2, 4, 3, 5] at hin1
    have hin2 : fact_in_2.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 1200) [pmStore 2200, pmStore 2201, pmStore 2202, pmStore 2203] 1 [2, 4 * [pmStore 2200, pmStore 2201, pmStore 2202, pmStore 2203].length, 7, 5] [2, 4, 7, 5] at hin2
    have hSmWriter0 : smFinal 1010 = transposeAxes 2 3 (smStore 1000) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gSM) smStore) 1010 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000113_sm_node_0] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000113_sm_node_0 1010 (fun t => transposeAxes 2 3 (t 1000)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gSM t 0 1000 1010 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gSM (smNodes.take 0) smStore 1000 (by native_decide) (by native_decide)]
    have hPmWriter0_0 : pmFinal 3000 = transposeAxes 2 3 (pmStore 2000) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3000 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000113_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000113_pm_node_0 3000 (fun t => transposeAxes 2 3 (t 2000)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 0 2000 3000 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 0) pmStore 2000 (by native_decide) (by native_decide)]
    have hPmWriter0_1 : pmFinal 3001 = transposeAxes 2 3 (pmStore 2001) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3001 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000113_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000113_pm_node_1 3001 (fun t => transposeAxes 2 3 (t 2001)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 1 2001 3001 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 1) pmStore 2001 (by native_decide) (by native_decide)]
    have hPmWriter0_2 : pmFinal 3002 = transposeAxes 2 3 (pmStore 2002) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3002 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000113_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000113_pm_node_2 3002 (fun t => transposeAxes 2 3 (t 2002)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 2 2002 3002 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 2) pmStore 2002 (by native_decide) (by native_decide)]
    have hPmWriter0_3 : pmFinal 3003 = transposeAxes 2 3 (pmStore 2003) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3003 = _
      rw [show pmNodes = pmNodes.take 3 ++ [segment_000113_pm_node_3] ++ pmNodes.drop 4 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 3) (pmNodes.drop 4)
        segment_000113_pm_node_3 3003 (fun t => transposeAxes 2 3 (t 2003)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 3 2003 3003 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 3) pmStore 2003 (by native_decide) (by native_decide)]
    have hSmWriter1 : smFinal 1110 = transposeAxes 2 3 (smStore 1100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gSM) smStore) 1110 = _
      rw [show smNodes = smNodes.take 1 ++ [segment_000113_sm_node_1] ++ smNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gSM smStore (smNodes.take 1) (smNodes.drop 2)
        segment_000113_sm_node_1 1110 (fun t => transposeAxes 2 3 (t 1100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gSM t 0 1100 1110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gSM (smNodes.take 1) smStore 1100 (by native_decide) (by native_decide)]
    have hPmWriter1_0 : pmFinal 3100 = transposeAxes 2 3 (pmStore 2100) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3100 = _
      rw [show pmNodes = pmNodes.take 4 ++ [segment_000113_pm_node_4] ++ pmNodes.drop 5 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 4) (pmNodes.drop 5)
        segment_000113_pm_node_4 3100 (fun t => transposeAxes 2 3 (t 2100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 0 2100 3100 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 4) pmStore 2100 (by native_decide) (by native_decide)]
    have hPmWriter1_1 : pmFinal 3101 = transposeAxes 2 3 (pmStore 2101) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3101 = _
      rw [show pmNodes = pmNodes.take 5 ++ [segment_000113_pm_node_5] ++ pmNodes.drop 6 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 5) (pmNodes.drop 6)
        segment_000113_pm_node_5 3101 (fun t => transposeAxes 2 3 (t 2101)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 1 2101 3101 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 5) pmStore 2101 (by native_decide) (by native_decide)]
    have hPmWriter1_2 : pmFinal 3102 = transposeAxes 2 3 (pmStore 2102) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3102 = _
      rw [show pmNodes = pmNodes.take 6 ++ [segment_000113_pm_node_6] ++ pmNodes.drop 7 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 6) (pmNodes.drop 7)
        segment_000113_pm_node_6 3102 (fun t => transposeAxes 2 3 (t 2102)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 2 2102 3102 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 6) pmStore 2102 (by native_decide) (by native_decide)]
    have hPmWriter1_3 : pmFinal 3103 = transposeAxes 2 3 (pmStore 2103) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3103 = _
      rw [show pmNodes = pmNodes.take 7 ++ [segment_000113_pm_node_7] ++ pmNodes.drop 8 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 7) (pmNodes.drop 8)
        segment_000113_pm_node_7 3103 (fun t => transposeAxes 2 3 (t 2103)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 3 2103 3103 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 7) pmStore 2103 (by native_decide) (by native_decide)]
    have hSmWriter2 : smFinal 1210 = transposeAxes 2 3 (smStore 1200) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gSM) smStore) 1210 = _
      rw [show smNodes = smNodes.take 2 ++ [segment_000113_sm_node_2] ++ smNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gSM smStore (smNodes.take 2) (smNodes.drop 3)
        segment_000113_sm_node_2 1210 (fun t => transposeAxes 2 3 (t 1200)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gSM t 0 1200 1210 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gSM (smNodes.take 2) smStore 1200 (by native_decide) (by native_decide)]
    have hPmWriter2_0 : pmFinal 3200 = transposeAxes 2 3 (pmStore 2200) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3200 = _
      rw [show pmNodes = pmNodes.take 8 ++ [segment_000113_pm_node_8] ++ pmNodes.drop 9 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 8) (pmNodes.drop 9)
        segment_000113_pm_node_8 3200 (fun t => transposeAxes 2 3 (t 2200)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 0 2200 3200 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 8) pmStore 2200 (by native_decide) (by native_decide)]
    have hPmWriter2_1 : pmFinal 3201 = transposeAxes 2 3 (pmStore 2201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3201 = _
      rw [show pmNodes = pmNodes.take 9 ++ [segment_000113_pm_node_9] ++ pmNodes.drop 10 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 9) (pmNodes.drop 10)
        segment_000113_pm_node_9 3201 (fun t => transposeAxes 2 3 (t 2201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 1 2201 3201 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 9) pmStore 2201 (by native_decide) (by native_decide)]
    have hPmWriter2_2 : pmFinal 3202 = transposeAxes 2 3 (pmStore 2202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3202 = _
      rw [show pmNodes = pmNodes.take 10 ++ [segment_000113_pm_node_10] ++ pmNodes.drop 11 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 10) (pmNodes.drop 11)
        segment_000113_pm_node_10 3202 (fun t => transposeAxes 2 3 (t 2202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 2 2202 3202 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 10) pmStore 2202 (by native_decide) (by native_decide)]
    have hPmWriter2_3 : pmFinal 3203 = transposeAxes 2 3 (pmStore 2203) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticTransposeRealSegment113.gPM) pmStore) 3203 = _
      rw [show pmNodes = pmNodes.take 11 ++ [segment_000113_pm_node_11] ++ pmNodes.drop 12 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTransposeRealSegment113.gPM pmStore (pmNodes.take 11) (pmNodes.drop 12)
        segment_000113_pm_node_11 3203 (fun t => transposeAxes 2 3 (t 2203)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTransposeRealSegment113.gPM t 3 2203 3203 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTransposeRealSegment113.gPM (pmNodes.take 11) pmStore 2203 (by native_decide) (by native_decide)]
    have htransport0 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4 hin0
    have hout0 : fact_out_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 1010) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 3 [2, 4, 5, 12] [2, 4, 5, 3]
      rw [hSmWriter0, hPmWriter0_0, hPmWriter0_1, hPmWriter0_2, hPmWriter0_3]
      simpa using htransport0
    have htransport1 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4 hin1
    have hout1 : fact_out_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 1110) [pmFinal 3100, pmFinal 3101, pmFinal 3102, pmFinal 3103] 2 [2, 4, 20, 3] [2, 4, 5, 3]
      rw [hSmWriter1, hPmWriter1_0, hPmWriter1_1, hPmWriter1_2, hPmWriter1_3]
      simpa using htransport1
    have htransport2 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4 hin2
    have hout2 : fact_out_2.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 1210) [pmFinal 3200, pmFinal 3201, pmFinal 3202, pmFinal 3203] 1 [2, 16, 5, 7] [2, 4, 5, 7]
      rw [hSmWriter2, hPmWriter2_0, hPmWriter2_1, hPmWriter2_2, hPmWriter2_3]
      simpa using htransport2
    let segment_000113_publish_1 : RelationState := { facts := fact_out_0 :: state_pre.facts, nonempty := by simp }
    have hpublished1 : segment_000113_publish_1.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert hframe hout0 (by native_decide)
    let segment_000113_publish_2 : RelationState := { facts := fact_out_0 :: fact_out_1 :: state_pre.facts, nonempty := by simp }
    have hpublished2 : segment_000113_publish_2.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert hpublished1 hout1 (by native_decide)
    exact RelationState.Holds.mono_insert hpublished2 hout2 (by native_decide)

#print axioms segment_000113
end
end SyntheticTransposeRealSegment113

end TrainVerify.Denote
