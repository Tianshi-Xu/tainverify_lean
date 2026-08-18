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

-- FW_transpose with literal [d0,d1] parameters is interpreted by transposeAxes d0 d1.
private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
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
    have hin : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 2 [2, 4, 3 * [pmStore 200, pmStore 201, pmStore 202].length, 5] [2, 4, 3, 5] at hin
    have hSmWriter : smFinal 110 = transposeAxes 2 3 (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim2To3.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim2To3.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => transposeAxes 2 3 (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim2To3.gSM t 0 100 110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim2To3.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = transposeAxes 2 3 (pmStore 200) := by
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
    have hPmWriter1 : pmFinal 301 = transposeAxes 2 3 (pmStore 201) := by
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
    have hPmWriter2 : pmFinal 302 = transposeAxes 2 3 (pmStore 202) := by
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
    have htransport := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4 hin
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 3 [2, 4, 5, 9] [2, 4, 5, 3]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa using htransport
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

-- FW_transpose with literal [d0,d1] parameters is interpreted by transposeAxes d0 d1.
private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
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
    have hin : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 3 [2, 4, 3, 5 * [pmStore 200, pmStore 201, pmStore 202].length] [2, 4, 3, 5] at hin
    have hSmWriter : smFinal 110 = transposeAxes 2 3 (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim3To2.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim3To2.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => transposeAxes 2 3 (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim3To2.gSM t 0 100 110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim3To2.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = transposeAxes 2 3 (pmStore 200) := by
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
    have hPmWriter1 : pmFinal 301 = transposeAxes 2 3 (pmStore 201) := by
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
    have hPmWriter2 : pmFinal 302 = transposeAxes 2 3 (pmStore 202) := by
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
    have htransport := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4 hin
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 2 [2, 4, 15, 3] [2, 4, 5, 3]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa using htransport
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

-- FW_transpose with literal [d0,d1] parameters is interpreted by transposeAxes d0 d1.
private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
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
    have hin : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 4 * [pmStore 200, pmStore 201, pmStore 202].length, 7, 5] [2, 4, 7, 5] at hin
    have hSmWriter : smFinal 110 = transposeAxes 2 3 (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticTranspose23Dim1.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticTranspose23Dim1.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => transposeAxes 2 3 (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_transposeAxes_out SyntheticTranspose23Dim1.gSM t 0 100 110 2 3
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticTranspose23Dim1.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = transposeAxes 2 3 (pmStore 200) := by
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
    have hPmWriter1 : pmFinal 301 = transposeAxes 2 3 (pmStore 201) := by
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
    have hPmWriter2 : pmFinal 302 = transposeAxes 2 3 (pmStore 202) := by
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
    have htransport := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4 hin
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 12, 5, 7] [2, 4, 5, 7]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa using htransport
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
end SyntheticTranspose23Dim1

end TrainVerify.Denote
