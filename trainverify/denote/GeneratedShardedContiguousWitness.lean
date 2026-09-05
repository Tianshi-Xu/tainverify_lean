import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticContiguous
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [200], outs := [300] }, { rank := 1, op := "OpName.FW_contiguous", ins := [201], outs := [301] }, { rank := 2, op := "OpName.FW_contiguous", ins := [202], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 4] [2, 3, 4]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 4] [2, 3, 4]
def state_pre : RelationState where
  facts := [fact_in]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_contiguous", ins := [200], outs := [300] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_contiguous", ins := [201], outs := [301] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_contiguous", ins := [202], outs := [302] }
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [200], outs := [300] }, { rank := 1, op := "OpName.FW_contiguous", ins := [201], outs := [301] }, { rank := 2, op := "OpName.FW_contiguous", ins := [202], outs := [302] }]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticContiguous.gSM SyntheticContiguous.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticContiguous.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticContiguous.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 9, 4] [2, 3, 4] at hin
    have hSmWriter : smFinal 110 = fw_contiguous (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticContiguous.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContiguous.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => fw_contiguous (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_sm_node]
          exact applyNode_fw_contiguous_out SyntheticContiguous.gSM t 0 100 110
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContiguous.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = fw_contiguous (pmStore 200) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticContiguous.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContiguous.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 300 (fun t => fw_contiguous (t 200)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_pm_node_0]
          exact applyNode_fw_contiguous_out SyntheticContiguous.gPM t 0 200 300
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContiguous.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 301 = fw_contiguous (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticContiguous.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContiguous.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 301 (fun t => fw_contiguous (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_pm_node_1]
          exact applyNode_fw_contiguous_out SyntheticContiguous.gPM t 1 201 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContiguous.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 302 = fw_contiguous (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticContiguous.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContiguous.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 302 (fun t => fw_contiguous (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_pm_node_2]
          exact applyNode_fw_contiguous_out SyntheticContiguous.gPM t 2 202 302
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContiguous.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide)]
    have htransport := ShardedRel.fw_contiguous hin
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 9, 4] [2, 3, 4]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa only [List.map] using htransport
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
end SyntheticContiguous
end TrainVerify.Denote
