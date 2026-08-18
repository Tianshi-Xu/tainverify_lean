import denote.KRankMatmulContractionReduction

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticContraction
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_matmul", ins := [100, 101], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_matmul", ins := [200, 210], outs := [300] }, { rank := 1, op := "OpName.FW_matmul", ins := [201, 211], outs := [301] }, { rank := 2, op := "OpName.FW_matmul", ins := [202, 212], outs := [302] }] }

def fact_x : RelationFact := .sharded 100 [200, 201, 202] 3 [2, 4, 5, 21] [2, 4, 5, 7]
def fact_y : RelationFact := .sharded 101 [210, 211, 212] 2 [2, 4, 21, 11] [2, 4, 7, 11]
def fact_out : RelationFact := .reduction 110 [300, 301, 302] [2, 4, 5, 11]
def state_pre : RelationState where
  facts := [fact_x, fact_y]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_matmul", ins := [100, 101], outs := [110] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_matmul", ins := [200, 210], outs := [300] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_matmul", ins := [201, 211], outs := [301] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_matmul", ins := [202, 212], outs := [302] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticContraction.gSM SyntheticContraction.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticContraction.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticContraction.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hX : fact_x.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 3 [2, 4, 5, 21] [2, 4, 5, 7] at hX
    have hY : fact_y.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 101) [pmStore 210, pmStore 211, pmStore 212] 2 [2, 4, 21, 11] [2, 4, 7, 11] at hY
    have hSmWriter : smFinal 110 = fw_matmul (smStore 100) (smStore 101) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticContraction.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContraction.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => fw_matmul (t 100) (t 101)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_matmul_out SyntheticContraction.gSM t 0 100 101 110
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gSM (smNodes.take 0) smStore 101 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = fw_matmul (pmStore 200) (pmStore 210) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticContraction.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContraction.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 300 (fun t => fw_matmul (t 200) (t 210)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_matmul_out SyntheticContraction.gPM t 0 200 210 300
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gPM (pmNodes.take 0) pmStore 210 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 301 = fw_matmul (pmStore 201) (pmStore 211) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticContraction.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContraction.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 301 (fun t => fw_matmul (t 201) (t 211)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_matmul_out SyntheticContraction.gPM t 1 201 211 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gPM (pmNodes.take 1) pmStore 211 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 302 = fw_matmul (pmStore 202) (pmStore 212) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticContraction.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticContraction.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 302 (fun t => fw_matmul (t 202) (t 212)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_matmul_out SyntheticContraction.gPM t 2 202 212 302
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticContraction.gPM (pmNodes.take 2) pmStore 212 (by native_decide) (by native_decide)]
    have htransport := ShardedRel.fw_matmul_contraction_axis_rank4
      (x := smStore 100) (y := smStore 101)
      (xs := [pmStore 200, pmStore 201, pmStore 202]) (ys := [pmStore 210, pmStore 211, pmStore 212]) (K := [pmStore 200, pmStore 201, pmStore 202].length)
      (b := 2) (h := 4) (q := 5) (k := 7) (m := 11)
      hX hY (by simp) (by native_decide) (by native_decide) (by native_decide)
      (by simp) (by simp)
    change ReductionRel (fw_matmul (smStore 100) (smStore 101)) (List.zipWith fw_matmul [pmStore 200, pmStore 201, pmStore 202] [pmStore 210, pmStore 211, pmStore 212]) [2, 4, 5, 11] at htransport
    have hout : fact_out.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] [2, 4, 5, 11]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa only [List.zipWith] using htransport
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
end SyntheticContraction
end TrainVerify.Denote
