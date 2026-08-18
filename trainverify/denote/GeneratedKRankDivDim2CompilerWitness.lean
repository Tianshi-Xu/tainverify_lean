import denote.KRankDivGather

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticDiv2
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_div", ins := [100], outs := [110], params := [8] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_div", ins := [201], outs := [301], params := [8] }, { rank := 1, op := "OpName.FW_div", ins := [202], outs := [302], params := [8] }, { rank := 2, op := "OpName.FW_div", ins := [203], outs := [303], params := [8] }] }

def fact_in : RelationFact := .sharded 100 [201, 202, 203] 2 [1, 12, 768, 64] [1, 12, 256, 64]
def fact_out : RelationFact := .sharded 110 [301, 302, 303] 2 [1, 12, 768, 64] [1, 12, 256, 64]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_div", ins := [100], outs := [110], params := [8] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_div", ins := [201], outs := [301], params := [8] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_div", ins := [202], outs := [302], params := [8] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_div", ins := [203], outs := [303], params := [8] }
private def segment_000000_sm_nodes : List NodeDecl := [segment_000000_sm_node]
private def segment_000000_pm_nodes : List NodeDecl := [segment_000000_pm_node_0, segment_000000_pm_node_1, segment_000000_pm_node_2]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticDiv2.gSM SyntheticDiv2.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticDiv2.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticDiv2.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 201, pmStore 202, pmStore 203] 2 [1, 12, 768, 64] [1, 12, 256, 64] at hin
    have hinDiv : ShardedRel (smStore 100) [pmStore 201, pmStore 202, pmStore 203] 2 [1, 12, 256 * [pmStore 201, pmStore 202, pmStore 203].length, 64] [1, 12, 256, 64] := by
      simpa using hin
    have hSmWriter : smFinal 110 = fw_div (8 : Scalar) (smStore 100) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticDiv2.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticDiv2.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 110 (fun t => fw_div (8 : Scalar) (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_div_out_g92 SyntheticDiv2.gSM t 0 8 100 110
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticDiv2.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 301 = fw_div (8 : Scalar) (pmStore 201) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticDiv2.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticDiv2.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_0 301 (fun t => fw_div (8 : Scalar) (t 201)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_div_out_g92 SyntheticDiv2.gPM t 0 8 201 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticDiv2.gPM (pmNodes.take 0) pmStore 201 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 302 = fw_div (8 : Scalar) (pmStore 202) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticDiv2.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticDiv2.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_1 302 (fun t => fw_div (8 : Scalar) (t 202)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_div_out_g92 SyntheticDiv2.gPM t 1 8 202 302
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticDiv2.gPM (pmNodes.take 1) pmStore 202 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 303 = fw_div (8 : Scalar) (pmStore 203) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticDiv2.gPM) pmStore) 303 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticDiv2.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_2 303 (fun t => fw_div (8 : Scalar) (t 203)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_div_out_g92 SyntheticDiv2.gPM t 2 8 203 303
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticDiv2.gPM (pmNodes.take 2) pmStore 203 (by native_decide) (by native_decide)]
    have htransport := ShardedRel.fw_div_dim2_rank4 (h := hinDiv) (c := (8 : Scalar))
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 301, pmFinal 302, pmFinal 303] 2 [1, 12, 768, 64] [1, 12, 256, 64]
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
end SyntheticDiv2
end TrainVerify.Denote
