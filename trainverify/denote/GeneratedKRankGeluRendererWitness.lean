import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticGelu
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }, { rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }, { rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 12, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000051_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }
private def segment_000051_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }
private def segment_000051_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }
private def segment_000051_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }
private def segment_000051_sm_nodes : List NodeDecl := [segment_000051_sm_node]
private def segment_000051_pm_nodes : List NodeDecl := [segment_000051_pm_node_0, segment_000051_pm_node_1, segment_000051_pm_node_2]

private def segment_000051 :
    ClosedDepSegmentCertificate SyntheticGelu.gSM SyntheticGelu.gPM state_pre state_post where
  smNodes := segment_000051_sm_nodes
  pmNodes := segment_000051_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000051_sm_nodes
    let pmNodes : List NodeDecl := segment_000051_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 12, 5] [2, 4, 5] at hin
    have hSmWriter : smFinal 110 = fw_gelu (smStore 100) := by
      simpa [smFinal, smNodes, segment_000051_sm_nodes] using
        (foldl_faithful_unary_middle_writer SyntheticGelu.gSM smStore
          [] [] segment_000051_sm_node 100 110 fw_gelu (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_gelu_out SyntheticGelu.gSM t 0 100 110)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hPmWriter0 : pmFinal 300 = fw_gelu (pmStore 200) := by
      simpa [pmFinal, pmNodes, segment_000051_pm_nodes] using
        (foldl_faithful_unary_middle_writer SyntheticGelu.gPM pmStore
          [] [segment_000051_pm_node_1, segment_000051_pm_node_2] segment_000051_pm_node_0 200 300 fw_gelu (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_gelu_out SyntheticGelu.gPM t 0 200 300)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hPmWriter1 : pmFinal 301 = fw_gelu (pmStore 201) := by
      simpa [pmFinal, pmNodes, segment_000051_pm_nodes] using
        (foldl_faithful_unary_middle_writer SyntheticGelu.gPM pmStore
          [segment_000051_pm_node_0] [segment_000051_pm_node_2] segment_000051_pm_node_1 201 301 fw_gelu (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_gelu_out SyntheticGelu.gPM t 1 201 301)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hPmWriter2 : pmFinal 302 = fw_gelu (pmStore 202) := by
      simpa [pmFinal, pmNodes, segment_000051_pm_nodes] using
        (foldl_faithful_unary_middle_writer SyntheticGelu.gPM pmStore
          [segment_000051_pm_node_0, segment_000051_pm_node_1] [] segment_000051_pm_node_2 202 302 fw_gelu (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_gelu_out SyntheticGelu.gPM t 2 202 302)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hcomm := TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq 1 [pmStore 200, pmStore 201, pmStore 202].length [pmStore 200, pmStore 201, pmStore 202] [2, 4, 5]
      (by simp) rfl
      (by simp only [List.head?, Option.map, Option.getD]; exact hin.shard_shapes _ (by simp))
      (by intro i hi; exact hin.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 12, 5] [2, 4, 5]
      constructor
      · rw [hSmWriter, hin.full_value, hcomm]
        simp only [List.map, List.length_cons, List.length_nil]
        rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
      · rw [hSmWriter, fw_gelu_shape]
        exact hin.full_shape
      · simp
      · exact hin.gather_dim_lt
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          rw [hPmWriter0, fw_gelu_shape]
          exact hin.shard_shapes (pmStore 200) (by simp)
        · subst shard
          rw [hPmWriter1, fw_gelu_shape]
          exact hin.shard_shapes (pmStore 201) (by simp)
        · subst shard
          rw [hPmWriter2, fw_gelu_shape]
          exact hin.shard_shapes (pmStore 202) (by simp)
      · exact hin.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#print axioms segment_000051
end
end SyntheticGelu
end TrainVerify.Denote
