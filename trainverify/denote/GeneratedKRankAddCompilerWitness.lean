import denote.KRankAddGather
import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticAdd
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] }, { rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] }, { rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] }] }

def fact_a : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 5] [2, 4, 5]
def fact_b : RelationFact := .sharded 110 [210, 211, 212] 1 [2, 12, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 120 [300, 301, 302] 1 [2, 12, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_a, fact_b]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000004_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] }
private def segment_000004_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] }
private def segment_000004_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] }
private def segment_000004_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] }
private def segment_000004_sm_nodes : List NodeDecl := [segment_000004_sm_node]
private def segment_000004_pm_nodes : List NodeDecl := [segment_000004_pm_node_0, segment_000004_pm_node_1, segment_000004_pm_node_2]

private def segment_000004 :
    ClosedDepSegmentCertificate SyntheticAdd.gSM SyntheticAdd.gPM state_pre state_post where
  smNodes := segment_000004_sm_nodes
  pmNodes := segment_000004_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000004_sm_nodes
    let pmNodes : List NodeDecl := segment_000004_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have ha : fact_a.Holds smStore pmStore := hstate _ (by native_decide)
    have hb : fact_b.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 12, 5] [2, 4, 5] at ha
    change ShardedRel (smStore 110) [pmStore 210, pmStore 211, pmStore 212] 1 [2, 12, 5] [2, 4, 5] at hb
    have hSmWriter : smFinal 120 = elemwiseAdd (smStore 100) (smStore 110) := by
      simpa [smFinal, smNodes, segment_000004_sm_nodes] using
        (foldl_faithful_binary_middle_writer SyntheticAdd.gSM smStore [] [] segment_000004_sm_node
          100 110 120 elemwiseAdd (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_add2_out SyntheticAdd.gSM t 0 100 110 120)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hPmWriter0 : pmFinal 300 = elemwiseAdd (pmStore 200) (pmStore 210) := by
      simpa [pmFinal, pmNodes, segment_000004_pm_nodes] using
        (foldl_faithful_binary_middle_writer SyntheticAdd.gPM pmStore [] [segment_000004_pm_node_1, segment_000004_pm_node_2] segment_000004_pm_node_0
          200 210 300 elemwiseAdd (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_add2_out SyntheticAdd.gPM t 0 200 210 300)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hPmWriter1 : pmFinal 301 = elemwiseAdd (pmStore 201) (pmStore 211) := by
      simpa [pmFinal, pmNodes, segment_000004_pm_nodes] using
        (foldl_faithful_binary_middle_writer SyntheticAdd.gPM pmStore [segment_000004_pm_node_0] [segment_000004_pm_node_2] segment_000004_pm_node_1
          201 211 301 elemwiseAdd (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_add2_out SyntheticAdd.gPM t 1 201 211 301)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hPmWriter2 : pmFinal 302 = elemwiseAdd (pmStore 202) (pmStore 212) := by
      simpa [pmFinal, pmNodes, segment_000004_pm_nodes] using
        (foldl_faithful_binary_middle_writer SyntheticAdd.gPM pmStore [segment_000004_pm_node_0, segment_000004_pm_node_1] [] segment_000004_pm_node_2
          202 212 302 elemwiseAdd (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_add2_out SyntheticAdd.gPM t 2 202 212 302)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hcomm := fw_add_allGather_dim_K 1 [2, 4, 5] [pmStore 200, pmStore 201, pmStore 202] [pmStore 210, pmStore 211, pmStore 212]
      ha.shards_nonempty (by simp) ha.gather_dim_lt
      (fun r hr => ha.shard_shapes _ (List.get_mem _ ⟨r, hr⟩))
      (fun r hr => hb.shard_shapes _ (List.get_mem _ ⟨r, hr⟩))
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 120) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 12, 5] [2, 4, 5]
      constructor
      · rw [hSmWriter, ha.full_value, hb.full_value, hcomm]
        simp only [List.zipWith, List.length_cons, List.length_nil]
        rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
      · rw [hSmWriter]
        exact elemwiseAdd_shape_of_shapes _ _ [2, 12, 5] ha.full_shape hb.full_shape
      · simp
      · exact ha.gather_dim_lt
      · intro shard hmem
        have hAShape0 := ha.shard_shapes (pmStore 200) (by simp)
        have hBShape0 := hb.shard_shapes (pmStore 210) (by simp)
        have hAShape1 := ha.shard_shapes (pmStore 201) (by simp)
        have hBShape1 := hb.shard_shapes (pmStore 211) (by simp)
        have hAShape2 := ha.shard_shapes (pmStore 202) (by simp)
        have hBShape2 := hb.shard_shapes (pmStore 212) (by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          rw [hPmWriter0]
          exact elemwiseAdd_shape_of_shapes _ _ [2, 4, 5] hAShape0 hBShape0
        · subst shard
          rw [hPmWriter1]
          exact elemwiseAdd_shape_of_shapes _ _ [2, 4, 5] hAShape1 hBShape1
        · subst shard
          rw [hPmWriter2]
          exact elemwiseAdd_shape_of_shapes _ _ [2, 4, 5] hAShape2 hBShape2
      · exact ha.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#print axioms segment_000004
end
end SyntheticAdd
end TrainVerify.Denote
