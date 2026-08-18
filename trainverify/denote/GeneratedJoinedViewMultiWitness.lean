/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedJoinedViewPairWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_joined_input_0 : RelationFact :=
  .joined 40 300 [1, 8, 3, 4]

private def fact_joined_input_1 : RelationFact :=
  .joined 41 301 [1, 8, 3, 5]

private def fact_joined_output_0 : RelationFact :=
  .joined 60 400 [1, 8, 12]

private def fact_joined_output_1 : RelationFact :=
  .joined 61 401 [1, 8, 13]

private def anchor : RelationFact :=
  .tensorShape .sm 77 [1]

private def state_pre : RelationState where
  facts := [anchor, fact_joined_input_0, fact_joined_input_1]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, fact_joined_output_0, fact_joined_output_1]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedJoinedViewPairWitness

namespace TrainVerify.Denote.GeneratedJoinedViewPairWitness
noncomputable section
private def sm_graph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }] }
private def pm_graph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }] }
private def segment_multi (smGraph pmGraph : GraphDecl) :
    ClosedDepSegmentCertificate smGraph pmGraph state_pre state_post where
  smNodes := [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin_0 : fact_joined_input_0.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm_0 : smFinal 60 = fw_view [1, 8, 12] (smStore 40) := by
      simpa [smFinal, smNodes] using
        (foldl_faithful_unary_middle_writer smGraph smStore
          [] [{ rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }] { rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }
          40 60 (fun x => fw_view [1, 8, 12] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out smGraph t 0 1 [8, 12] 40 60)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hpm_0 : pmFinal 400 = fw_view [1, 8, 12] (pmStore 300) := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_unary_middle_writer pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }] [{ rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }] { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }
          300 400 (fun x => fw_view [1, 8, 12] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out pmGraph t 1 1 [8, 12] 300 400)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hout_0 : fact_joined_output_0.Holds smFinal pmFinal := by
      change smFinal 60 = pmFinal 400 ∧
        (smFinal 60).shape = [1, 8, 12] ∧
        (pmFinal 400).shape = [1, 8, 12]
      change smStore 40 = pmStore 300 ∧
        (smStore 40).shape = [1, 8, 3, 4] ∧
        (pmStore 300).shape = [1, 8, 3, 4] at hin_0
      rw [hsm_0, hpm_0]
      exact JoinedRel.fw_view [1, 8, 12] [1, 8, 3, 4] hin_0
    have hin_1 : fact_joined_input_1.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm_1 : smFinal 61 = fw_view [1, 8, 13] (smStore 41) := by
      simpa [smFinal, smNodes] using
        (foldl_faithful_unary_middle_writer smGraph smStore
          [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }] [] { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }
          41 61 (fun x => fw_view [1, 8, 13] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out smGraph t 0 1 [8, 13] 41 61)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hpm_1 : pmFinal 401 = fw_view [1, 8, 13] (pmStore 301) := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_unary_middle_writer pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }] [] { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }
          301 401 (fun x => fw_view [1, 8, 13] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out pmGraph t 1 1 [8, 13] 301 401)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hout_1 : fact_joined_output_1.Holds smFinal pmFinal := by
      change smFinal 61 = pmFinal 401 ∧
        (smFinal 61).shape = [1, 8, 13] ∧
        (pmFinal 401).shape = [1, 8, 13]
      change smStore 41 = pmStore 301 ∧
        (smStore 41).shape = [1, 8, 3, 5] ∧
        (pmStore 301).shape = [1, 8, 3, 5] at hin_1
      rw [hsm_1, hpm_1]
      exact JoinedRel.fw_view [1, 8, 13] [1, 8, 3, 5] hin_1
    let publish_0 : RelationState := {
      facts := [anchor, fact_joined_output_0]
      nonempty := by native_decide }
    have hpublish_0 : publish_0.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert (before := state_pre)
        (after := publish_0) (fresh := fact_joined_output_0)
        hframe hout_0 (by native_decide)
    have hpublish_1 : state_post.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert (before := publish_0)
        (after := state_post) (fresh := fact_joined_output_1)
        hpublish_0 hout_1 (by native_decide)
    exact hpublish_1

#print axioms segment_multi
end
end TrainVerify.Denote.GeneratedJoinedViewPairWitness

namespace TrainVerify.Denote.GeneratedJoinedViewTripleWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_joined_input_0 : RelationFact :=
  .joined 40 300 [1, 8, 3, 4]

private def fact_joined_input_1 : RelationFact :=
  .joined 41 301 [1, 8, 3, 5]

private def fact_joined_input_2 : RelationFact :=
  .joined 42 302 [1, 8, 3, 6]

private def fact_joined_output_0 : RelationFact :=
  .joined 60 400 [1, 8, 12]

private def fact_joined_output_1 : RelationFact :=
  .joined 61 401 [1, 8, 13]

private def fact_joined_output_2 : RelationFact :=
  .joined 62 402 [1, 8, 14]

private def anchor : RelationFact :=
  .tensorShape .sm 77 [1]

private def state_pre : RelationState where
  facts := [anchor, fact_joined_input_0, fact_joined_input_1, fact_joined_input_2]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, fact_joined_output_0, fact_joined_output_1, fact_joined_output_2]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedJoinedViewTripleWitness

namespace TrainVerify.Denote.GeneratedJoinedViewTripleWitness
noncomputable section
private def sm_graph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [42], outs := [62], params := [1, 8, 14] }] }
private def pm_graph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 3, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 2, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 3, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 1, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 2, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 3, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }] }
private def segment_multi (smGraph pmGraph : GraphDecl) :
    ClosedDepSegmentCertificate smGraph pmGraph state_pre state_post where
  smNodes := [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [42], outs := [62], params := [1, 8, 14] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 3, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 2, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 3, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 1, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 2, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 3, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [42], outs := [62], params := [1, 8, 14] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 3, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 2, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 3, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 1, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 2, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 3, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin_0 : fact_joined_input_0.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm_0 : smFinal 60 = fw_view [1, 8, 12] (smStore 40) := by
      simpa [smFinal, smNodes] using
        (foldl_faithful_unary_middle_writer smGraph smStore
          [] [{ rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [42], outs := [62], params := [1, 8, 14] }] { rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }
          40 60 (fun x => fw_view [1, 8, 12] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out smGraph t 0 1 [8, 12] 40 60)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hpm_0 : pmFinal 400 = fw_view [1, 8, 12] (pmStore 300) := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_unary_middle_writer pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }] [{ rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 2, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 3, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 1, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 2, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 3, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }] { rank := 3, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }
          300 400 (fun x => fw_view [1, 8, 12] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out pmGraph t 3 1 [8, 12] 300 400)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hout_0 : fact_joined_output_0.Holds smFinal pmFinal := by
      change smFinal 60 = pmFinal 400 ∧
        (smFinal 60).shape = [1, 8, 12] ∧
        (pmFinal 400).shape = [1, 8, 12]
      change smStore 40 = pmStore 300 ∧
        (smStore 40).shape = [1, 8, 3, 4] ∧
        (pmStore 300).shape = [1, 8, 3, 4] at hin_0
      rw [hsm_0, hpm_0]
      exact JoinedRel.fw_view [1, 8, 12] [1, 8, 3, 4] hin_0
    have hin_1 : fact_joined_input_1.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm_1 : smFinal 61 = fw_view [1, 8, 13] (smStore 41) := by
      simpa [smFinal, smNodes] using
        (foldl_faithful_unary_middle_writer smGraph smStore
          [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }] [{ rank := 0, op := "OpName.FW_view", ins := [42], outs := [62], params := [1, 8, 14] }] { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }
          41 61 (fun x => fw_view [1, 8, 13] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out smGraph t 0 1 [8, 13] 41 61)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hpm_1 : pmFinal 401 = fw_view [1, 8, 13] (pmStore 301) := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_unary_middle_writer pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 3, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 2, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }] [{ rank := 0, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 1, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 2, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 3, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }] { rank := 3, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }
          301 401 (fun x => fw_view [1, 8, 13] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out pmGraph t 3 1 [8, 13] 301 401)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hout_1 : fact_joined_output_1.Holds smFinal pmFinal := by
      change smFinal 61 = pmFinal 401 ∧
        (smFinal 61).shape = [1, 8, 13] ∧
        (pmFinal 401).shape = [1, 8, 13]
      change smStore 41 = pmStore 301 ∧
        (smStore 41).shape = [1, 8, 3, 5] ∧
        (pmStore 301).shape = [1, 8, 3, 5] at hin_1
      rw [hsm_1, hpm_1]
      exact JoinedRel.fw_view [1, 8, 13] [1, 8, 3, 5] hin_1
    have hin_2 : fact_joined_input_2.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm_2 : smFinal 62 = fw_view [1, 8, 14] (smStore 42) := by
      simpa [smFinal, smNodes] using
        (foldl_faithful_unary_middle_writer smGraph smStore
          [{ rank := 0, op := "OpName.FW_view", ins := [40], outs := [60], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [41], outs := [61], params := [1, 8, 13] }] [] { rank := 0, op := "OpName.FW_view", ins := [42], outs := [62], params := [1, 8, 14] }
          42 62 (fun x => fw_view [1, 8, 14] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out smGraph t 0 1 [8, 14] 42 62)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hpm_2 : pmFinal 402 = fw_view [1, 8, 14] (pmStore 302) := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_unary_middle_writer pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 3, op := "OpName.FW_view", ins := [300], outs := [400], params := [1, 8, 12] }, { rank := 0, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 1, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 2, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 3, op := "OpName.FW_view", ins := [301], outs := [401], params := [1, 8, 13] }, { rank := 0, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 1, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }, { rank := 2, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }] [] { rank := 3, op := "OpName.FW_view", ins := [302], outs := [402], params := [1, 8, 14] }
          302 402 (fun x => fw_view [1, 8, 14] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out pmGraph t 3 1 [8, 14] 302 402)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hout_2 : fact_joined_output_2.Holds smFinal pmFinal := by
      change smFinal 62 = pmFinal 402 ∧
        (smFinal 62).shape = [1, 8, 14] ∧
        (pmFinal 402).shape = [1, 8, 14]
      change smStore 42 = pmStore 302 ∧
        (smStore 42).shape = [1, 8, 3, 6] ∧
        (pmStore 302).shape = [1, 8, 3, 6] at hin_2
      rw [hsm_2, hpm_2]
      exact JoinedRel.fw_view [1, 8, 14] [1, 8, 3, 6] hin_2
    let publish_0 : RelationState := {
      facts := [anchor, fact_joined_output_0]
      nonempty := by native_decide }
    have hpublish_0 : publish_0.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert (before := state_pre)
        (after := publish_0) (fresh := fact_joined_output_0)
        hframe hout_0 (by native_decide)
    let publish_1 : RelationState := {
      facts := [anchor, fact_joined_output_0, fact_joined_output_1]
      nonempty := by native_decide }
    have hpublish_1 : publish_1.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert (before := publish_0)
        (after := publish_1) (fresh := fact_joined_output_1)
        hpublish_0 hout_1 (by native_decide)
    have hpublish_2 : state_post.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert (before := publish_1)
        (after := state_post) (fresh := fact_joined_output_2)
        hpublish_1 hout_2 (by native_decide)
    exact hpublish_2

#print axioms segment_multi
end
end TrainVerify.Denote.GeneratedJoinedViewTripleWitness
