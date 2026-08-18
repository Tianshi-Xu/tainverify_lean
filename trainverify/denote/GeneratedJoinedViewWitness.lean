/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedJoinedViewWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_joined_input : RelationFact :=
  .joined 49 317 [1, 8, 3, 4]

private def fact_joined_output : RelationFact :=
  .joined 50 321 [1, 8, 12]

private def anchor : RelationFact :=
  .tensorShape .sm 77 [1]

private def state_pre : RelationState where
  facts := [anchor, fact_joined_input]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, fact_joined_output]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedJoinedViewWitness

namespace TrainVerify.Denote.GeneratedJoinedViewWitness
noncomputable section
private def sm_graph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [49], outs := [50], params := [1, 8, 12] }] }
private def pm_graph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }] }
private def segment_000000 (smGraph pmGraph : GraphDecl) :
    ClosedDepSegmentCertificate smGraph pmGraph state_pre state_post where
  smNodes := [{ rank := 0, op := "OpName.FW_view", ins := [49], outs := [50], params := [1, 8, 12] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [49], outs := [50], params := [1, 8, 12] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 2, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_joined_input.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm : smFinal 50 = fw_view [1, 8, 12] (smStore 49) := by
      simpa [smFinal, smNodes] using
        (foldl_faithful_unary_middle_writer smGraph smStore
          [] [] { rank := 0, op := "OpName.FW_view", ins := [49], outs := [50], params := [1, 8, 12] }
          49 50 (fun x => fw_view [1, 8, 12] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out smGraph t 0 1 [8, 12] 49 50)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hpm : pmFinal 321 = fw_view [1, 8, 12] (pmStore 317) := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_unary_middle_writer pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, { rank := 1, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }] [] { rank := 2, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }
          317 321 (fun x => fw_view [1, 8, 12] x) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
            simp [applyNodeDistributed, applyNodeRingAttn]
            exact applyNode_fw_view_out pmGraph t 2 1 [8, 12] 317 321)
          (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hout : fact_joined_output.Holds smFinal pmFinal := by
      change smFinal 50 = pmFinal 321 ∧
        (smFinal 50).shape = [1, 8, 12] ∧
        (pmFinal 321).shape = [1, 8, 12]
      change smStore 49 = pmStore 317 ∧
        (smStore 49).shape = [1, 8, 3, 4] ∧
        (pmStore 317).shape = [1, 8, 3, 4] at hin
      rw [hsm, hpm]
      exact JoinedRel.fw_view [1, 8, 12] [1, 8, 3, 4] hin
    exact RelationState.Holds.mono_insert hframe hout (by native_decide)

#print axioms segment_000000
end
end TrainVerify.Denote.GeneratedJoinedViewWitness
