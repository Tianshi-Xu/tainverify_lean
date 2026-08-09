/- Canonical Goal 1, layer 23: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.CanonicalL22Output
import denote.yoco_goals.ZigzagPointwiseRel
import denote.MultirefGeneral

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def cL23nSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6214],
    outs := [8937, 8941], params := [2] }
private def cL23nPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11508],
    outs := [16454, 16458], params := [2] }
private def cL23nPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11509],
    outs := [16462, 16466], params := [2] }
private def cL23nSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8937, 6215], outs := [6216] }
private def cL23nPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16454, 6215], outs := [11512] }
private def cL23nPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16462, 6215], outs := [11513] }
private def cL23nSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6216],
    outs := [8948, 8952, 8956, 8960, 8964], params := [5] }
private def cL23nPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11512],
    outs := [15432, 15208, 15218, 15232, 15244], params := [5] }
private def cL23nPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11513],
    outs := [15434, 15209, 15219, 15233, 15245], params := [5] }

private theorem cL23n_red_sm8937 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8937 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6214 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 897 cL23nSmRef2
    6214 8937 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23nSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6214 [8937, 8941] 2 rfl 8937
    (by decide)

private theorem cL23n_red_pm16454 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16454 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11508 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1963 cL23nPmRef20
    11508 16454 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23nPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11508 [16454, 16458] 2 rfl 16454
    (by decide)

private theorem cL23n_red_pm16462 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16462 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11509 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1964 cL23nPmRef21
    11509 16462 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23nPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11509 [16462, 16466] 2 rfl 16462
    (by decide)

private theorem cL23n_red_sm6216 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6216 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8937)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6215) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 898 cL23nSmRms
    8937 6215 6216 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23nSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8937 6215 6216

private theorem cL23n_red_pm11512 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11512 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16454)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6215) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1965 cL23nPmRms0
    16454 6215 11512 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23nPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16454 6215 11512

private theorem cL23n_red_pm11513 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11513 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16462)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6215) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1966 cL23nPmRms1
    16462 6215 11513 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23nPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16462 6215 11513

private theorem cL23n_red_sm8952 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8952 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6216 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 899 cL23nSmRef5
    6216 8952 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23nSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6216 [8948, 8952, 8956, 8960, 8964]
    5 rfl 8952 (by decide)

private theorem cL23n_red_pm15208 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15208 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11512 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1967 cL23nPmRef50
    11512 15208 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23nPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11512
    [15432, 15208, 15218, 15232, 15244] 5 rfl 15208 (by decide)

private theorem cL23n_red_pm15209 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15209 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11513 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1968 cL23nPmRef51
    11513 15209 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23nPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11513
    [15434, 15209, 15219, 15233, 15245] 5 rfl 15209 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 6215. -/
theorem canonical_l23_weight6215_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6215 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6215 := by
  have h := hInit initGoal_6215 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6215 pm_goal_1.numRanks _ rfl,
    show initGoal_6215.tps = [{rank := 0, tid := 6215}] from rfl,
    show initGoal_6215.ts = 6215 from rfl,
    show initGoal_6215.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 6215 = initSM 6215 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6215
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 6215 = initPM 6215 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6215
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem cL23n_norm_of_layer22 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer22 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6214)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11509)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := canonical_l23_weight6215_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8937)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16462)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23n_red_sm8937 initSM, cL23n_red_pm16454 initPM, cL23n_red_pm16462 initPM]
    exact hLayer22
  rw [cL23n_red_sm6216 initSM, cL23n_red_pm11512 initPM, cL23n_red_pm11513 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L23 shared RMSNorm relation.  The computed L22 output relation is
obtained internally from `canonical_l22_output_from_inputs`; no computed
intermediate is added to the caller contract. -/
theorem canonical_l23_norm_from_l22_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hProjectionWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210)
    (hProjectionWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hLayer22 := canonical_l22_output_from_inputs initSM initPM hResidual hAttention
    hProjectionWeight hProjectionWeightShape
  exact cL23n_norm_of_layer22 initSM initPM hInit hLayer22

/-- The exact expert activation inputs are multiref aliases of the canonical
L23 shared RMSNorm outputs, so their zigzag relation is also a conclusion. -/
theorem canonical_l23_activation_from_l22_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hProjectionWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210)
    (hProjectionWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8952)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15209)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := canonical_l23_norm_from_l22_inputs initSM initPM hInit hResidual hAttention
    hProjectionWeight hProjectionWeightShape
  rw [cL23n_red_sm8952 initSM, cL23n_red_pm15208 initPM, cL23n_red_pm15209 initPM]
  exact hNorm

end
end TrainVerify.Denote.GeneratedPatterns
