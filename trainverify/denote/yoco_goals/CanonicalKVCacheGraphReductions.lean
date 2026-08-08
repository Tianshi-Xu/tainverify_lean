/- Layout-neutral graph reductions and initialized-weight bridge for the canonical Goal 1 cache segment. -/
import denote.yoco_goals.Goal_1
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

def cKVConSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5562],
    outs := [8337, 8341], params := [2] }
def cKVConPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9632],
    outs := [15806, 15810], params := [2] }
def cKVConPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9633],
    outs := [15814, 15818], params := [2] }
def cKVConSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8337, 5563], outs := [5564] }
def cKVConPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15806, 5563], outs := [9636] }
def cKVConPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15814, 5563], outs := [9637] }
def cKVConSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564],
    outs := [8348, 8352, 8356, 8360, 8364], params := [5] }
def cKVConPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636],
    outs := [15384, 13796, 13806, 13820, 13832], params := [5] }
def cKVConPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637],
    outs := [15386, 13797, 13807, 13821, 13833], params := [5] }

theorem cKVCon_red_sm8337 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8337 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5562 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 445 cKVConSmResidualRef
    5562 8337 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5562 [8337, 8341] 2 rfl 8337 (by decide)

theorem cKVCon_red_pm15806 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15806 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9632 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 987 cKVConPmResidualRef0
    9632 15806 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9632 [15806, 15810] 2 rfl 15806 (by decide)

theorem cKVCon_red_pm15814 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15814 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9633 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 988 cKVConPmResidualRef1
    9633 15814 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9633 [15814, 15818] 2 rfl 15814 (by decide)

theorem cKVCon_red_sm5564 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5564 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8337)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 446 cKVConSmRms
    8337 5563 5564 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold cKVConSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8337 5563 5564

theorem cKVCon_red_pm9636 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9636 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15806)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 989 cKVConPmRms0
    15806 5563 9636 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold cKVConPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15806 5563 9636

theorem cKVCon_red_pm9637 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9637 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15814)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 990 cKVConPmRms1
    15814 5563 9637 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold cKVConPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15814 5563 9637

theorem cKVCon_red_sm8352 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8352 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 447 cKVConSmNormRef
    5564 8352 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364]
    5 rfl 8352 (by decide)

theorem cKVCon_red_pm13796 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13796 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 991 cKVConPmNormRef0
    9636 13796 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636
    [15384, 13796, 13806, 13820, 13832] 5 rfl 13796 (by decide)

theorem cKVCon_red_pm13797 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13797 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 992 cKVConPmNormRef1
    9637 13797 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637
    [15386, 13797, 13807, 13821, 13833] 5 rfl 13797 (by decide)

theorem cKVCon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5563 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5563 := by
  have h := hInit initGoal_5563 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5563 pm_goal_1.numRanks _ rfl,
    show initGoal_5563.tps = [{rank := 0, tid := 5563}] from rfl,
    show initGoal_5563.ts = 5563 from rfl,
    show initGoal_5563.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5563
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5563
      (by native_decide) (by native_decide)]
  exact hval

theorem cKVCon_red_sm8341 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8341 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5562 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 445 cKVConSmResidualRef
    5562 8341 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5562 [8337, 8341] 2 rfl 8341 (by decide)

theorem cKVCon_red_pm15810 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15810 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9632 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 987 cKVConPmResidualRef0
    9632 15810 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9632 [15806, 15810] 2 rfl 15810 (by decide)

theorem cKVCon_red_pm15818 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15818 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9633 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 988 cKVConPmResidualRef1
    9633 15818 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9633 [15814, 15818] 2 rfl 15818 (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
