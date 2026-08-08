/- Canonical Goal 1, layer 23: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.CanonicalL23Expert
import denote.yoco_goals.CanonicalL23GateDown

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

private def cL23dSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6216], outs := [8948, 8952, 8956, 8960, 8964], params := [5] }

private def cL23dPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11512], outs := [15432, 15208, 15218, 15232, 15244], params := [5] }

private def cL23dPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11513], outs := [15434, 15209, 15219, 15233, 15245], params := [5] }

private def cL23dSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8960], outs := [6231], params := [4096, 1024] }

private def cL23dSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8964], outs := [6235], params := [4096, 1024] }

private def cL23dPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15232], outs := [11544], params := [2048, 1024] }

private def cL23dPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15233], outs := [11545], params := [2048, 1024] }

private def cL23dPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15244], outs := [11556], params := [2048, 1024] }

private def cL23dPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15245], outs := [11557], params := [2048, 1024] }

private def cL23dSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6231, 6232], outs := [6233] }

private def cL23dSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6235, 6236], outs := [6237] }

private def cL23dPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11544, 6232], outs := [11548] }

private def cL23dPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11545, 6232], outs := [11549] }

private def cL23dPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11556, 6236], outs := [11560] }

private def cL23dPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11557, 6236], outs := [11561] }

private def cL23dSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6233], outs := [6234], params := [4096, 512] }

private def cL23dSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6237], outs := [6238], params := [4096, 512] }

private def cL23dPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11548], outs := [11550], params := [2048, 512] }

private def cL23dPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11549], outs := [11551], params := [2048, 512] }

private def cL23dPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11560], outs := [11562], params := [2048, 512] }

private def cL23dPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11561], outs := [11563], params := [2048, 512] }

private def cL23dSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [6234, 6238], outs := [6239] }

private def cL23dPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11550, 11562], outs := [11568] }

private def cL23dPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11551, 11563], outs := [11569] }

private def cL23dSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6239], outs := [6240], params := [4096, 512] }

private def cL23dPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11568], outs := [11570], params := [2048, 512] }

private def cL23dPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11569], outs := [11571], params := [2048, 512] }

private def cL23dSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6240, 6241], outs := [6242] }

private def cL23dPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11570, 6241], outs := [11576] }

private def cL23dPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11571, 6241], outs := [11577] }

private def cL23dSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6242], outs := [6243], params := [4096, 1024] }

private def cL23dPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11576], outs := [11578], params := [2048, 1024] }

private def cL23dPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11577], outs := [11579], params := [2048, 1024] }

private theorem cL23d_red_sm8960 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8960 =
      denoteGraphDistributedFaithful sm_goal_1 init 6216 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 899 cL23dSmRef
    6216 8960 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6216 [8948, 8952, 8956, 8960, 8964] 5 rfl 8960 (by decide)

private theorem cL23d_red_sm8964 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8964 =
      denoteGraphDistributedFaithful sm_goal_1 init 6216 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 899 cL23dSmRef
    6216 8964 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6216 [8948, 8952, 8956, 8960, 8964] 5 rfl 8964 (by decide)

private theorem cL23d_red_pm15232 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15232 =
      denoteGraphDistributedFaithful pm_goal_1 init 11512 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1967 cL23dPmRef0
    11512 15232 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11512 [15432, 15208, 15218, 15232, 15244] 5 rfl 15232 (by decide)

private theorem cL23d_red_pm15244 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15244 =
      denoteGraphDistributedFaithful pm_goal_1 init 11512 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1967 cL23dPmRef0
    11512 15244 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11512 [15432, 15208, 15218, 15232, 15244] 5 rfl 15244 (by decide)

private theorem cL23d_red_pm15233 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15233 =
      denoteGraphDistributedFaithful pm_goal_1 init 11513 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1968 cL23dPmRef1
    11513 15233 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11513 [15434, 15209, 15219, 15233, 15245] 5 rfl 15233 (by decide)

private theorem cL23d_red_pm15245 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15245 =
      denoteGraphDistributedFaithful pm_goal_1 init 11513 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1968 cL23dPmRef1
    11513 15245 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11513 [15434, 15209, 15219, 15233, 15245] 5 rfl 15245 (by decide)

private theorem cL23d_red_sm6231 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6231 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8960) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 902 cL23dSmReshapeA
    8960 6231 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8960 6231 [4096, 1024]

private theorem cL23d_red_sm6235 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6235 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8964) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 903 cL23dSmReshapeB
    8964 6235 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8964 6235 [4096, 1024]

private theorem cL23d_red_pm11544 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11544 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15232) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1970 cL23dPmReshapeA0
    15232 11544 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15232 11544 [2048, 1024]

private theorem cL23d_red_pm11545 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11545 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15233) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1974 cL23dPmReshapeA1
    15233 11545 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15233 11545 [2048, 1024]

private theorem cL23d_red_pm11556 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11556 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15244) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1971 cL23dPmReshapeB0
    15244 11556 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15244 11556 [2048, 1024]

private theorem cL23d_red_pm11557 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11557 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15245) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1975 cL23dPmReshapeB1
    15245 11557 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15245 11557 [2048, 1024]

private theorem cL23d_red_sm6234 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6234 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6233) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 910 cL23dSmViewA
    6233 6234 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6233 6234

private theorem cL23d_red_sm6238 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6238 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6237) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 911 cL23dSmViewB
    6237 6238 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6237 6238

private theorem cL23d_red_pm11550 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11550 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11548) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1985 cL23dPmViewA0
    11548 11550 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11548 11550

private theorem cL23d_red_pm11551 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11551 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11549) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1990 cL23dPmViewA1
    11549 11551 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11549 11551

private theorem cL23d_red_pm11562 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11562 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11560) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1986 cL23dPmViewB0
    11560 11562 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11560 11562

private theorem cL23d_red_pm11563 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11563 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11561) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1991 cL23dPmViewB1
    11561 11563 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11561 11563

private theorem cL23d_red_sm6240 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6240 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6239) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 915 cL23dSmReshapeDown
    6239 6240 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6239 6240 [4096, 512]

private theorem cL23d_red_pm11570 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11570 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11568) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1998 cL23dPmReshapeDown0
    11568 11570 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11568 11570 [2048, 512]

private theorem cL23d_red_pm11571 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11571 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11569) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 2001 cL23dPmReshapeDown1
    11569 11571 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11569 11571 [2048, 512]

private theorem cL23d_red_sm6243 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6243 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 6242) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 917 cL23dSmViewDown
    6242 6243 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6242 6243

private theorem cL23d_red_pm11578 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11578 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11576) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 2006 cL23dPmViewDown0
    11576 11578 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11576 11578

private theorem cL23d_red_pm11579 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11579 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11577) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 2007 cL23dPmViewDown1
    11577 11579 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11577 11579

private theorem cL23d_red_sm6233 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6233 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6231)
        (denoteGraphDistributedFaithful sm_goal_1 init 6232) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 906 cL23dSmLinearA
    6231 6232 6233 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6231 6232 6233

private theorem cL23d_red_sm6237 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6237 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6235)
        (denoteGraphDistributedFaithful sm_goal_1 init 6236) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 907 cL23dSmLinearB
    6235 6236 6237 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6235 6236 6237

private theorem cL23d_red_pm11548 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11548 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11544)
        (denoteGraphDistributedFaithful pm_goal_1 init 6232) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1977 cL23dPmLinearA0
    11544 6232 11548 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11544 6232 11548

private theorem cL23d_red_pm11549 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11549 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11545)
        (denoteGraphDistributedFaithful pm_goal_1 init 6232) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1982 cL23dPmLinearA1
    11545 6232 11549 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11545 6232 11549

private theorem cL23d_red_pm11560 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11560 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11556)
        (denoteGraphDistributedFaithful pm_goal_1 init 6236) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1978 cL23dPmLinearB0
    11556 6236 11560 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11556 6236 11560

private theorem cL23d_red_pm11561 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11561 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11557)
        (denoteGraphDistributedFaithful pm_goal_1 init 6236) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1983 cL23dPmLinearB1
    11557 6236 11561 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11557 6236 11561

private theorem cL23d_red_sm6239 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6239 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 6234)
        (denoteGraphDistributedFaithful sm_goal_1 init 6238) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 914 cL23dSmSwi
    6234 6238 6239 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 6234 6238 6239

private theorem cL23d_red_pm11568 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11568 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11550)
        (denoteGraphDistributedFaithful pm_goal_1 init 11562) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1993 cL23dPmSwi0
    11550 11562 11568 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 11550 11562 11568

private theorem cL23d_red_pm11569 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11569 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11551)
        (denoteGraphDistributedFaithful pm_goal_1 init 11563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1997 cL23dPmSwi1
    11551 11563 11569 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 11551 11563 11569

private theorem cL23d_red_sm6242 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6242 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6240)
        (denoteGraphDistributedFaithful sm_goal_1 init 6241) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 916 cL23dSmLinearDown
    6240 6241 6242 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6240 6241 6242

private theorem cL23d_red_pm11576 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11576 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11570)
        (denoteGraphDistributedFaithful pm_goal_1 init 6241) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 2002 cL23dPmLinearDown0
    11570 6241 11576 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11570 6241 11576

private theorem cL23d_red_pm11577 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11577 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11571)
        (denoteGraphDistributedFaithful pm_goal_1 init 6241) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 2005 cL23dPmLinearDown1
    11571 6241 11577 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23dPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11571 6241 11577

private theorem cL23d_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem cL23d_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
    (htp : gW.tps = [{rank := 0, tid := W}])
    (hts : gW.ts = W) (hgd : gW.gatherDim = 0) (hrep : gW.replicated = false)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM W =
      denoteGraphDistributedFaithful pm_goal_1 initPM W := by
  have hi := (hInit gW hgW).2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hi
  simp only [List.map, reconstructWithDim] at hi
  rw [cL23d_leaf sm_goal_1 initSM W (by native_decide) hsm,
    cL23d_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem cL23d_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (shape : Shape)
    (henv : pmInitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [cL23d_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L23 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem canonical_l23_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6243)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11579)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15233)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23d_red_sm8960 initSM, cL23d_red_pm15232 initPM, cL23d_red_pm15233 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8964)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15244)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15245)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23d_red_sm8964 initSM, cL23d_red_pm15244 initPM, cL23d_red_pm15245 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6231)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11544)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11545)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23d_red_sm6231 initSM, cL23d_red_pm11544 initPM, cL23d_red_pm11545 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6235)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11556)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11557)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23d_red_sm6235 initSM, cL23d_red_pm11556 initPM, cL23d_red_pm11557 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := cL23d_weight_eq initSM initPM hInit initGoal_6232 (by native_decide)
    6232 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := cL23d_weight_eq initSM initPM hInit initGoal_6236 (by native_decide)
    6236 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := cL23d_weight_shape initPM hPM 6232 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := cL23d_weight_shape initPM hPM 6236 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6233)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11548)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11549)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL23d_red_sm6233 initSM, cL23d_red_pm11548 initPM,
      cL23d_red_pm11549 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6237)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11560)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11561)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL23d_red_sm6237 initSM, cL23d_red_pm11560 initPM,
      cL23d_red_pm11561 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11550)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11551)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL23d_red_sm6234 initSM, cL23d_red_pm11550 initPM, cL23d_red_pm11551 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6238)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11563)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL23d_red_sm6238 initSM, cL23d_red_pm11562 initPM, cL23d_red_pm11563 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11550)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11551)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6238)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11563)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6239)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11568)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11569)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL23d_red_sm6239 initSM, cL23d_red_pm11568 initPM, cL23d_red_pm11569 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6240)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11570)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11571)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL23d_red_sm6240 initSM, cL23d_red_pm11570 initPM, cL23d_red_pm11571 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := cL23d_weight_eq initSM initPM hInit initGoal_6241 (by native_decide)
    6241 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := cL23d_weight_shape initPM hPM 6241 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6242)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11576)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11577)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23d_red_sm6242 initSM, cL23d_red_pm11576 initPM,
      cL23d_red_pm11577 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [cL23d_red_sm6243 initSM, cL23d_red_pm11578 initPM, cL23d_red_pm11579 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
