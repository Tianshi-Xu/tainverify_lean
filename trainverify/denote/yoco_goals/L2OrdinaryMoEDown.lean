/- Canonical Goal 1 cache-source layer: ordinary SwiGLU/down-projection branch. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.FaithfulStackGather
import denote.yoco_goals.ZigzagLayoutRel
import denote.yoco_goals.ZigzagLinearRel
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

private def l2OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5069], outs := [7880, 7884, 7888, 7892, 7896], params := [5] }

private def l2OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8160], outs := [15312, 12662, 12672, 12686, 12698], params := [5] }

private def l2OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8161], outs := [15314, 12663, 12673, 12687, 12699], params := [5] }

private def l2OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7892], outs := [5084], params := [4096, 1024] }

private def l2OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7896], outs := [5088], params := [4096, 1024] }

private def l2OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12686], outs := [8192], params := [2048, 1024] }

private def l2OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12687], outs := [8193], params := [2048, 1024] }

private def l2OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12698], outs := [8204], params := [2048, 1024] }

private def l2OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12699], outs := [8205], params := [2048, 1024] }

private def l2OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5084, 5085], outs := [5086] }

private def l2OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5088, 5089], outs := [5090] }

private def l2OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8192, 5085], outs := [8196] }

private def l2OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8193, 5085], outs := [8197] }

private def l2OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8204, 5089], outs := [8208] }

private def l2OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8205, 5089], outs := [8209] }

private def l2OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5086], outs := [5087], params := [4096, 512] }

private def l2OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5090], outs := [5091], params := [4096, 512] }

private def l2OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8196], outs := [8198], params := [2048, 512] }

private def l2OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8197], outs := [8199], params := [2048, 512] }

private def l2OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8208], outs := [8210], params := [2048, 512] }

private def l2OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8209], outs := [8211], params := [2048, 512] }

private def l2OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5087, 5091], outs := [5092] }

private def l2OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [8198, 8210], outs := [8216] }

private def l2OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [8199, 8211], outs := [8217] }

private def l2OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5092], outs := [5093], params := [4096, 512] }

private def l2OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8216], outs := [8218], params := [2048, 512] }

private def l2OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [8217], outs := [8219], params := [2048, 512] }

private def l2OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5093, 5094], outs := [5095] }

private def l2OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8218, 5094], outs := [8224] }

private def l2OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8219, 5094], outs := [8225] }

private def l2OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5095], outs := [5096], params := [4096, 1024] }

private def l2OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8224], outs := [8226], params := [2048, 1024] }

private def l2OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8225], outs := [8227], params := [2048, 1024] }

private theorem l2OMOd_red_sm12686 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7892 =
      denoteGraphDistributedFaithful sm_goal_1 init 5069 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 96 l2OMOdSmRef
    5069 7892 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5069 [7880, 7884, 7888, 7892, 7896] 5 rfl 7892 (by decide)

private theorem l2OMOd_red_sm12698 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7896 =
      denoteGraphDistributedFaithful sm_goal_1 init 5069 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 96 l2OMOdSmRef
    5069 7896 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5069 [7880, 7884, 7888, 7892, 7896] 5 rfl 7896 (by decide)

private theorem l2OMOd_red_pm12686 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12686 =
      denoteGraphDistributedFaithful pm_goal_1 init 8160 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 235 l2OMOdPmRef0
    8160 12686 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8160 [15312, 12662, 12672, 12686, 12698] 5 rfl 12686 (by decide)

private theorem l2OMOd_red_pm12698 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12698 =
      denoteGraphDistributedFaithful pm_goal_1 init 8160 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 235 l2OMOdPmRef0
    8160 12698 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8160 [15312, 12662, 12672, 12686, 12698] 5 rfl 12698 (by decide)

private theorem l2OMOd_red_pm12687 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12687 =
      denoteGraphDistributedFaithful pm_goal_1 init 8161 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 236 l2OMOdPmRef1
    8161 12687 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8161 [15314, 12663, 12673, 12687, 12699] 5 rfl 12687 (by decide)

private theorem l2OMOd_red_pm12699 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12699 =
      denoteGraphDistributedFaithful pm_goal_1 init 8161 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 236 l2OMOdPmRef1
    8161 12699 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8161 [15314, 12663, 12673, 12687, 12699] 5 rfl 12699 (by decide)

private theorem l2OMOd_red_sm5084 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5084 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7892) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 99 l2OMOdSmReshapeA
    7892 5084 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7892 5084 [4096, 1024]

private theorem l2OMOd_red_sm5088 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5088 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7896) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 100 l2OMOdSmReshapeB
    7896 5088 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7896 5088 [4096, 1024]

private theorem l2OMOd_red_pm8192 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8192 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12686) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 238 l2OMOdPmReshapeA0
    12686 8192 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12686 8192 [2048, 1024]

private theorem l2OMOd_red_pm8193 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8193 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12687) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 242 l2OMOdPmReshapeA1
    12687 8193 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12687 8193 [2048, 1024]

private theorem l2OMOd_red_pm8204 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8204 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12698) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 239 l2OMOdPmReshapeB0
    12698 8204 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12698 8204 [2048, 1024]

private theorem l2OMOd_red_pm8205 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8205 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12699) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 243 l2OMOdPmReshapeB1
    12699 8205 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12699 8205 [2048, 1024]

private theorem l2OMOd_red_sm5087 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5087 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5086) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 107 l2OMOdSmViewA
    5086 5087 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5086 5087

private theorem l2OMOd_red_sm5091 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5091 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5090) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 108 l2OMOdSmViewB
    5090 5091 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5090 5091

private theorem l2OMOd_red_pm8198 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8198 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8196) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 253 l2OMOdPmViewA0
    8196 8198 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8196 8198

private theorem l2OMOd_red_pm8199 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8199 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8197) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 258 l2OMOdPmViewA1
    8197 8199 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8197 8199

private theorem l2OMOd_red_pm8210 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8210 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8208) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 254 l2OMOdPmViewB0
    8208 8210 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8208 8210

private theorem l2OMOd_red_pm8211 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8211 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8209) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 259 l2OMOdPmViewB1
    8209 8211 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8209 8211

private theorem l2OMOd_red_sm5093 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5093 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5092) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 112 l2OMOdSmReshapeDown
    5092 5093 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5092 5093 [4096, 512]

private theorem l2OMOd_red_pm8218 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8218 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8216) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 266 l2OMOdPmReshapeDown0
    8216 8218 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 8216 8218 [2048, 512]

private theorem l2OMOd_red_pm8219 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8219 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8217) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 269 l2OMOdPmReshapeDown1
    8217 8219 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 8217 8219 [2048, 512]

private theorem l2OMOd_red_sm5096 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5096 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5095) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 114 l2OMOdSmViewDown
    5095 5096 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5095 5096

private theorem l2OMOd_red_pm8226 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8226 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8224) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 274 l2OMOdPmViewDown0
    8224 8226 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 8224 8226

private theorem l2OMOd_red_pm8227 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8227 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8225) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 275 l2OMOdPmViewDown1
    8225 8227 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 8225 8227

private theorem l2OMOd_red_sm5086 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5086 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5084)
        (denoteGraphDistributedFaithful sm_goal_1 init 5085) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 103 l2OMOdSmLinearA
    5084 5085 5086 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5084 5085 5086

private theorem l2OMOd_red_sm5090 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5090 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5088)
        (denoteGraphDistributedFaithful sm_goal_1 init 5089) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 104 l2OMOdSmLinearB
    5088 5089 5090 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5088 5089 5090

private theorem l2OMOd_red_pm8196 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8196 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8192)
        (denoteGraphDistributedFaithful pm_goal_1 init 5085) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 245 l2OMOdPmLinearA0
    8192 5085 8196 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8192 5085 8196

private theorem l2OMOd_red_pm8197 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8197 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8193)
        (denoteGraphDistributedFaithful pm_goal_1 init 5085) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 250 l2OMOdPmLinearA1
    8193 5085 8197 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8193 5085 8197

private theorem l2OMOd_red_pm8208 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8208 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8204)
        (denoteGraphDistributedFaithful pm_goal_1 init 5089) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 246 l2OMOdPmLinearB0
    8204 5089 8208 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8204 5089 8208

private theorem l2OMOd_red_pm8209 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8209 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8205)
        (denoteGraphDistributedFaithful pm_goal_1 init 5089) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 251 l2OMOdPmLinearB1
    8205 5089 8209 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8205 5089 8209

private theorem l2OMOd_red_sm5092 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5092 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5087)
        (denoteGraphDistributedFaithful sm_goal_1 init 5091) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 111 l2OMOdSmSwi
    5087 5091 5092 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5087 5091 5092

private theorem l2OMOd_red_pm8216 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8216 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8198)
        (denoteGraphDistributedFaithful pm_goal_1 init 8210) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 261 l2OMOdPmSwi0
    8198 8210 8216 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 8198 8210 8216

private theorem l2OMOd_red_pm8217 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8217 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8199)
        (denoteGraphDistributedFaithful pm_goal_1 init 8211) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 265 l2OMOdPmSwi1
    8199 8211 8217 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 8199 8211 8217

private theorem l2OMOd_red_sm5095 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5095 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5093)
        (denoteGraphDistributedFaithful sm_goal_1 init 5094) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 113 l2OMOdSmLinearDown
    5093 5094 5095 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5093 5094 5095

private theorem l2OMOd_red_pm8224 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8224 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8218)
        (denoteGraphDistributedFaithful pm_goal_1 init 5094) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 270 l2OMOdPmLinearDown0
    8218 5094 8224 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8218 5094 8224

private theorem l2OMOd_red_pm8225 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8225 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8219)
        (denoteGraphDistributedFaithful pm_goal_1 init 5094) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 273 l2OMOdPmLinearDown1
    8219 5094 8225 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8219 5094 8225

private theorem l2OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l2OMOd_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals) (W : Tid)
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
  rw [l2OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l2OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l2OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l2OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv



private theorem ordinary_view
    {full rank0 rank1 : Tensor} {fullShape shardShape : Shape}
    (h : Ordinary2Rel full rank0 rank1 fullShape shardShape) :
    Ordinary2Rel (fw_view fullShape full) (fw_view shardShape rank0)
      (fw_view shardShape rank1) fullShape shardShape := by
  rw [fw_view_id full fullShape h.full_shape,
    fw_view_id rank0 shardShape h.rank0_shape,
    fw_view_id rank1 shardShape h.rank1_shape]
  exact h

private theorem ordinary_linear
    {full rank0 rank1 w : Tensor} (lDim inDim outDim : Nat)
    (h : Ordinary2Rel full rank0 rank1 [lDim * 2, inDim] [lDim, inDim])
    (hw : w.shape = [outDim, inDim])
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) :
    Ordinary2Rel (fw_linear full w) (fw_linear rank0 w) (fw_linear rank1 w)
      [lDim * 2, outDim] [lDim, outDim] := by
  refine {
    full_value := ?_
    full_shape := fw_linear_shape_2d' (lDim * 2) inDim outDim full w h.full_shape hw
    rank0_shape := fw_linear_shape_2d' lDim inDim outDim rank0 w h.rank0_shape hw
    rank1_shape := fw_linear_shape_2d' lDim inDim outDim rank1 w h.rank1_shape hw
  }
  rw [h.full_value]
  exact fw_mix_precision_linear_allGather0_commute_2 rank0 rank1 w
    lDim inDim outDim hl hin hout h.rank0_shape h.rank1_shape hw

/-- fw_swiglu commutes with dim-0 sharding. -/
private theorem l2OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden])
    (hc : c.shape = [shard, hidden]) (hd : d.shape = [shard, hidden]) :
    fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [fw_swiglu a c, fw_swiglu b d] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [ha]
  have hhead_cd : (([c, d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [hc]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_ab]; simp [List.set, List.getD]
  have hG_cd : (allGatherPrimDimN 0 2 0 [c, d]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_cd]; simp [List.set, List.getD]
  have hswig_shape : ∀ (g u : Tensor), u.shape = [shard, hidden] → (fw_swiglu g u).shape = [shard, hidden] := by
    intro g u hu; unfold fw_swiglu Tensor.mkShape; simp; exact hu
  have hswig_ac : (fw_swiglu a c).shape = [shard, hidden] := hswig_shape a c hc
  have hswig_bd : (fw_swiglu b d).shape = [shard, hidden] := hswig_shape b d hd
  have hhead_swig : (([fw_swiglu a c, fw_swiglu b d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hswig_ac]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_swiglu a c, fw_swiglu b d]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_swig]; simp [List.set, List.getD]
  apply Tensor.ext
  · have hLHS_shape : (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, hidden] := by
      unfold fw_swiglu Tensor.mkShape; simp; exact hG_cd
    rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    have hLHS_shape : (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, hidden] := by
      unfold fw_swiglu Tensor.mkShape; simp; exact hG_cd
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * hidden := by simpa [prodShape] using hidx
    set row := idx / hidden with hrow_def
    set j := idx % hidden with hj_def
    have hj_lt : j < hidden := by rw [hj_def]; exact Nat.mod_lt _ hhid
    have hrow_lt : row < 2 * shard := by
      rw [hrow_def]; exact Nat.div_lt_iff_lt_mul hhid |>.mpr (by linarith [hidx_bound])
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; exact Nat.div_lt_iff_lt_mul hshard |>.mpr (by linarith [hrow_lt])
    have hidx_eq : idx = (r * shard + i) * hidden + j := by
      rw [hr_def, hi_def, hj_def, hrow_def]
      have h1 : row = shard * (row / shard) + row % shard := (Nat.div_add_mod row shard).symm
      have h2 : idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
      calc idx = hidden * (idx / hidden) + idx % hidden := h2
        _ = row * hidden + j := by rw [← hrow_def, ← hj_def]; ring
        _ = (shard * (row / shard) + row % shard) * hidden + j := by rw [← h1]
        _ = (row / shard * shard + row % shard) * hidden + j := by ring
    -- LHS at idx = silu(gather_ab[idx]) * gather_cd[idx]
    have hLHS_val : valAt (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])) idx
        = siluScalar (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx) * valAt (allGatherPrimDimN 0 2 0 [c, d]) idx := by
      unfold fw_swiglu Tensor.mkShape valAt
      simp [hG_cd, prodShape]
      simp [hidx_bound]
    rw [hLHS_val]
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_cd : ∀ r' (_ : r' < 2),
        (([c, d].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hc, hd]
    have hshapes_swig : ∀ r' (_ : r' < 2),
        (([fw_swiglu a c, fw_swiglu b d].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hswig_ac, hswig_bd]
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead_ab hshapes_ab
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [c, d] (by omega) hshard hhid hhead_cd hshapes_cd
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_swiglu a c, fw_swiglu b d]
          (by omega) hshard hhid hhead_swig hshapes_swig r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_swig : [fw_swiglu a c, fw_swiglu b d].getD r (zeroTensor [shard, hidden]) =
        fw_swiglu ([a, b].getD r (zeroTensor [shard, hidden])) ([c, d].getD r (zeroTensor [shard, hidden])) := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_swig]
    set g := [a, b].getD r (zeroTensor [shard, hidden]) with hg_def
    set u := [c, d].getD r (zeroTensor [shard, hidden]) with hu_def
    have hg_shape : g.shape = [shard, hidden] := hshapes_ab r hr_lt
    have hu_shape : u.shape = [shard, hidden] := hshapes_cd r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    unfold fw_swiglu Tensor.mkShape valAt
    simp [hu_shape, hg_shape, prodShape, hloc_bound]


private theorem ordinary_swiglu
    {fullA rankA0 rankA1 fullB rankB0 rankB1 : Tensor} (lDim hidden : Nat)
    (hA : Ordinary2Rel fullA rankA0 rankA1 [lDim * 2, hidden] [lDim, hidden])
    (hB : Ordinary2Rel fullB rankB0 rankB1 [lDim * 2, hidden] [lDim, hidden])
    (hl : 0 < lDim) (hh : 0 < hidden) :
    Ordinary2Rel (fw_swiglu fullA fullB) (fw_swiglu rankA0 rankB0)
      (fw_swiglu rankA1 rankB1) [lDim * 2, hidden] [lDim, hidden] := by
  refine {
    full_value := ?_
    full_shape := by unfold fw_swiglu Tensor.mkShape; simp; exact hB.full_shape
    rank0_shape := by unfold fw_swiglu Tensor.mkShape; simp; exact hB.rank0_shape
    rank1_shape := by unfold fw_swiglu Tensor.mkShape; simp; exact hB.rank1_shape
  }
  rw [hA.full_value, hB.full_value]
  exact l2OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5096 ↔ 8226/8227` ordinary relation. -/
theorem l2_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8217)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5096)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8227)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5093)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8219)
      [4096, 512] [2048, 512] := by
    rw [l2OMOd_red_sm5093 initSM, l2OMOd_red_pm8218 initPM, l2OMOd_red_pm8219 initPM]
    exact ordinary_view hSwi
  have hwD := l2OMOd_weight_eq initSM initPM hInit initGoal_5094 (by native_decide)
    5094 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l2OMOd_weight_shape initPM hPM 5094 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5095)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8224)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8225)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMOd_red_sm5095 initSM, l2OMOd_red_pm8224 initPM,
      l2OMOd_red_pm8225 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l2OMOd_red_sm5096 initSM, l2OMOd_red_pm8226 initPM, l2OMOd_red_pm8227 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l2_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5069)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8161)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5096)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8227)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5084)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8193)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMOd_red_sm5084 initSM, l2OMOd_red_pm8192 initPM,
      l2OMOd_red_pm8193 initPM, l2OMOd_red_sm12686 initSM,
      l2OMOd_red_pm12686 initPM, l2OMOd_red_pm12687 initPM]
    exact ordinary_view hNorm
  have hwA := l2OMOd_weight_eq initSM initPM hInit initGoal_5085 (by native_decide)
    5085 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l2OMOd_weight_shape initPM hPM 5085 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5086)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8196)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8197)
      [4096, 512] [2048, 512] := by
    rw [l2OMOd_red_sm5086 initSM, l2OMOd_red_pm8196 initPM,
      l2OMOd_red_pm8197 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5087)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8198)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8199)
      [4096, 512] [2048, 512] := by
    rw [l2OMOd_red_sm5087 initSM, l2OMOd_red_pm8198 initPM,
      l2OMOd_red_pm8199 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5088)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8204)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8205)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMOd_red_sm5088 initSM, l2OMOd_red_pm8204 initPM,
      l2OMOd_red_pm8205 initPM, l2OMOd_red_sm12698 initSM,
      l2OMOd_red_pm12698 initPM, l2OMOd_red_pm12699 initPM]
    exact ordinary_view hNorm
  have hwB := l2OMOd_weight_eq initSM initPM hInit initGoal_5089 (by native_decide)
    5089 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l2OMOd_weight_shape initPM hPM 5089 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5090)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8209)
      [4096, 512] [2048, 512] := by
    rw [l2OMOd_red_sm5090 initSM, l2OMOd_red_pm8208 initPM,
      l2OMOd_red_pm8209 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5091)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8211)
      [4096, 512] [2048, 512] := by
    rw [l2OMOd_red_sm5091 initSM, l2OMOd_red_pm8210 initPM,
      l2OMOd_red_pm8211 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8217)
      [4096, 512] [2048, 512] := by
    rw [l2OMOd_red_sm5092 initSM, l2OMOd_red_pm8216 initPM,
      l2OMOd_red_pm8217 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l2_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l2_ordinary_moe_down_from_swiglu
#print axioms l2_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
