/- Canonical Goal 1, layer 14: faithful MoE join and residual output. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagBroadcastMul
import denote.yoco_goals.ZigzagPointwiseRel

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

private def l14ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5852, 5865], outs := [5866] }
private def l14ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10464, 10500], outs := [10506] }
private def l14ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10465, 10501], outs := [10507] }

private def l14ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5847, 5866], outs := [5867] }
private def l14ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10454, 10506], outs := [10510] }
private def l14ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10455, 10507], outs := [10511] }

private def l14ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5867], outs := [5868] }
private def l14ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10510], outs := [10516] }
private def l14ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10511], outs := [10517] }

private def l14ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8668, 5868], outs := [5869] }
private def l14ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16234, 10516], outs := [10520] }
private def l14ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16242, 10517], outs := [10521] }

private theorem l14ZMo_red_sm5866 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5866 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5852)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5865) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 673 l14ZMoSmMul
    5852 5865 5866 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5852 5865 5866

private theorem l14ZMo_red_pm10506 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10506 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10464)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10500) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1476 l14ZMoPmMul0
    10464 10500 10506 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10464 10500 10506

private theorem l14ZMo_red_pm10507 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10507 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10465)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10501) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1477 l14ZMoPmMul1
    10465 10501 10507 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10465 10501 10507

private theorem l14ZMo_red_sm5867 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5867 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5847)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5866) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 674 l14ZMoSmJoin
    5847 5866 5867 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5847 5866 5867

private theorem l14ZMo_red_pm10510 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10510 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10454)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10506) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1478 l14ZMoPmJoin0
    10454 10506 10510 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 10454 10506 10510

private theorem l14ZMo_red_pm10511 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10511 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10455)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10507) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1479 l14ZMoPmJoin1
    10455 10507 10511 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 10455 10507 10511

private theorem l14ZMo_red_sm5868 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5868 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5867 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 675 l14ZMoSmFloat
    5867 5868 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5867 5868 []

private theorem l14ZMo_red_pm10516 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10516 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10510 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1480 l14ZMoPmFloat0
    10510 10516 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10510 10516 []

private theorem l14ZMo_red_pm10517 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10517 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10511 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1481 l14ZMoPmFloat1
    10511 10517 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10511 10517 []

private theorem l14ZMo_red_sm5869 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5869 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8668)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5868) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 676 l14ZMoSmOutput
    8668 5868 5869 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8668 5868 5869

private theorem l14ZMo_red_pm10520 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10520 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16234)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10516) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1482 l14ZMoPmOutput0
    16234 10516 10520 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16234 10516 10520

private theorem l14ZMo_red_pm10521 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10521 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16242)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10517) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1483 l14ZMoPmOutput1
    16242 10517 10521 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16242 10517 10521

/-- The real canonical L14 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5869 ↔ 10520/10521` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l14_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8668)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16242)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5847)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10455)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5852)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10464)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10465)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5865)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10500)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10501)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10521)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5852)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10464)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10465)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5865)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10500)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10501)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5866)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10506)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10507)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMo_red_sm5866 initSM, l14ZMo_red_pm10506 initPM,
      l14ZMo_red_pm10507 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5867)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10510)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10511)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMo_red_sm5867 initSM, l14ZMo_red_pm10510 initPM,
      l14ZMo_red_pm10511 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5868)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10516)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10517)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMo_red_sm5868 initSM, l14ZMo_red_pm10516 initPM,
      l14ZMo_red_pm10517 initPM]
    exact hJoin
  rw [l14ZMo_red_sm5869 initSM, l14ZMo_red_pm10520 initPM,
    l14ZMo_red_pm10521 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
