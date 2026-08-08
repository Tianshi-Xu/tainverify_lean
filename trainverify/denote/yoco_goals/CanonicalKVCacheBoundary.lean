/- Canonical Goal 1: faithful K/V cache source boundary at SM 5595 and PM 9722/9723. -/
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

private def cKVCSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5578, 5591], outs := [5592] }
private def cKVCPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9666, 9702], outs := [9708] }
private def cKVCPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9667, 9703], outs := [9709] }

private def cKVCSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5573, 5592], outs := [5593] }
private def cKVCPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9656, 9708], outs := [9712] }
private def cKVCPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9657, 9709], outs := [9713] }

private def cKVCSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5593], outs := [5594] }
private def cKVCPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9712], outs := [9718] }
private def cKVCPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9713], outs := [9719] }

private def cKVCSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8341, 5594], outs := [5595] }
private def cKVCPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15810, 9718], outs := [9722] }
private def cKVCPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15818, 9719], outs := [9723] }

private theorem cKVC_red_sm5592 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5592 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5591) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 466 cKVCSmMul
    5578 5591 5592 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5578 5591 5592

private theorem cKVC_red_pm9708 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9708 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9702) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1032 cKVCPmMul0
    9666 9702 9708 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9666 9702 9708

private theorem cKVC_red_pm9709 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9709 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9703) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1033 cKVCPmMul1
    9667 9703 9709 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9667 9703 9709

private theorem cKVC_red_sm5593 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5593 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5592) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 467 cKVCSmJoin
    5573 5592 5593 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5573 5592 5593

private theorem cKVC_red_pm9712 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9712 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9708) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1034 cKVCPmJoin0
    9656 9708 9712 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9656 9708 9712

private theorem cKVC_red_pm9713 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9713 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9709) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1035 cKVCPmJoin1
    9657 9709 9713 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9657 9709 9713

private theorem cKVC_red_sm5594 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5594 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5593 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 468 cKVCSmFloat
    5593 5594 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5593 5594 []

private theorem cKVC_red_pm9718 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9712 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1036 cKVCPmFloat0
    9712 9718 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9712 9718 []

private theorem cKVC_red_pm9719 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9719 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9713 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1037 cKVCPmFloat1
    9713 9719 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9713 9719 []

private theorem cKVC_red_sm5595 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5595 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8341)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5594) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 469 cKVCSmOutput
    8341 5594 5595 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8341 5594 5595

private theorem cKVC_red_pm9722 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9722 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15810)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9718) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1038 cKVCPmOutput0
    15810 9718 9722 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15810 9718 9722

private theorem cKVC_red_pm9723 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9723 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15818)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9719) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1039 cKVCPmOutput1
    15818 9719 9723 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15818 9719 9723

/-- The real canonical cache-source tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5595 ↔ 9722/9723` relation consumed by L22 K/V.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem canonical_kv_cache_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8341)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15810)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5591)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5591)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5592)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9709)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVC_red_sm5592 initSM, cKVC_red_pm9708 initPM,
      cKVC_red_pm9709 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5593)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9713)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVC_red_sm5593 initSM, cKVC_red_pm9712 initPM,
      cKVC_red_pm9713 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5594)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9718)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9719)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVC_red_sm5594 initSM, cKVC_red_pm9718 initPM,
      cKVC_red_pm9719 initPM]
    exact hJoin
  rw [cKVC_red_sm5595 initSM, cKVC_red_pm9722 initPM,
    cKVC_red_pm9723 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms canonical_kv_cache_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns

