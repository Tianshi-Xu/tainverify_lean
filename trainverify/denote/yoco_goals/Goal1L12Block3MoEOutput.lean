/- Canonical Goal 1, layer 12: faithful MoE join and residual output. -/
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

private def l12ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5744, 5757], outs := [5758] }
private def l12ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10156, 10192], outs := [10198] }
private def l12ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10157, 10193], outs := [10199] }

private def l12ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5739, 5758], outs := [5759] }
private def l12ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10146, 10198], outs := [10202] }
private def l12ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10147, 10199], outs := [10203] }

private def l12ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5759], outs := [5760] }
private def l12ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10202], outs := [10208] }
private def l12ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10203], outs := [10209] }

private def l12ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8590, 5760], outs := [5761] }
private def l12ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16170, 10208], outs := [10212] }
private def l12ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16178, 10209], outs := [10213] }

private theorem l12ZMo_red_sm5758 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5758 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5744)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5757) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 603 l12ZMoSmMul
    5744 5757 5758 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5744 5757 5758

private theorem l12ZMo_red_pm10198 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10198 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10156)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10192) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1324 l12ZMoPmMul0
    10156 10192 10198 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10156 10192 10198

private theorem l12ZMo_red_pm10199 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10199 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10157)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10193) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1325 l12ZMoPmMul1
    10157 10193 10199 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10157 10193 10199

private theorem l12ZMo_red_sm5759 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5759 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5739)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5758) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 604 l12ZMoSmJoin
    5739 5758 5759 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5739 5758 5759

private theorem l12ZMo_red_pm10202 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10202 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10146)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10198) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1326 l12ZMoPmJoin0
    10146 10198 10202 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 10146 10198 10202

private theorem l12ZMo_red_pm10203 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10203 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10147)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10199) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1327 l12ZMoPmJoin1
    10147 10199 10203 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 10147 10199 10203

private theorem l12ZMo_red_sm5760 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5760 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5759 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 605 l12ZMoSmFloat
    5759 5760 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5759 5760 []

private theorem l12ZMo_red_pm10208 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10208 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10202 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1328 l12ZMoPmFloat0
    10202 10208 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10202 10208 []

private theorem l12ZMo_red_pm10209 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10209 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10203 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1329 l12ZMoPmFloat1
    10203 10209 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10203 10209 []

private theorem l12ZMo_red_sm5761 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5761 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8590)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5760) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 606 l12ZMoSmOutput
    8590 5760 5761 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8590 5760 5761

private theorem l12ZMo_red_pm10212 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10212 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16170)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10208) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1330 l12ZMoPmOutput0
    16170 10208 10212 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16170 10208 10212

private theorem l12ZMo_red_pm10213 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10213 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16178)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10209) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1331 l12ZMoPmOutput1
    16178 10209 10213 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16178 10209 10213

/-- The real canonical L21 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5761 ↔ 10212/10213` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem goal1_l12_block3_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8590)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16170)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16178)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10146)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10147)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5744)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5757)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5761)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10213)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5744)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5757)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5758)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10198)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10199)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMo_red_sm5758 initSM, l12ZMo_red_pm10198 initPM,
      l12ZMo_red_pm10199 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5759)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10203)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMo_red_sm5759 initSM, l12ZMo_red_pm10202 initPM,
      l12ZMo_red_pm10203 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5760)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10209)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMo_red_sm5760 initSM, l12ZMo_red_pm10208 initPM,
      l12ZMo_red_pm10209 initPM]
    exact hJoin
  rw [l12ZMo_red_sm5761 initSM, l12ZMo_red_pm10212 initPM,
    l12ZMo_red_pm10213 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
