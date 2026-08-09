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

private def l12B2ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5690, 5703], outs := [5704] }
private def l12B2ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10002, 10038], outs := [10044] }
private def l12B2ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10003, 10039], outs := [10045] }

private def l12B2ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5685, 5704], outs := [5705] }
private def l12B2ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9992, 10044], outs := [10048] }
private def l12B2ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9993, 10045], outs := [10049] }

private def l12B2ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5705], outs := [5706] }
private def l12B2ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10048], outs := [10054] }
private def l12B2ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10049], outs := [10055] }

private def l12B2ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8551, 5706], outs := [5707] }
private def l12B2ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16138, 10054], outs := [10058] }
private def l12B2ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16146, 10055], outs := [10059] }

private theorem l12B2ZMo_red_sm5704 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5704 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5690)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5703) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 568 l12B2ZMoSmMul
    5690 5703 5704 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5690 5703 5704

private theorem l12B2ZMo_red_pm10044 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10044 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10002)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10038) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1248 l12B2ZMoPmMul0
    10002 10038 10044 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10002 10038 10044

private theorem l12B2ZMo_red_pm10045 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10045 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10003)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10039) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1249 l12B2ZMoPmMul1
    10003 10039 10045 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10003 10039 10045

private theorem l12B2ZMo_red_sm5705 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5705 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5685)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5704) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 569 l12B2ZMoSmJoin
    5685 5704 5705 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5685 5704 5705

private theorem l12B2ZMo_red_pm10048 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10048 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9992)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10044) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1250 l12B2ZMoPmJoin0
    9992 10044 10048 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9992 10044 10048

private theorem l12B2ZMo_red_pm10049 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10049 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9993)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10045) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1251 l12B2ZMoPmJoin1
    9993 10045 10049 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9993 10045 10049

private theorem l12B2ZMo_red_sm5706 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5706 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5705 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 570 l12B2ZMoSmFloat
    5705 5706 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5705 5706 []

private theorem l12B2ZMo_red_pm10054 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10054 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10048 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1252 l12B2ZMoPmFloat0
    10048 10054 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10048 10054 []

private theorem l12B2ZMo_red_pm10055 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10055 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10049 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1253 l12B2ZMoPmFloat1
    10049 10055 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10049 10055 []

private theorem l12B2ZMo_red_sm5707 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5707 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8551)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5706) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 571 l12B2ZMoSmOutput
    8551 5706 5707 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8551 5706 5707

private theorem l12B2ZMo_red_pm10058 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10058 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16138)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10054) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1254 l12B2ZMoPmOutput0
    16138 10054 10058 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16138 10054 10058

private theorem l12B2ZMo_red_pm10059 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10059 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16146)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10055) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1255 l12B2ZMoPmOutput1
    16146 10055 10059 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16146 10055 10059

/-- The real canonical L21 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5707 ↔ 10058/10059` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l12b2_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8551)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16138)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16146)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5685)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9993)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5690)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10002)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10003)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10038)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10039)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5690)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10002)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10003)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10038)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10039)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5704)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10045)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMo_red_sm5704 initSM, l12B2ZMo_red_pm10044 initPM,
      l12B2ZMo_red_pm10045 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5705)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10048)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10049)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMo_red_sm5705 initSM, l12B2ZMo_red_pm10048 initPM,
      l12B2ZMo_red_pm10049 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5706)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10055)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMo_red_sm5706 initSM, l12B2ZMo_red_pm10054 initPM,
      l12B2ZMo_red_pm10055 initPM]
    exact hJoin
  rw [l12B2ZMo_red_sm5707 initSM, l12B2ZMo_red_pm10058 initPM,
    l12B2ZMo_red_pm10059 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
