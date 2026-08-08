/- Canonical Goal 1, layer 21: faithful MoE join and residual output. -/
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

private def cL21oSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [6176, 6189], outs := [6190] }
private def cL21oPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11388, 11424], outs := [11430] }
private def cL21oPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11389, 11425], outs := [11431] }

private def cL21oSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [6171, 6190], outs := [6191] }
private def cL21oPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11378, 11430], outs := [11434] }
private def cL21oPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11379, 11431], outs := [11435] }

private def cL21oSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6191], outs := [6192] }
private def cL21oPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11434], outs := [11440] }
private def cL21oPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11435], outs := [11441] }

private def cL21oSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8902, 6192], outs := [6193] }
private def cL21oPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16426, 11440], outs := [11444] }
private def cL21oPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16434, 11441], outs := [11445] }

private theorem cL21o_red_sm6190 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6190 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 6176)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6189) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 883 cL21oSmMul
    6176 6189 6190 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 6176 6189 6190

private theorem cL21o_red_pm11430 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11430 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11388)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11424) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1932 cL21oPmMul0
    11388 11424 11430 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 11388 11424 11430

private theorem cL21o_red_pm11431 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11431 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11389)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11425) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1933 cL21oPmMul1
    11389 11425 11431 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 11389 11425 11431

private theorem cL21o_red_sm6191 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6191 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 6171)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6190) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 884 cL21oSmJoin
    6171 6190 6191 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 6171 6190 6191

private theorem cL21o_red_pm11434 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11434 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11378)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11430) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1934 cL21oPmJoin0
    11378 11430 11434 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 11378 11430 11434

private theorem cL21o_red_pm11435 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11435 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11379)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11431) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1935 cL21oPmJoin1
    11379 11431 11435 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 11379 11431 11435

private theorem cL21o_red_sm6192 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6192 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6191 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 885 cL21oSmFloat
    6191 6192 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21oSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6191 6192 []

private theorem cL21o_red_pm11440 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11440 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11434 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1936 cL21oPmFloat0
    11434 11440 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11434 11440 []

private theorem cL21o_red_pm11441 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11441 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11435 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1937 cL21oPmFloat1
    11435 11441 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11435 11441 []

private theorem cL21o_red_sm6193 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6193 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8902)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6192) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 886 cL21oSmOutput
    8902 6192 6193 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8902 6192 6193

private theorem cL21o_red_pm11444 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11444 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16426)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11440) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1938 cL21oPmOutput0
    16426 11440 11444 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16426 11440 11444

private theorem cL21o_red_pm11445 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11445 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16434)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11441) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1939 cL21oPmOutput1
    16434 11441 11445 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21oPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16434 11441 11445

/-- The real canonical L21 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `6193 ↔ 11444/11445` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem canonical_l21_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8902)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16426)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6171)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11378)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11379)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11388)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11389)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6189)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11424)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11425)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11388)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11389)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6189)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11424)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11425)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6190)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21o_red_sm6190 initSM, cL21o_red_pm11430 initPM,
      cL21o_red_pm11431 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6191)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11435)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21o_red_sm6191 initSM, cL21o_red_pm11434 initPM,
      cL21o_red_pm11435 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11440)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11441)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21o_red_sm6192 initSM, cL21o_red_pm11440 initPM,
      cL21o_red_pm11441 initPM]
    exact hJoin
  rw [cL21o_red_sm6193 initSM, cL21o_red_pm11444 initPM,
    cL21o_red_pm11445 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
