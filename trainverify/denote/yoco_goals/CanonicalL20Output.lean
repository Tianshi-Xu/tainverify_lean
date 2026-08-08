/- Canonical Goal 1, layer 20: faithful attention projection and residual output. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLinearRel
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

private def cL20SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6152], outs := [6154],
    params := [4096, 1024] }
private def cL20SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6154], outs := [6155],
    params := [4096, 1024] }
private def cL20SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6155, 6156],
    outs := [6157] }
private def cL20SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6157], outs := [6158],
    params := [4096, 1024] }
private def cL20SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6158], outs := [6159] }
private def cL20SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8894, 6159], outs := [6160] }

private def cL20PmReshape00 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11324], outs := [11326],
    params := [2048, 1024] }
private def cL20PmReshape01 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11325], outs := [11327],
    params := [2048, 1024] }
private def cL20PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11326], outs := [11332],
    params := [2048, 1024] }
private def cL20PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11327], outs := [11333],
    params := [2048, 1024] }
private def cL20PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11332, 6156],
    outs := [11336] }
private def cL20PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11333, 6156],
    outs := [11337] }
private def cL20PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11336], outs := [11346],
    params := [2048, 1024] }
private def cL20PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11337], outs := [11347],
    params := [2048, 1024] }
private def cL20PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11346], outs := [11350] }
private def cL20PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11347], outs := [11351] }
private def cL20PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16410, 11350], outs := [11354] }
private def cL20PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16418, 11351], outs := [11355] }

private theorem cL20_red_sm6154 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6154 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6152) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 856 cL20SmReshape0
    6152 6154 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6152 6154 [4096, 1024]

private theorem cL20_red_pm11326 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11326 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11324) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1875 cL20PmReshape00
    11324 11326 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmReshape00
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11324 11326 [2048, 1024]

private theorem cL20_red_pm11327 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11327 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11325) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1876 cL20PmReshape01
    11325 11327 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmReshape01
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11325 11327 [2048, 1024]

private theorem cL20_red_sm6155 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6155 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6154) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 857 cL20SmReshape1
    6154 6155 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6154 6155 [4096, 1024]

private theorem cL20_red_pm11332 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11332 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11326) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1877 cL20PmReshape10
    11326 11332 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11326 11332 [2048, 1024]

private theorem cL20_red_pm11333 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11333 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11327) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1878 cL20PmReshape11
    11327 11333 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11327 11333 [2048, 1024]

private theorem cL20_red_sm6157 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6157 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6155)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6156) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 858 cL20SmLinear
    6155 6156 6157 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL20SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6155 6156 6157

private theorem cL20_red_pm11336 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11336 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11332)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6156) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1879 cL20PmLinear0
    11332 6156 11336 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL20PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11332 6156 11336

private theorem cL20_red_pm11337 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11337 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11333)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6156) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1880 cL20PmLinear1
    11333 6156 11337 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL20PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11333 6156 11337

private theorem cL20_red_sm6158 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6158 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6157) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 859 cL20SmView
    6157 6158 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6157 6158

private theorem cL20_red_pm11346 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11346 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11336) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1881 cL20PmView0
    11336 11346 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11336 11346

private theorem cL20_red_pm11347 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11347 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11337) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1882 cL20PmView1
    11337 11347 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11337 11347

private theorem cL20_red_sm6159 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6159 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6158 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 860 cL20SmFloat
    6158 6159 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6158 6159 []

private theorem cL20_red_pm11350 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11350 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11346 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1883 cL20PmFloat0
    11346 11350 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11346 11350 []

private theorem cL20_red_pm11351 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11351 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11347 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1884 cL20PmFloat1
    11347 11351 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11347 11351 []

private theorem cL20_red_sm6160 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6160 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8894)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6159) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 861 cL20SmAdd
    8894 6159 6160 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL20SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8894 6159 6160

private theorem cL20_red_pm11354 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11354 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16410)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11350) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1885 cL20PmAdd0
    16410 11350 11354 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL20PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16410 11350 11354

private theorem cL20_red_pm11355 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11355 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16418)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11351) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1886 cL20PmAdd1
    16418 11351 11355 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL20PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16418 11351 11355

/-- The real canonical L20 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l20_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6152)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11325)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6156 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6156)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6156).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6159)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11350)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11351)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6154)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11326)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11327)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL20_red_sm6154 initSM, cL20_red_pm11326 initPM, cL20_red_pm11327 initPM]
    exact Zigzag2Rel.view_id' hAttention
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11332)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11333)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL20_red_sm6155 initSM, cL20_red_pm11332 initPM, cL20_red_pm11333 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11336)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11337)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL20_red_sm6157 initSM, cL20_red_pm11336 initPM, cL20_red_pm11337 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6158)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11347)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL20_red_sm6158 initSM, cL20_red_pm11346 initPM, cL20_red_pm11347 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL20_red_sm6159 initSM, cL20_red_pm11350 initPM, cL20_red_pm11351 initPM]
  exact hView

/-- Canonical L20 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `6160 ↔ 11354/11355` relation is a conclusion, never a
caller contract. -/
theorem canonical_l20_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8894)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16410)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16418)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6152)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11325)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6156 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6156)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6156).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l20_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL20_red_sm6160 initSM, cL20_red_pm11354 initPM, cL20_red_pm11355 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l20_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
