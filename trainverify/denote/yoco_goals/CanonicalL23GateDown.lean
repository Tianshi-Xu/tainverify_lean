/- Canonical Goal 1, layer 23: faithful gate and down-projection branches. -/
import denote.yoco_goals.CanonicalL23Join
import denote.MultirefGeneral
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

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

private def cL23gdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6216],
    outs := [8948, 8952, 8956, 8960, 8964], params := [5] }
private def cL23gdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11512],
    outs := [15432, 15208, 15218, 15232, 15244], params := [5] }
private def cL23gdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11513],
    outs := [15434, 15209, 15219, 15233, 15245], params := [5] }
private def cL23gdSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8956], outs := [6226],
    params := [4096, 1024] }
private def cL23gdPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15218], outs := [11534],
    params := [2048, 1024] }
private def cL23gdPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15219], outs := [11535],
    params := [2048, 1024] }
private def cL23gdSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6226, 6227],
    outs := [6228] }
private def cL23gdPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11534, 6227],
    outs := [11538] }
private def cL23gdPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11535, 6227],
    outs := [11539] }
private def cL23gdSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6228], outs := [6229],
    params := [4096, 1] }
private def cL23gdPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11538], outs := [11540],
    params := [2048, 1] }
private def cL23gdPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11539], outs := [11541],
    params := [2048, 1] }
private def cL23gdSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [6229], outs := [6230] }
private def cL23gdPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11540], outs := [11542] }
private def cL23gdPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11541], outs := [11543] }

private theorem cL23gd_red_sm8956 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8956 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6216 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 899 cL23gdSmRef
    6216 8956 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6216 [8948, 8952, 8956, 8960, 8964]
    5 rfl 8956 (by decide)

private theorem cL23gd_red_pm15218 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15218 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11512 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1967 cL23gdPmRef0
    11512 15218 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11512
    [15432, 15208, 15218, 15232, 15244] 5 rfl 15218 (by decide)

private theorem cL23gd_red_pm15219 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15219 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11513 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1968 cL23gdPmRef1
    11513 15219 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11513
    [15434, 15209, 15219, 15233, 15245] 5 rfl 15219 (by decide)

private theorem cL23gd_red_sm6226 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6226 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8956) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 901 cL23gdSmReshape
    8956 6226 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8956 6226 [4096, 1024]

private theorem cL23gd_red_pm11534 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11534 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 15218) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1969 cL23gdPmReshape0
    15218 11534 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15218 11534 [2048, 1024]

private theorem cL23gd_red_pm11535 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11535 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 15219) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1973 cL23gdPmReshape1
    15219 11535 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15219 11535 [2048, 1024]

private theorem cL23gd_red_sm6228 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6228 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6226)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6227) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 905 cL23gdSmLinear
    6226 6227 6228 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23gdSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6226 6227 6228

private theorem cL23gd_red_pm11538 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11538 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11534)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6227) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1976 cL23gdPmLinear0
    11534 6227 11538 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11534 6227 11538

private theorem cL23gd_red_pm11539 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11539 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11535)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6227) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1981 cL23gdPmLinear1
    11535 6227 11539 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11535 6227 11539

private theorem cL23gd_red_sm6229 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6229 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 6228) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 909 cL23gdSmView
    6228 6229 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 6228 6229

private theorem cL23gd_red_pm11540 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11540 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11538) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1984 cL23gdPmView0
    11538 11540 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 11538 11540

private theorem cL23gd_red_pm11541 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11541 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11539) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1989 cL23gdPmView1
    11539 11541 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 11539 11541

private theorem cL23gd_red_sm6230 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6230 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 6229) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 913 cL23gdSmSigmoid
    6229 6230 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 6229 6230

private theorem cL23gd_red_pm11542 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11542 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11540) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1992 cL23gdPmSigmoid0
    11540 11542 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 11540 11542

private theorem cL23gd_red_pm11543 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11543 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11541) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1996 cL23gdPmSigmoid1
    11541 11543 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23gdPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 11541 11543

private theorem cL23gd_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6227 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6227 ∉ n.outs) := by
  native_decide

private theorem cL23gd_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6227 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6227 := by
  have hi := (hInit initGoal_6227 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6227 pm_goal_1.numRanks _ rfl,
    show initGoal_6227.tps = [{rank := 0, tid := 6227}] from rfl,
    show initGoal_6227.ts = 6227 from rfl,
    show initGoal_6227.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6227
      (by native_decide) cL23gd_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6227
      (by native_decide) cL23gd_weight_not_written.2]
  exact hi

private theorem cL23gd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6227).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 6227 = initPM 6227 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6227
      (by native_decide) cL23gd_weight_not_written.2
  rw [e]
  exact hPM 6227 [1, 1024] (by native_decide)

/-- The canonical L23 scalar gate is derived from the shared normalized MoE input.
Every intermediate relation (multiref, reshape, projection, view, sigmoid) is
closed inside this theorem; callers provide no relation over a computed gate. -/
theorem canonical_l23_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11542)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11543)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8956)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15219)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23gd_red_sm8956 initSM, cL23gd_red_pm15218 initPM,
      cL23gd_red_pm15219 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11534)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11535)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23gd_red_sm6226 initSM, cL23gd_red_pm11534 initPM,
      cL23gd_red_pm11535 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := cL23gd_weight_eq initSM initPM hInit
  have hwShape := cL23gd_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6228)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11539)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [cL23gd_red_sm6228 initSM, cL23gd_red_pm11538 initPM,
      cL23gd_red_pm11539 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6229)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11540)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11541)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [cL23gd_red_sm6229 initSM, cL23gd_red_pm11540 initPM,
      cL23gd_red_pm11541 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6229)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11540)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11541)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [cL23gd_red_sm6230 initSM, cL23gd_red_pm11542 initPM,
    cL23gd_red_pm11543 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
