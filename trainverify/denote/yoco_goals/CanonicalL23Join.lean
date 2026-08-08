/- Canonical Goal 1, layer 23: faithful gated multiply and MoE join. -/
import denote.yoco_goals.CanonicalL23Output
import denote.yoco_goals.ZigzagBroadcastMul

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

private def cL23jSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [6230, 6243], outs := [6244] }
private def cL23jPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11542, 11578], outs := [11584] }
private def cL23jPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11543, 11579], outs := [11585] }
private def cL23jSmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [6225, 6244], outs := [6245] }
private def cL23jPmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11532, 11584], outs := [11588] }
private def cL23jPmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11533, 11585], outs := [11589] }

private theorem cL23j_red_sm6244 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6244 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 6230)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6243) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 918 cL23jSmMul
    6230 6243 6244 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23jSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 6230 6243 6244

private theorem cL23j_red_pm11584 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11584 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11542)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11578) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2008 cL23jPmMul0
    11542 11578 11584 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23jPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 11542 11578 11584

private theorem cL23j_red_pm11585 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11585 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11543)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11579) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2009 cL23jPmMul1
    11543 11579 11585 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23jPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 11543 11579 11585

private theorem cL23j_red_sm6245 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6245 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 6225)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6244) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 919 cL23jSmAdd
    6225 6244 6245 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23jSmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 6225 6244 6245

private theorem cL23j_red_pm11588 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11588 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11532)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2010 cL23jPmAdd0
    11532 11584 11588 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23jPmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 11532 11584 11588

private theorem cL23j_red_pm11589 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11589 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11533)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11585) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2011 cL23jPmAdd1
    11533 11585 11589 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23jPmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 11533 11585 11589

/-- The final two operators of the canonical L23 MoE branch, reduced against the
real Goal-1 graph.  The three premises are the independently composable upstream
lineage obligations (GMM expert output, scalar gate, and down projection); the
join relation itself is derived rather than accepted from the caller. -/
theorem canonical_l23_join_from_branch_inputs (initSM initPM : Store)
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6225)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11532)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11533)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11542)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11543)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6243)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11579)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6245)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11542)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11543)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6243)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11579)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6244)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23j_red_sm6244 initSM, cL23j_red_pm11584 initPM, cL23j_red_pm11585 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown' (by decide) (by decide)
  rw [cL23j_red_sm6245 initSM, cL23j_red_pm11588 initPM, cL23j_red_pm11589 initPM]
  exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
