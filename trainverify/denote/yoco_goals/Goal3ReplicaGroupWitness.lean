import denote.yoco_goals.Goal_3

set_option linter.style.nativeDecide false

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.Goal3ReplicaGroupWitness

private def smSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [4692, 4693, 4689, 4694, 4695], outs := [4696],
    params := [16, 4, 64, 64, 1, 512] }

private def pmSliding0R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [7433, 7435, 7421, 4694, 4695], outs := [7437],
    params := [16, 4, 64, 64, 1, 512] }

private def pmSliding0R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [7434, 7436, 7422, 4694, 4695], outs := [7438],
    params := [16, 4, 64, 64, 1, 512] }

example : sm_goal_3.replicaBuddies smSliding0 = [smSliding0] := by native_decide
example : pm_goal_3.replicaBuddies pmSliding0R0 = [pmSliding0R0, pmSliding0R1] := by
  native_decide
example : pm_goal_3.replicaBuddies pmSliding0R1 = [pmSliding0R0, pmSliding0R1] := by
  native_decide

end TrainVerify.Denote.Goal3ReplicaGroupWitness
