/- Manual proof for Goal 23 (split file). -/
import denote.GeneratedData
import denote.Goal_23

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.ManualProofs

/-!
## Goal 23

Outline:
- Unfold `goal_23_stmt_cut`.
- Use `goal_23_cut_initGoals` to obtain intermediate consistency for tid=24.
- Unfold `denoteGraph` for `sm_goal_23` and `pm_goal_23`.
- Use `BW_linear` lemma to show shard reconstruction equals SM output for tid=23.
-/

-- goal_23_proof omitted: not required for the current task.

end TrainVerify.Denote.ManualProofs
