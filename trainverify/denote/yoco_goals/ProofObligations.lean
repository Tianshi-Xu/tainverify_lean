/- YOCO-MoE proof obligation index (completed).

All five pattern bodies are proved. `Instances.lean` exports each pattern under
its strongest honest statement shape:

* goal 1: labels-in-vocabulary contract;
* goal 2: shuffle-free cut statement;
* goal 3: 12 cu-seqlens pins contract;
* goal 4: shuffle-free cut statement;
* goal 5: valid full-graph statement via generated cut-to-full bridge.

`MainTheorem.lean` no longer composes the invalid historical five-way
`all_goals_stmt`. It proves `yoco_moe_corrected_main`, combining direct
`denoteGraphDistributedFaithful` full results for sound goals 1/2/5, the honest
pattern tier above, and the ownership-aware emitted-corpus shape. Full goals
3/4 are source/runtime findings on the audited CP2 graph, not open Lean proof
obligations.
-/
import denote.yoco_goals.MainTheorem

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedProofObligations

/-- No optional segment package remains open. -/
def optionalSegmentProofPackageCount : Nat := 0

/-- Five pattern packages are complete under their honest contracts. -/
def completedPatternProofCount : Nat := 5

/-- No human proof body remains open in the YOCO goal ecosystem. -/
def humanProofObligationCount : Nat := 0

end TrainVerify.Denote.GeneratedProofObligations
