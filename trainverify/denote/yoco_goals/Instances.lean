/- Honest pattern instances.

   The historical file tried to coerce every pattern into the five unconditional
   full-graph `goal_N_stmt` declarations and left three `sorry`s. That API was
   semantically wrong:

   * goal 1 requires a labels-in-vocabulary caller contract;
   * goal 2 has a proven cut statement (its full faithful theorem lives on the
     distributed-faithful track);
   * goal 3 requires 12 cu-seqlens pins;
   * goal 3/4's old full-graph ordinary equalities are false on CP2;
   * goal 5 has a valid generated cut-to-full bridge.

   Each theorem below therefore exports the strongest statement actually proved,
   without `sorry` or impossible strengthening. -/
import denote.yoco_goals.Pattern_1
import denote.yoco_goals.Pattern_2
import denote.yoco_goals.Pattern_3
import denote.yoco_goals.Pattern_4
import denote.yoco_goals.Pattern_5
import denote.yoco_goals.Goal_5_CutToFull

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.GeneratedPatternInstances

/-- Goal 1's honest instance. Cross-entropy correctness needs the caller's
    labels-in-vocabulary contract, so the unconditional legacy `goal_1_stmt`
    is intentionally not exported. -/
theorem prove_goal_1_from_pattern_1 : goal_1_stmt_with_labels :=
  prove_pattern_1 pattern_1_target.goal_1

/-- Goal 2's proven shuffle-free cut instance. The corrected faithful full-graph
    theorem uses the direct `denoteGraphDistributedFaithful` proof instead of
    pretending that the legacy non-base cut has an automatic lift. -/
theorem prove_goal_2_from_pattern_2 : goal_2_stmt_cut :=
  prove_pattern_2 pattern_2_target.goal_2

/- Goals 3 and 4 are blocked for a DIFFERENT and permanent reason than 1/2.

   There is no `goal_3_stmt` / `goal_4_stmt` any more, and there never can be:
   those statements are FALSE, not merely unproven. Both goals stack the 24
   per-layer routing tensors; 12 of those members are produced after the CP2
   `FW_maybe_shuffle` and are zigzag-owned, while the goal asserted one uniform
   ordinary dim-1 gather over all 24.

   `trainverify/GOAL_3_4_LAYOUT_SPLIT.md` records the audited root cause: a
   concrete cp=2 fixture: the ordinary gather of the zigzag shards has the same
   SHAPE as the contiguous tensor but disagrees in value at flat index 2 (6
   versus 2). Shape checking cannot see the difference, which is why the emitter
   produced these goals in the first place. `Verdict/graph_to_lean.py` now
   refuses to emit them and states the true obligations as `ZigzagLineageGoal`s.

   The CUT statements are a different matter and remain sound: `pm_goal_3` /
   `pm_goal_4` are sliced subgraphs built from `ChunkPrim` with no shuffle in
   them. Pattern_4 proves its raw cut statement sorry-free. Pattern_3 proves
   `goal_3_stmt_with_pins`, which requires 12 explicit cu_seqlens value pins;
   turning that conditional theorem into the raw `goal_3_stmt_cut` is not valid.
   The instance below therefore exports the conditional statement directly. No
   cut-to-full bridge is emitted for either goal because the corresponding
   full-graph equalities are false. -/

/-- Goal 3's honest instance. The 12 cu-seqlens pins are part of the caller
    contract; dropping them would strengthen the theorem invalidly. -/
theorem prove_goal_3_from_pattern_3 : goal_3_stmt_with_pins :=
  prove_pattern_3 pattern_3_target.goal_3

/-- Goal 4: stated over the cut. Pattern_4 discharges it outright, so this is no
    longer a `sorry` — the previous `sorry` was owed entirely to the impossible
    cut-to-full lift, not to any gap in Pattern_4. -/
theorem prove_goal_4_from_pattern_4 : goal_4_stmt_cut :=
  prove_pattern_4 pattern_4_target.goal_4

/-- Goal 5: base, has working cut_to_full bridge. ✅ -/
theorem prove_goal_5_from_pattern_5 : goal_5_stmt := by
  have hcut : goal_5_stmt_cut := prove_pattern_5 pattern_5_target.goal_5
  exact goal_5_cut_to_full hcut

end TrainVerify.Denote.GeneratedPatternInstances
