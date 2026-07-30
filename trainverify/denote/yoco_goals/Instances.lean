/- Pattern instances.
   Migrated 2026-07-02 (A-path): pattern_N_target now binds to
   goal_N_stmt_cut; converting back to goal_N_stmt requires the
   corresponding Goal_N_CutToFull bridge.

   Goals 1/2/3/4 are non-base (have prereqs) — their cut_to_full
   bridges are not auto-emittable yet (blocker: denoteGraph_slice_
   self_agrees). They are left as sorry-in-uncut until either:
     - M2 non-base emitter is fixed, OR
     - Hand-written per-goal cut_to_full bridges are provided.

   Goal 5 IS base (goal_5_cut_initGoals = initGoals) so has a
   working auto-emitted Goal_5_CutToFull.lean.
-/
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

/-- Goal 1: non-base, cut_to_full bridge missing. Left as sorry pending
    non-base emitter fix. -/
theorem prove_goal_1_from_pattern_1 : goal_1_stmt := by
  sorry -- Requires Goal_1_CutToFull.lean (blocked on non-base emitter)

/-- Goal 2: non-base, cut_to_full bridge missing. Pattern_2 proves
    goal_2_stmt_cut; bridge to goal_2_stmt needs Goal_2_CutToFull.lean. -/
theorem prove_goal_2_from_pattern_2 : goal_2_stmt := by
  sorry -- Requires Goal_2_CutToFull.lean (blocked on non-base emitter)

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
   turning that conditional theorem into the raw `goal_3_stmt_cut` is not valid,
   so its raw cut instance remains `sorry`. No cut-to-full bridge is emitted for
   either goal because the corresponding full-graph equalities are false. -/

/-- Goal 3: Pattern_3 proves the honest conditional `goal_3_stmt_with_pins`, not
    the raw cut statement. Discharging the 12 pin assumptions is separate work. -/
theorem prove_goal_3_from_pattern_3 : goal_3_stmt_cut := by
  sorry

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
