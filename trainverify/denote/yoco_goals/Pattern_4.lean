/- Pattern_4 proof: goal_4_stmt_cut.
   Pattern: 4
   Op flavour: topk_routing per-layer, context-parallel
     SM=25 ops (24 topk_routing + 1 FW_stack), PM=55 ops
     (24 chunk pairs + 24 topk pairs + 2 stacks + 1 allGather)

   The stack collects the `.snd.snd` output (gate_scores = softmax logits)
   of each topk_routing, NOT the routing_map.

   Status: MACHINERY LEMMA + PROOF OBLIGATIONS. The final math step
   (per-layer topk_routing sharding + stack-lift) is deferred; requires
   ~1 week of row-wise induction on softmax.
-/
import denote.yoco_goals.Goal_4
import denote.GraphSlicing

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_4_goalIds : List Nat := [4]
inductive pattern_4_target : Prop → Prop
  | goal_4 : pattern_4_target goal_4_stmt_cut

def pattern_4_stmt : Prop :=
  ∀ {target : Prop}, pattern_4_target target → target

/-!
### SM-side machinery: denote sm_goal_4 at write tid 4676.

sm_goal_4 has 25 nodes: 24 topk_routing (indices 0..23), 1 FW_stack (index 24).
Each topk_routing writes 3 tids (probs, map, scores); scores is the .snd.snd
output and is what feeds into the final FW_stack.

The stack input tids [4711, 4765, ..., 5901] are the SCORES outputs of the
24 topk_routing nodes.
-/

/-- Helper: FW_stack at position 24 writes tid 4676 = stack of 24 gate_scores.

    ⚠️ MACHINERY PROOF DEFERRED (~200 LOC of 25-step chain reduction using
    `applyNode_fw_stack_out` + `applyNode_fw_topk_routing_scores_out` +
    `applyNode_eq_of_not_mem_outs` skips). The proof structure mirrors
    Pattern_2's `denote_pm_goal_2_4674`. -/
theorem denote_sm_goal_4_4676 (initSM : Store) :
    denoteGraph sm_goal_4 initSM 4676 = fw_stack
      [(fw_topk_routing (initSM 4708) 8 1).snd.snd,
       (fw_topk_routing (initSM 4762) 8 1).snd.snd,
       (fw_topk_routing (initSM 4816) 8 1).snd.snd,
       (fw_topk_routing (initSM 4870) 8 1).snd.snd,
       (fw_topk_routing (initSM 4924) 8 1).snd.snd,
       (fw_topk_routing (initSM 4978) 8 1).snd.snd,
       (fw_topk_routing (initSM 5032) 8 1).snd.snd,
       (fw_topk_routing (initSM 5086) 8 1).snd.snd,
       (fw_topk_routing (initSM 5140) 8 1).snd.snd,
       (fw_topk_routing (initSM 5194) 8 1).snd.snd,
       (fw_topk_routing (initSM 5248) 8 1).snd.snd,
       (fw_topk_routing (initSM 5302) 8 1).snd.snd,
       (fw_topk_routing (initSM 5359) 8 1).snd.snd,
       (fw_topk_routing (initSM 5408) 8 1).snd.snd,
       (fw_topk_routing (initSM 5457) 8 1).snd.snd,
       (fw_topk_routing (initSM 5506) 8 1).snd.snd,
       (fw_topk_routing (initSM 5555) 8 1).snd.snd,
       (fw_topk_routing (initSM 5604) 8 1).snd.snd,
       (fw_topk_routing (initSM 5653) 8 1).snd.snd,
       (fw_topk_routing (initSM 5702) 8 1).snd.snd,
       (fw_topk_routing (initSM 5751) 8 1).snd.snd,
       (fw_topk_routing (initSM 5800) 8 1).snd.snd,
       (fw_topk_routing (initSM 5849) 8 1).snd.snd,
       (fw_topk_routing (initSM 5898) 8 1).snd.snd] := by
  -- Unfold denoteGraph on sm_goal_4 (25 nodes). All 24 topk_routings are
  -- independent (different logits inputs), and the final FW_stack reads
  -- their scores outputs.
  unfold denoteGraph
  simp only [sm_goal_4, List.foldl]
  -- After simp, goal is: applyNode {..} S24 last_node 4676 = fw_stack [...]
  -- where S24 is the fold through the 24 topk nodes.
  -- The FW_stack node writes 4676, so applyNode_fw_stack_out applies.
  sorry -- Continuation: apply applyNode_fw_stack_out + prove each ins is
        -- the correct scores value. Would need per-scores-tid reduction lemma.

theorem prove_goal_4 : goal_4_stmt_cut := by
  sorry -- Math: apply per-layer topk sharding lemma × 24, then stack-lift.
        -- Row-wise argument on softmax + topk_routing. Est. 1 week.

theorem prove_pattern_4 : pattern_4_stmt := by
  intro target h
  cases h
  exact prove_goal_4

end TrainVerify.Denote.GeneratedPatterns
