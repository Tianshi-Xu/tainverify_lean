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

/-- Helper: for scores_tid at position k (0..23), the fold through take 24
    yields the topk scores. Instantiated 24 times below via explicit split. -/
private theorem denote_sm_S24_at_scores
    (initSM : Store) (k : Nat) (logitsTid probsTid mapTid scoresTid : Tid)
    (hk : k + 1 ≤ 24)
    (h_prefix_eq : sm_goal_4.nodes.take (k+1) =
      (sm_goal_4.nodes.take k) ++
      [{ rank := (0:Nat), op := "OpName.FW_topk_routing", ins := [logitsTid],
         outs := [probsTid, mapTid, scoresTid], params := [8] }])
    (h_prefix_no_write_scores :
      ∀ n ∈ sm_goal_4.nodes.take k, scoresTid ∉ n.outs)
    (h_prefix_no_write_logits :
      ∀ n ∈ sm_goal_4.nodes.take k, logitsTid ∉ n.outs)
    (h_suffix_no_write :
      ∀ n ∈ (sm_goal_4.nodes.drop (k+1)).take (24 - (k+1)), scoresTid ∉ n.outs)
    (h_pne : probsTid ≠ scoresTid) (h_mne : mapTid ≠ scoresTid) :
    ((sm_goal_4.nodes.take 24).foldl (applyNode sm_goal_4) initSM) scoresTid =
    (fw_topk_routing (initSM logitsTid) 8 1).snd.snd := by
  have h_split : sm_goal_4.nodes.take 24 =
      sm_goal_4.nodes.take (k+1) ++ (sm_goal_4.nodes.drop (k+1)).take (24 - (k+1)) := by
    have heq : k + 1 + (24 - (k+1)) = 24 := by omega
    calc sm_goal_4.nodes.take 24
        = sm_goal_4.nodes.take (k+1 + (24 - (k+1))) := by rw [heq]
      _ = sm_goal_4.nodes.take (k+1) ++ (sm_goal_4.nodes.drop (k+1)).take (24 - (k+1)) := by
          rw [List.take_add]
  rw [h_split, List.foldl_append]
  rw [foldl_applyNode_at_not_written sm_goal_4 _ _ scoresTid h_suffix_no_write]
  rw [h_prefix_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set S_k : Store := (sm_goal_4.nodes.take k).foldl (applyNode sm_goal_4) initSM
  have h_S_k_logits : S_k logitsTid = initSM logitsTid :=
    foldl_applyNode_at_not_written sm_goal_4 _ initSM logitsTid h_prefix_no_write_logits
  have h_apply := applyNode_fw_topk_routing_scores_out sm_goal_4 S_k 0
    logitsTid probsTid mapTid scoresTid [8] h_pne h_mne
  rw [h_apply, h_S_k_logits]
  rfl

/-- Main machinery: denote sm_goal_4 at 4676 = fw_stack of 24 topk scores. -/
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
  -- sm_goal_4.nodes = topks (24) ++ [stack]. Unfold denoteGraph.
  have h_split_full : sm_goal_4.nodes = sm_goal_4.nodes.take 24 ++
      [{ rank := 0, op := "OpName.FW_stack",
         ins := [4711, 4765, 4819, 4873, 4927, 4981, 5035, 5089, 5143, 5197,
                 5251, 5305, 5362, 5411, 5460, 5509, 5558, 5607, 5656, 5705,
                 5754, 5803, 5852, 5901],
         outs := [4676], params := [] }] := by
    show sm_goal_4.nodes = _
    rfl
  unfold denoteGraph
  rw [h_split_full, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set S24 : Store := (sm_goal_4.nodes.take 24).foldl (applyNode sm_goal_4) initSM
  rw [applyNode_fw_stack_out sm_goal_4 S24 0 _ 4676 []]
  show fw_stack [S24 4711, S24 4765, S24 4819, S24 4873, S24 4927, S24 4981,
                 S24 5035, S24 5089, S24 5143, S24 5197, S24 5251, S24 5305,
                 S24 5362, S24 5411, S24 5460, S24 5509, S24 5558, S24 5607,
                 S24 5656, S24 5705, S24 5754, S24 5803, S24 5852, S24 5901] = _
  -- Reduce each S24 tid_i via denote_sm_S24_at_scores.
  -- The h_prefix_eq / h_prefix_no_write_* / h_suffix_no_write hypotheses
  -- are all provable by rfl / decide / native_decide on the concrete
  -- sm_goal_4 literal.
  have h4711 : S24 4711 = (fw_topk_routing (initSM 4708) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 0 4708 4709 4710 4711 (by omega)
      (by rfl)
      (by intro n hn; simp only [List.take_zero, List.not_mem_nil] at hn)
      (by intro n hn; simp only [List.take_zero, List.not_mem_nil] at hn)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h4765 : S24 4765 = (fw_topk_routing (initSM 4762) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 1 4762 4763 4764 4765 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h4819 : S24 4819 = (fw_topk_routing (initSM 4816) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 2 4816 4817 4818 4819 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h4873 : S24 4873 = (fw_topk_routing (initSM 4870) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 3 4870 4871 4872 4873 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h4927 : S24 4927 = (fw_topk_routing (initSM 4924) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 4 4924 4925 4926 4927 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h4981 : S24 4981 = (fw_topk_routing (initSM 4978) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 5 4978 4979 4980 4981 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5035 : S24 5035 = (fw_topk_routing (initSM 5032) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 6 5032 5033 5034 5035 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5089 : S24 5089 = (fw_topk_routing (initSM 5086) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 7 5086 5087 5088 5089 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5143 : S24 5143 = (fw_topk_routing (initSM 5140) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 8 5140 5141 5142 5143 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5197 : S24 5197 = (fw_topk_routing (initSM 5194) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 9 5194 5195 5196 5197 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5251 : S24 5251 = (fw_topk_routing (initSM 5248) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 10 5248 5249 5250 5251 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5305 : S24 5305 = (fw_topk_routing (initSM 5302) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 11 5302 5303 5304 5305 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5362 : S24 5362 = (fw_topk_routing (initSM 5359) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 12 5359 5360 5361 5362 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5411 : S24 5411 = (fw_topk_routing (initSM 5408) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 13 5408 5409 5410 5411 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5460 : S24 5460 = (fw_topk_routing (initSM 5457) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 14 5457 5458 5459 5460 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5509 : S24 5509 = (fw_topk_routing (initSM 5506) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 15 5506 5507 5508 5509 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5558 : S24 5558 = (fw_topk_routing (initSM 5555) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 16 5555 5556 5557 5558 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5607 : S24 5607 = (fw_topk_routing (initSM 5604) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 17 5604 5605 5606 5607 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5656 : S24 5656 = (fw_topk_routing (initSM 5653) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 18 5653 5654 5655 5656 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5705 : S24 5705 = (fw_topk_routing (initSM 5702) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 19 5702 5703 5704 5705 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5754 : S24 5754 = (fw_topk_routing (initSM 5751) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 20 5751 5752 5753 5754 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5803 : S24 5803 = (fw_topk_routing (initSM 5800) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 21 5800 5801 5802 5803 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5852 : S24 5852 = (fw_topk_routing (initSM 5849) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 22 5849 5850 5851 5852 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  have h5901 : S24 5901 = (fw_topk_routing (initSM 5898) 8 1).snd.snd :=
    denote_sm_S24_at_scores initSM 23 5898 5899 5900 5901 (by omega)
      (by rfl)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by intro n hn; fin_cases hn <;> decide)
      (by decide) (by decide)
  rw [h4711, h4765, h4819, h4873, h4927, h4981, h5035, h5089, h5143, h5197, h5251, h5305, h5362, h5411, h5460, h5509, h5558, h5607, h5656, h5705, h5754, h5803, h5852, h5901]

theorem prove_goal_4 : goal_4_stmt_cut := by
  sorry -- Math: apply per-layer topk sharding lemma × 24, then stack-lift.
        -- Row-wise argument on softmax + topk_routing. Est. 1 week.

theorem prove_pattern_4 : pattern_4_stmt := by
  intro target h
  cases h
  exact prove_goal_4

end TrainVerify.Denote.GeneratedPatterns
