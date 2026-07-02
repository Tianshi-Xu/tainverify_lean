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

/-!
### PM-side machinery: denote pm_goal_4 at write tid 4676.

pm_goal_4.nodes has 55 nodes:
  - Positions 0..51: 4 ChunkPrim (pm[0,1,4,5]) + 48 FW_topk_routing (rest)
  - Position 52: FW_stack (rank 0) → 11781
  - Position 53: FW_stack (rank 1) → 11782
  - Position 54: AllGatherPrim → 4676

The 24 SM scores per rank come from stacking the .snd.snd of each layer's topk.
Layers 0/1 (positions 0..7) chunk initPM 4708/4762 then topk; layers 2..23
(positions 8..51) directly topk on upstream tids 7851, 7852, 8037, 8038, ...
which are boundary (from goal_4_prereqs' intermediateGoals).
-/

/-- Helper: for pm_goal_4, S_pm52 at scoresTid of a topk node at position k
    (0..51) equals topk_scores of `logitsVal`, given `logitsVal` matches
    what S_k computes at logitsTid. -/
private theorem denote_pm_S52_at_scores
    (initPM : Store) (k : Nat) (rank_i : Nat)
    (logitsTid probsTid mapTid scoresTid : Tid) (logitsVal : Tensor)
    (hk : k + 1 ≤ 52)
    (h_prefix_eq : pm_goal_4.nodes.take (k+1) =
      (pm_goal_4.nodes.take k) ++
      [{ rank := rank_i, op := "OpName.FW_topk_routing", ins := [logitsTid],
         outs := [probsTid, mapTid, scoresTid], params := [8] }])
    (h_logits_val : ((pm_goal_4.nodes.take k).foldl (applyNode pm_goal_4) initPM) logitsTid
                    = logitsVal)
    (h_suffix_no_write :
      ∀ n ∈ (pm_goal_4.nodes.drop (k+1)).take (52 - (k+1)), scoresTid ∉ n.outs)
    (h_pne : probsTid ≠ scoresTid) (h_mne : mapTid ≠ scoresTid) :
    ((pm_goal_4.nodes.take 52).foldl (applyNode pm_goal_4) initPM) scoresTid =
    (fw_topk_routing logitsVal 8 1).snd.snd := by
  have h_split : pm_goal_4.nodes.take 52 =
      pm_goal_4.nodes.take (k+1) ++ (pm_goal_4.nodes.drop (k+1)).take (52 - (k+1)) := by
    have heq : k + 1 + (52 - (k+1)) = 52 := by omega
    calc pm_goal_4.nodes.take 52
        = pm_goal_4.nodes.take (k+1 + (52 - (k+1))) := by rw [heq]
      _ = pm_goal_4.nodes.take (k+1) ++ (pm_goal_4.nodes.drop (k+1)).take (52 - (k+1)) := by
          rw [List.take_add]
  rw [h_split, List.foldl_append]
  rw [foldl_applyNode_at_not_written pm_goal_4 _ _ scoresTid h_suffix_no_write]
  rw [h_prefix_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set S_k : Store := (pm_goal_4.nodes.take k).foldl (applyNode pm_goal_4) initPM
  have h_apply := applyNode_fw_topk_routing_scores_out pm_goal_4 S_k rank_i
    logitsTid probsTid mapTid scoresTid [8] h_pne h_mne
  rw [h_apply, h_logits_val]
  rfl

/-- Helper: prefix chunk yields chunked initPM. Similar pattern for
    ChunkPrim at positions 0,1,4,5. -/
private theorem denote_pm_S52_at_chunk
    (initPM : Store) (k : Nat) (rank_i : Nat)
    (inTid outTid : Tid) (inVal : Tensor)
    (hk : k + 1 ≤ 52)
    (h_prefix_eq : pm_goal_4.nodes.take (k+1) =
      (pm_goal_4.nodes.take k) ++
      [{ rank := rank_i, op := "OpName.ChunkPrim", ins := [inTid],
         outs := [outTid], params := [0] }])
    (h_in_val : ((pm_goal_4.nodes.take k).foldl (applyNode pm_goal_4) initPM) inTid
                = inVal)
    (h_suffix_no_write :
      ∀ n ∈ (pm_goal_4.nodes.drop (k+1)).take (52 - (k+1)), outTid ∉ n.outs) :
    ((pm_goal_4.nodes.take 52).foldl (applyNode pm_goal_4) initPM) outTid =
    chunkPrimDimN 0 pm_goal_4.numRanks rank_i inVal := by
  have h_split : pm_goal_4.nodes.take 52 =
      pm_goal_4.nodes.take (k+1) ++ (pm_goal_4.nodes.drop (k+1)).take (52 - (k+1)) := by
    have heq : k + 1 + (52 - (k+1)) = 52 := by omega
    calc pm_goal_4.nodes.take 52
        = pm_goal_4.nodes.take (k+1 + (52 - (k+1))) := by rw [heq]
      _ = pm_goal_4.nodes.take (k+1) ++ (pm_goal_4.nodes.drop (k+1)).take (52 - (k+1)) := by
          rw [List.take_add]
  rw [h_split, List.foldl_append]
  rw [foldl_applyNode_at_not_written pm_goal_4 _ _ outTid h_suffix_no_write]
  rw [h_prefix_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set S_k : Store := (pm_goal_4.nodes.take k).foldl (applyNode pm_goal_4) initPM
  rw [applyNode_chunkPrimDimN_out pm_goal_4 S_k rank_i inTid outTid 0]
  rw [h_in_val]

/-- Helper: mini-reduction for pm[2..7] where the topk's logitsTid was
    written by an earlier chunk in the same layer. -/
private theorem pm_prefix_at_chunked
    (initPM : Store) (k k_chunk : Nat) (rank_i : Nat)
    (srcTid logitsTid : Tid)
    (h_take_k : pm_goal_4.nodes.take k =
      (pm_goal_4.nodes.take k_chunk) ++
      [{ rank := rank_i, op := "OpName.ChunkPrim", ins := [srcTid],
         outs := [logitsTid], params := [0] }] ++
      (pm_goal_4.nodes.drop (k_chunk + 1)).take (k - (k_chunk + 1)))
    (h_prefix_no_write_src :
      ∀ n ∈ pm_goal_4.nodes.take k_chunk, srcTid ∉ n.outs)
    (h_between_no_write :
      ∀ n ∈ (pm_goal_4.nodes.drop (k_chunk + 1)).take (k - (k_chunk + 1)),
        logitsTid ∉ n.outs) :
    ((pm_goal_4.nodes.take k).foldl (applyNode pm_goal_4) initPM) logitsTid =
    chunkPrimDimN 0 pm_goal_4.numRanks rank_i (initPM srcTid) := by
  rw [h_take_k, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_applyNode_at_not_written pm_goal_4 _ _ logitsTid h_between_no_write]
  set S_chunk : Store := (pm_goal_4.nodes.take k_chunk).foldl (applyNode pm_goal_4) initPM
  rw [applyNode_chunkPrimDimN_out pm_goal_4 S_chunk rank_i srcTid logitsTid 0]
  have h_src_eq : S_chunk srcTid = initPM srcTid :=
    foldl_applyNode_at_not_written pm_goal_4 _ initPM srcTid h_prefix_no_write_src
  rw [h_src_eq]

/-- Main PM machinery: denote pm_goal_4 at 4676 = allGather of 2 fw_stacks. -/
theorem denote_pm_goal_4_4676 (initPM : Store) :
    denoteGraph pm_goal_4 initPM 4676 =
    allGatherPrimDimN 1 pm_goal_4.numRanks 0
      [fw_stack
        [(fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4708)) 8 1).snd.snd,
         (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4762)) 8 1).snd.snd,
         (fw_topk_routing (initPM 7851) 8 1).snd.snd,
         (fw_topk_routing (initPM 8037) 8 1).snd.snd,
         (fw_topk_routing (initPM 8223) 8 1).snd.snd,
         (fw_topk_routing (initPM 8409) 8 1).snd.snd,
         (fw_topk_routing (initPM 8595) 8 1).snd.snd,
         (fw_topk_routing (initPM 8781) 8 1).snd.snd,
         (fw_topk_routing (initPM 8967) 8 1).snd.snd,
         (fw_topk_routing (initPM 9153) 8 1).snd.snd,
         (fw_topk_routing (initPM 9339) 8 1).snd.snd,
         (fw_topk_routing (initPM 9525) 8 1).snd.snd,
         (fw_topk_routing (initPM 9729) 8 1).snd.snd,
         (fw_topk_routing (initPM 9901) 8 1).snd.snd,
         (fw_topk_routing (initPM 10073) 8 1).snd.snd,
         (fw_topk_routing (initPM 10245) 8 1).snd.snd,
         (fw_topk_routing (initPM 10417) 8 1).snd.snd,
         (fw_topk_routing (initPM 10589) 8 1).snd.snd,
         (fw_topk_routing (initPM 10761) 8 1).snd.snd,
         (fw_topk_routing (initPM 10933) 8 1).snd.snd,
         (fw_topk_routing (initPM 11105) 8 1).snd.snd,
         (fw_topk_routing (initPM 11277) 8 1).snd.snd,
         (fw_topk_routing (initPM 11449) 8 1).snd.snd,
         (fw_topk_routing (initPM 11621) 8 1).snd.snd],
       fw_stack
        [(fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 1 (initPM 4708)) 8 1).snd.snd,
         (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 1 (initPM 4762)) 8 1).snd.snd,
         (fw_topk_routing (initPM 7852) 8 1).snd.snd,
         (fw_topk_routing (initPM 8038) 8 1).snd.snd,
         (fw_topk_routing (initPM 8224) 8 1).snd.snd,
         (fw_topk_routing (initPM 8410) 8 1).snd.snd,
         (fw_topk_routing (initPM 8596) 8 1).snd.snd,
         (fw_topk_routing (initPM 8782) 8 1).snd.snd,
         (fw_topk_routing (initPM 8968) 8 1).snd.snd,
         (fw_topk_routing (initPM 9154) 8 1).snd.snd,
         (fw_topk_routing (initPM 9340) 8 1).snd.snd,
         (fw_topk_routing (initPM 9526) 8 1).snd.snd,
         (fw_topk_routing (initPM 9730) 8 1).snd.snd,
         (fw_topk_routing (initPM 9902) 8 1).snd.snd,
         (fw_topk_routing (initPM 10074) 8 1).snd.snd,
         (fw_topk_routing (initPM 10246) 8 1).snd.snd,
         (fw_topk_routing (initPM 10418) 8 1).snd.snd,
         (fw_topk_routing (initPM 10590) 8 1).snd.snd,
         (fw_topk_routing (initPM 10762) 8 1).snd.snd,
         (fw_topk_routing (initPM 10934) 8 1).snd.snd,
         (fw_topk_routing (initPM 11106) 8 1).snd.snd,
         (fw_topk_routing (initPM 11278) 8 1).snd.snd,
         (fw_topk_routing (initPM 11450) 8 1).snd.snd,
         (fw_topk_routing (initPM 11622) 8 1).snd.snd]] := by
  have h_split_full : pm_goal_4.nodes = pm_goal_4.nodes.take 52 ++
      [{ rank := 0, op := "OpName.FW_stack",
         ins := [7485, 7671, 7857, 8043, 8229, 8415, 8601, 8787, 8973, 9159,
                 9345, 9531, 9735, 9907, 10079, 10251, 10423, 10595, 10767,
                 10939, 11111, 11283, 11455, 11627],
         outs := [11781], params := [] },
       { rank := 1, op := "OpName.FW_stack",
         ins := [7486, 7672, 7858, 8044, 8230, 8416, 8602, 8788, 8974, 9160,
                 9346, 9532, 9736, 9908, 10080, 10252, 10424, 10596, 10768,
                 10940, 11112, 11284, 11456, 11628],
         outs := [11782], params := [] },
       { rank := 0, op := "OpName.AllGatherPrim",
         ins := [11781, 11782], outs := [4676], params := [1] }] := by
    show pm_goal_4.nodes = _
    rfl
  unfold denoteGraph
  rw [h_split_full, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_cons, List.foldl_nil]
  set S52 : Store := (pm_goal_4.nodes.take 52).foldl (applyNode pm_goal_4) initPM
  set S53 : Store := applyNode pm_goal_4 S52
    { rank := 0, op := "OpName.FW_stack",
      ins := [7485, 7671, 7857, 8043, 8229, 8415, 8601, 8787, 8973, 9159,
              9345, 9531, 9735, 9907, 10079, 10251, 10423, 10595, 10767,
              10939, 11111, 11283, 11455, 11627],
      outs := [11781], params := [] }
  set S54 : Store := applyNode pm_goal_4 S53
    { rank := 1, op := "OpName.FW_stack",
      ins := [7486, 7672, 7858, 8044, 8230, 8416, 8602, 8788, 8974, 9160,
              9346, 9532, 9736, 9908, 10080, 10252, 10424, 10596, 10768,
              10940, 11112, 11284, 11456, 11628],
      outs := [11782], params := [] }
  rw [applyNode_allGatherPrimDimN_out pm_goal_4 S54 0 [11781, 11782] 4676 1]
  have h_S54_11781 : S54 11781 = S53 11781 := by
    show applyNode pm_goal_4 S53 _ 11781 = S53 11781
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S53 _ 11781 (by decide)
  have h_S54_11782 : S54 11782 = fw_stack ([7486, 7672, 7858, 8044, 8230, 8416, 8602, 8788, 8974, 9160, 9346, 9532, 9736, 9908, 10080, 10252, 10424, 10596, 10768, 10940, 11112, 11284, 11456, 11628].map S53) := by
    show applyNode pm_goal_4 S53 _ 11782 = _
    exact applyNode_fw_stack_out pm_goal_4 S53 1 _ 11782 []
  have h_S53_11781 : S53 11781 = fw_stack ([7485, 7671, 7857, 8043, 8229, 8415, 8601, 8787, 8973, 9159, 9345, 9531, 9735, 9907, 10079, 10251, 10423, 10595, 10767, 10939, 11111, 11283, 11455, 11627].map S52) := by
    show applyNode pm_goal_4 S52 _ 11781 = _
    exact applyNode_fw_stack_out pm_goal_4 S52 0 _ 11781 []
  have h_out_7479 : S52 7479 = chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4708) :=
    denote_pm_S52_at_chunk initPM 0 0 4708 7479 _ (by omega)
      (by rfl)
      (by rfl)
      (by native_decide)
  have h_out_7480 : S52 7480 = chunkPrimDimN 0 pm_goal_4.numRanks 1 (initPM 4708) :=
    denote_pm_S52_at_chunk initPM 1 1 4708 7480 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 4708 (by native_decide))
      (by native_decide)
  have h_out_7665 : S52 7665 = chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4762) :=
    denote_pm_S52_at_chunk initPM 4 0 4762 7665 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 4762 (by native_decide))
      (by native_decide)
  have h_out_7666 : S52 7666 = chunkPrimDimN 0 pm_goal_4.numRanks 1 (initPM 4762) :=
    denote_pm_S52_at_chunk initPM 5 1 4762 7666 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 4762 (by native_decide))
      (by native_decide)
  have h_scores_7485 : S52 7485 = (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4708)) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 2 0 7479 7481 7483 7485 _ (by omega)
      (by rfl)
      (pm_prefix_at_chunked initPM 2 0 0 4708 7479
        (by rfl)
        (by native_decide)
        (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_7486 : S52 7486 = (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 1 (initPM 4708)) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 3 1 7480 7482 7484 7486 _ (by omega)
      (by rfl)
      (pm_prefix_at_chunked initPM 3 1 1 4708 7480
        (by rfl)
        (by native_decide)
        (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_7671 : S52 7671 = (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4762)) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 6 0 7665 7667 7669 7671 _ (by omega)
      (by rfl)
      (pm_prefix_at_chunked initPM 6 4 0 4762 7665
        (by rfl)
        (by native_decide)
        (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_7672 : S52 7672 = (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 1 (initPM 4762)) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 7 1 7666 7668 7670 7672 _ (by omega)
      (by rfl)
      (pm_prefix_at_chunked initPM 7 5 1 4762 7666
        (by rfl)
        (by native_decide)
        (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_7857 : S52 7857 = (fw_topk_routing (initPM 7851) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 8 0 7851 7853 7855 7857 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 7851 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_7858 : S52 7858 = (fw_topk_routing (initPM 7852) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 9 1 7852 7854 7856 7858 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 7852 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8043 : S52 8043 = (fw_topk_routing (initPM 8037) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 10 0 8037 8039 8041 8043 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8037 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8044 : S52 8044 = (fw_topk_routing (initPM 8038) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 11 1 8038 8040 8042 8044 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8038 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8229 : S52 8229 = (fw_topk_routing (initPM 8223) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 12 0 8223 8225 8227 8229 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8223 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8230 : S52 8230 = (fw_topk_routing (initPM 8224) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 13 1 8224 8226 8228 8230 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8224 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8415 : S52 8415 = (fw_topk_routing (initPM 8409) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 14 0 8409 8411 8413 8415 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8409 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8416 : S52 8416 = (fw_topk_routing (initPM 8410) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 15 1 8410 8412 8414 8416 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8410 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8601 : S52 8601 = (fw_topk_routing (initPM 8595) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 16 0 8595 8597 8599 8601 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8595 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8602 : S52 8602 = (fw_topk_routing (initPM 8596) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 17 1 8596 8598 8600 8602 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8596 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8787 : S52 8787 = (fw_topk_routing (initPM 8781) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 18 0 8781 8783 8785 8787 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8781 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8788 : S52 8788 = (fw_topk_routing (initPM 8782) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 19 1 8782 8784 8786 8788 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8782 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8973 : S52 8973 = (fw_topk_routing (initPM 8967) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 20 0 8967 8969 8971 8973 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8967 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_8974 : S52 8974 = (fw_topk_routing (initPM 8968) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 21 1 8968 8970 8972 8974 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 8968 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9159 : S52 9159 = (fw_topk_routing (initPM 9153) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 22 0 9153 9155 9157 9159 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9153 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9160 : S52 9160 = (fw_topk_routing (initPM 9154) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 23 1 9154 9156 9158 9160 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9154 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9345 : S52 9345 = (fw_topk_routing (initPM 9339) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 24 0 9339 9341 9343 9345 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9339 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9346 : S52 9346 = (fw_topk_routing (initPM 9340) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 25 1 9340 9342 9344 9346 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9340 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9531 : S52 9531 = (fw_topk_routing (initPM 9525) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 26 0 9525 9527 9529 9531 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9525 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9532 : S52 9532 = (fw_topk_routing (initPM 9526) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 27 1 9526 9528 9530 9532 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9526 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9735 : S52 9735 = (fw_topk_routing (initPM 9729) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 28 0 9729 9731 9733 9735 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9729 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9736 : S52 9736 = (fw_topk_routing (initPM 9730) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 29 1 9730 9732 9734 9736 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9730 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9907 : S52 9907 = (fw_topk_routing (initPM 9901) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 30 0 9901 9903 9905 9907 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9901 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_9908 : S52 9908 = (fw_topk_routing (initPM 9902) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 31 1 9902 9904 9906 9908 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 9902 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10079 : S52 10079 = (fw_topk_routing (initPM 10073) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 32 0 10073 10075 10077 10079 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10073 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10080 : S52 10080 = (fw_topk_routing (initPM 10074) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 33 1 10074 10076 10078 10080 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10074 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10251 : S52 10251 = (fw_topk_routing (initPM 10245) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 34 0 10245 10247 10249 10251 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10245 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10252 : S52 10252 = (fw_topk_routing (initPM 10246) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 35 1 10246 10248 10250 10252 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10246 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10423 : S52 10423 = (fw_topk_routing (initPM 10417) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 36 0 10417 10419 10421 10423 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10417 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10424 : S52 10424 = (fw_topk_routing (initPM 10418) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 37 1 10418 10420 10422 10424 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10418 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10595 : S52 10595 = (fw_topk_routing (initPM 10589) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 38 0 10589 10591 10593 10595 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10589 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10596 : S52 10596 = (fw_topk_routing (initPM 10590) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 39 1 10590 10592 10594 10596 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10590 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10767 : S52 10767 = (fw_topk_routing (initPM 10761) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 40 0 10761 10763 10765 10767 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10761 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10768 : S52 10768 = (fw_topk_routing (initPM 10762) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 41 1 10762 10764 10766 10768 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10762 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10939 : S52 10939 = (fw_topk_routing (initPM 10933) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 42 0 10933 10935 10937 10939 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10933 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_10940 : S52 10940 = (fw_topk_routing (initPM 10934) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 43 1 10934 10936 10938 10940 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 10934 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11111 : S52 11111 = (fw_topk_routing (initPM 11105) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 44 0 11105 11107 11109 11111 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11105 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11112 : S52 11112 = (fw_topk_routing (initPM 11106) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 45 1 11106 11108 11110 11112 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11106 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11283 : S52 11283 = (fw_topk_routing (initPM 11277) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 46 0 11277 11279 11281 11283 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11277 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11284 : S52 11284 = (fw_topk_routing (initPM 11278) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 47 1 11278 11280 11282 11284 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11278 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11455 : S52 11455 = (fw_topk_routing (initPM 11449) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 48 0 11449 11451 11453 11455 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11449 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11456 : S52 11456 = (fw_topk_routing (initPM 11450) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 49 1 11450 11452 11454 11456 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11450 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11627 : S52 11627 = (fw_topk_routing (initPM 11621) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 50 0 11621 11623 11625 11627 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11621 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_scores_11628 : S52 11628 = (fw_topk_routing (initPM 11622) 8 1).snd.snd :=
    denote_pm_S52_at_scores initPM 51 1 11622 11624 11626 11628 _ (by omega)
      (by rfl)
      (by exact foldl_applyNode_at_not_written pm_goal_4 _ initPM 11622 (by native_decide))
      (by native_decide)
      (by decide) (by decide)
  have h_S53_7486 : S53 7486 = S52 7486 := by
    show applyNode pm_goal_4 S52 _ 7486 = S52 7486
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 7486 (by decide)
  have h_S53_7672 : S53 7672 = S52 7672 := by
    show applyNode pm_goal_4 S52 _ 7672 = S52 7672
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 7672 (by decide)
  have h_S53_7858 : S53 7858 = S52 7858 := by
    show applyNode pm_goal_4 S52 _ 7858 = S52 7858
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 7858 (by decide)
  have h_S53_8044 : S53 8044 = S52 8044 := by
    show applyNode pm_goal_4 S52 _ 8044 = S52 8044
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 8044 (by decide)
  have h_S53_8230 : S53 8230 = S52 8230 := by
    show applyNode pm_goal_4 S52 _ 8230 = S52 8230
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 8230 (by decide)
  have h_S53_8416 : S53 8416 = S52 8416 := by
    show applyNode pm_goal_4 S52 _ 8416 = S52 8416
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 8416 (by decide)
  have h_S53_8602 : S53 8602 = S52 8602 := by
    show applyNode pm_goal_4 S52 _ 8602 = S52 8602
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 8602 (by decide)
  have h_S53_8788 : S53 8788 = S52 8788 := by
    show applyNode pm_goal_4 S52 _ 8788 = S52 8788
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 8788 (by decide)
  have h_S53_8974 : S53 8974 = S52 8974 := by
    show applyNode pm_goal_4 S52 _ 8974 = S52 8974
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 8974 (by decide)
  have h_S53_9160 : S53 9160 = S52 9160 := by
    show applyNode pm_goal_4 S52 _ 9160 = S52 9160
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 9160 (by decide)
  have h_S53_9346 : S53 9346 = S52 9346 := by
    show applyNode pm_goal_4 S52 _ 9346 = S52 9346
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 9346 (by decide)
  have h_S53_9532 : S53 9532 = S52 9532 := by
    show applyNode pm_goal_4 S52 _ 9532 = S52 9532
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 9532 (by decide)
  have h_S53_9736 : S53 9736 = S52 9736 := by
    show applyNode pm_goal_4 S52 _ 9736 = S52 9736
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 9736 (by decide)
  have h_S53_9908 : S53 9908 = S52 9908 := by
    show applyNode pm_goal_4 S52 _ 9908 = S52 9908
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 9908 (by decide)
  have h_S53_10080 : S53 10080 = S52 10080 := by
    show applyNode pm_goal_4 S52 _ 10080 = S52 10080
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 10080 (by decide)
  have h_S53_10252 : S53 10252 = S52 10252 := by
    show applyNode pm_goal_4 S52 _ 10252 = S52 10252
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 10252 (by decide)
  have h_S53_10424 : S53 10424 = S52 10424 := by
    show applyNode pm_goal_4 S52 _ 10424 = S52 10424
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 10424 (by decide)
  have h_S53_10596 : S53 10596 = S52 10596 := by
    show applyNode pm_goal_4 S52 _ 10596 = S52 10596
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 10596 (by decide)
  have h_S53_10768 : S53 10768 = S52 10768 := by
    show applyNode pm_goal_4 S52 _ 10768 = S52 10768
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 10768 (by decide)
  have h_S53_10940 : S53 10940 = S52 10940 := by
    show applyNode pm_goal_4 S52 _ 10940 = S52 10940
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 10940 (by decide)
  have h_S53_11112 : S53 11112 = S52 11112 := by
    show applyNode pm_goal_4 S52 _ 11112 = S52 11112
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 11112 (by decide)
  have h_S53_11284 : S53 11284 = S52 11284 := by
    show applyNode pm_goal_4 S52 _ 11284 = S52 11284
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 11284 (by decide)
  have h_S53_11456 : S53 11456 = S52 11456 := by
    show applyNode pm_goal_4 S52 _ 11456 = S52 11456
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 11456 (by decide)
  have h_S53_11628 : S53 11628 = S52 11628 := by
    show applyNode pm_goal_4 S52 _ 11628 = S52 11628
    exact applyNode_eq_of_not_mem_outs pm_goal_4 S52 _ 11628 (by decide)
  -- Expand ins.map at each level (S54, S53, S52) via repeated simp+rw
  simp only [List.map]
  rw [h_S54_11781, h_S54_11782]
  simp only [List.map]
  rw [h_S53_11781]
  simp only [List.map]
  rw [h_S53_7486, h_S53_7672, h_S53_7858, h_S53_8044, h_S53_8230, h_S53_8416, h_S53_8602, h_S53_8788, h_S53_8974, h_S53_9160, h_S53_9346, h_S53_9532, h_S53_9736, h_S53_9908, h_S53_10080, h_S53_10252, h_S53_10424, h_S53_10596, h_S53_10768, h_S53_10940, h_S53_11112, h_S53_11284, h_S53_11456, h_S53_11628, h_scores_7485, h_scores_7671, h_scores_7857, h_scores_8043, h_scores_8229, h_scores_8415, h_scores_8601, h_scores_8787, h_scores_8973, h_scores_9159, h_scores_9345, h_scores_9531, h_scores_9735, h_scores_9907, h_scores_10079, h_scores_10251, h_scores_10423, h_scores_10595, h_scores_10767, h_scores_10939, h_scores_11111, h_scores_11283, h_scores_11455, h_scores_11627, h_scores_7486, h_scores_7672, h_scores_7858, h_scores_8044, h_scores_8230, h_scores_8416, h_scores_8602, h_scores_8788, h_scores_8974, h_scores_9160, h_scores_9346, h_scores_9532, h_scores_9736, h_scores_9908, h_scores_10080, h_scores_10252, h_scores_10424, h_scores_10596, h_scores_10768, h_scores_10940, h_scores_11112, h_scores_11284, h_scores_11456, h_scores_11628]


theorem prove_pattern_4 : pattern_4_stmt := by
  intro target h
  cases h
  exact prove_goal_4

end TrainVerify.Denote.GeneratedPatterns
