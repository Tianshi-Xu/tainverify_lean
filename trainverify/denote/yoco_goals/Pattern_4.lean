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


/-! ## Pattern_4 pure-math lemmas -/

/-- Softmax valAt for last-dim `64`, index expressed as `row * 64 + col`. -/
theorem softmax_valAt_d64 (x : Tensor) (pre : List Nat) (idx : Nat)
    (hrev : x.shape.reverse = 64 :: pre) (hidx : idx < prodShape x.shape) :
    valAt (softmax x) idx =
      (if (∑ j ∈ Finset.range 64, expFn (valAt x (idx / 64 * 64 + j))) = 0 then 0
       else expFn (valAt x (idx / 64 * 64 + idx % 64))
            / ∑ j ∈ Finset.range 64, expFn (valAt x (idx / 64 * 64 + j))) := by
  have heq : softmax x = Tensor.mkShape x.shape (fun outIdx =>
      if (∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j))) = 0 then 0
      else expFn (valAt x (outIdx.1 / 64 * 64 + outIdx.1 % 64))
           / ∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j))) := by
    unfold softmax; rw [hrev]; rfl
  rw [heq]
  rw [valAt_of_lt _ _ (show idx < prodShape
      (Tensor.mkShape x.shape (fun outIdx =>
        if (∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j))) = 0 then 0
        else expFn (valAt x (outIdx.1 / 64 * 64 + outIdx.1 % 64))
             / ∑ j ∈ Finset.range 64, expFn (valAt x (outIdx.1 / 64 * 64 + j)))).shape from hidx)]
  rfl

/-- **Lemma A**: softmax distributes over dim-0 all-gather for shard shape `[2048, 64]`. -/
theorem softmax_allGather2_dim0_2048_64 (a b : Tensor)
    (ha : a.shape = [2048, 64]) (hb : b.shape = [2048, 64]) :
    softmax (allGatherPrimDimN 0 2 0 [a, b]) =
      allGatherPrimDimN 0 2 0 [softmax a, softmax b] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
    simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]; simp [List.set, List.getD]
  have hsm_shape : ∀ c : Tensor, c.shape = [2048, 64] → (softmax c).shape = [2048, 64] := by
    intro c hc; unfold softmax; rw [hc]; rfl
  have hhead_sm : (([softmax a, softmax b] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [2048, 64] := by
    simp [hsm_shape a ha]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [softmax a, softmax b]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead_sm]; simp [List.set, List.getD]
  apply Tensor.ext
  · have h1 : (softmax (allGatherPrimDimN 0 2 0 [a, b])).shape = [4096, 64] := by
      unfold softmax; rw [hG_shape]; rfl
    rw [h1, hRHS_shape]
  · intro idx hidx
    have hidx_bound : idx < 262144 := by
      have h1 : (softmax (allGatherPrimDimN 0 2 0 [a, b])).shape = [4096, 64] := by
        unfold softmax; rw [hG_shape]; rfl
      rw [h1] at hidx
      simpa [prodShape] using hidx
    have hGrev : (allGatherPrimDimN 0 2 0 [a, b]).shape.reverse = 64 :: [4096] := by
      rw [hG_shape]; rfl
    have hGprod : idx < prodShape (allGatherPrimDimN 0 2 0 [a, b]).shape := by
      rw [hG_shape]; simpa [prodShape] using hidx_bound
    rw [softmax_valAt_d64 _ [4096] idx hGrev hGprod]
    set row := idx / 64 with hrow_def
    set col := idx % 64 with hcol_def
    have hrow_lt : row < 4096 := by rw [hrow_def]; omega
    have hcol_lt : col < 64 := by rw [hcol_def]; omega
    set r := row / 2048 with hr_def
    set i := row % 2048 with hi_def
    have hr_lt : r < 2 := by rw [hr_def]; omega
    have hi_lt : i < 2048 := by rw [hi_def]; omega
    have hidx_eq : idx = (r * 2048 + i) * 64 + col := by
      rw [hr_def, hi_def, hcol_def, hrow_def]; omega
    rw [hidx_eq]
    have hRHS_val_gather :
        valAt (allGatherPrimDimN 0 2 0 [softmax a, softmax b]) ((r * 2048 + i) * 64 + col) =
        valAt (([softmax a, softmax b].getD r (zeroTensor [2048, 64]))) (i * 64 + col) := by
      apply allGatherPrimDimN0_valAt 2 2048 64 [softmax a, softmax b]
        (by omega) (by omega) (by omega) hhead_sm
      · intro r' hr'
        rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, hsm_shape a ha, hsm_shape b hb]
      · exact hr_lt
      · exact hi_lt
      · exact hcol_lt
    rw [hRHS_val_gather]
    have hgetD_sm : [softmax a, softmax b].getD r (zeroTensor [2048, 64]) =
        softmax ([a, b].getD r (zeroTensor [2048, 64])) := by
      rcases (by omega : r = 0 ∨ r = 1) with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_sm]
    set cr := [a, b].getD r (zeroTensor [2048, 64]) with hcr_def
    have hcr_shape : cr.shape = [2048, 64] := by
      rw [hcr_def]
      rcases (by omega : r = 0 ∨ r = 1) with h | h <;> rw [h] <;>
        simp [List.getD, ha, hb]
    have hcr_rev : cr.shape.reverse = 64 :: [2048] := by rw [hcr_shape]; rfl
    have hloc_lt : i * 64 + col < prodShape cr.shape := by
      rw [hcr_shape]; simp only [prodShape, List.foldl]; omega
    rw [softmax_valAt_d64 cr [2048] (i * 64 + col) hcr_rev hloc_lt]
    rw [show row = (r * 2048 + i) from by rw [hr_def, hi_def]; omega]
    have hloc_div : (i * 64 + col) / 64 = i := by omega
    have hloc_mod : (i * 64 + col) % 64 = col := by omega
    rw [hloc_div, hloc_mod]
    have hsum : (∑ j ∈ Finset.range 64,
          expFn (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * 2048 + i) * 64 + j)))
        = (∑ j ∈ Finset.range 64, expFn (valAt cr (i * 64 + j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [allGatherPrimDimN0_valAt 2 2048 64 [a, b] (by omega) (by omega) (by omega) hhead ?_ r hr_lt i hi_lt j hj]
      · intro r' hr'
        rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, ha, hb]
    have hnum :
        expFn (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * 2048 + i) * 64 + col))
      = expFn (valAt cr (i * 64 + col)) := by
      rw [allGatherPrimDimN0_valAt 2 2048 64 [a, b] (by omega) (by omega) (by omega) hhead ?_ r hr_lt i hi_lt col hcol_lt]
      · intro r' hr'
        rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, ha, hb]
    rw [hsum, hnum]

/-- **Lemma B (generic)**: stack-gather commute for shard shape `[2048, 64]`. -/
theorem stack_allGather_commute_generic_2048_64
    (as bs : List Tensor) (hlen : as.length = bs.length) (hne : as ≠ [])
    (hAs : ∀ a ∈ as, a.shape = [2048, 64]) (hBs : ∀ b ∈ bs, b.shape = [2048, 64]) :
    fw_stack (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs)
      = allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs] := by
  -- Setup: shapes.
  have hbs_ne : bs ≠ [] := by
    intro h; apply hne
    have : bs.length = 0 := by rw [h]; rfl
    exact List.length_eq_zero_iff.mp (hlen.trans this)
  have h_as_pos : 0 < as.length := List.length_pos_of_ne_nil hne
  have h_bs_pos : 0 < bs.length := List.length_pos_of_ne_nil hbs_ne
  set N := as.length with hN_def
  have hbs_len : bs.length = N := hlen.symm
  -- Zipped list has length N.
  set zL := List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs with hzL_def
  have hzL_len : zL.length = N := by rw [hzL_def]; rw [List.length_zipWith, hbs_len]; omega
  -- Shard shapes.
  have hAgather : ∀ a b : Tensor, a.shape = [2048, 64] → b.shape = [2048, 64] →
      (allGatherPrimDimN 0 2 0 [a, b]).shape = [4096, 64] := by
    intro a b ha hb
    have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
      simp [ha]
    rw [allGatherPrimDimN_shape 0 2 [a, b] [2048, 64] hhead]
    simp [List.set, List.getD]
  -- Every element of zL has shape [4096, 64] — use getElem-based reasoning.
  -- Avoid dependent-type rewriting issues by working with List.getElem_zipWith directly.
  have hzL_elem_shape : ∀ (i : Nat) (hi_z : i < zL.length), (zL[i]'hi_z).shape = [4096, 64] := by
    intro i hi_z
    have hi_as : i < as.length := by rw [hzL_len] at hi_z; omega
    have hi_bs : i < bs.length := by rw [hbs_len]; omega
    have h_getElem_eq :
        (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs)[i]'
        (by rw [List.length_zipWith]; omega) =
        allGatherPrimDimN 0 2 0 [as[i]'hi_as, bs[i]'hi_bs] := by
      simp [List.getElem_zipWith]
    -- Reveal zL as zipWith via `show`, then apply eq.
    show ((List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs)[i]'hi_z).shape
        = [4096, 64]
    rw [h_getElem_eq]
    exact hAgather _ _ (hAs _ (List.getElem_mem hi_as)) (hBs _ (List.getElem_mem hi_bs))
  -- head shape of zL: unfold via case-analysis on as & bs (both non-empty).
  have hzL_head : (zL.head?.map (fun t => t.shape)).getD [] = [4096, 64] := by
    rw [hzL_def]
    cases as_lc : as with
    | nil => exact absurd as_lc hne
    | cons a₀ as' =>
      cases bs_lc : bs with
      | nil =>
        exfalso
        rw [bs_lc, hN_def, as_lc] at hlen
        simp at hlen
      | cons b₀ bs' =>
        simp only [List.zipWith, List.head?, Option.map_some, Option.getD_some]
        have ha₀ : a₀.shape = [2048, 64] := hAs a₀ (by rw [as_lc]; exact List.mem_cons_self ..)
        have hb₀ : b₀.shape = [2048, 64] := hBs b₀ (by rw [bs_lc]; exact List.mem_cons_self ..)
        exact hAgather a₀ b₀ ha₀ hb₀
  -- fw_stack zL has shape [N, 4096, 64].
  have hLHS_shape : (fw_stack zL).shape = N :: [4096, 64] := by
    rw [fw_stack_shape zL [4096, 64] hzL_head, hzL_len]
  -- as head shape.
  have has_head : (as.head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
    rcases has_lc : as with _ | ⟨h, t⟩
    · exact absurd has_lc hne
    · simp only [List.head?, Option.map_some, Option.getD_some]
      exact hAs h (by rw [has_lc]; exact List.mem_cons_self ..)
  have hbs_head : (bs.head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
    rcases hbs_lc : bs with _ | ⟨h, t⟩
    · exact absurd hbs_lc hbs_ne
    · simp only [List.head?, Option.map_some, Option.getD_some]
      exact hBs h (by rw [hbs_lc]; exact List.mem_cons_self ..)
  have hAs_stack_shape : (fw_stack as).shape = N :: [2048, 64] := by
    rw [fw_stack_shape as [2048, 64] has_head]
  have hBs_stack_shape : (fw_stack bs).shape = N :: [2048, 64] := by
    rw [fw_stack_shape bs [2048, 64] hbs_head, hbs_len]
  -- RHS shape.
  have hRHS_head : (([fw_stack as, fw_stack bs] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = N :: [2048, 64] := by
    simp [hAs_stack_shape]
  have hRHS_shape : (allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs]).shape
      = [N, 4096, 64] := by
    rw [allGatherPrimDimN_shape 1 2 _ (N :: [2048, 64]) hRHS_head]
    simp [List.set, List.getD]
  -- Now use Tensor.ext.
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    -- Both shapes are [N, 4096, 64]. idx < N * 4096 * 64 = N * 262144.
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < N * 262144 := by
      simp only [prodShape, List.foldl_cons, List.foldl_nil] at hidx
      omega
    -- Decompose idx = layer * 262144 + local (row * 64 + col), then row = r * 2048 + jL.
    set layer := idx / 262144 with hlayer_def
    set local' := idx % 262144 with hlocal_def
    have hlayer_lt : layer < N := by
      rw [hlayer_def]
      exact Nat.div_lt_of_lt_mul (by linarith [hidx_bound])
    have hlocal_lt : local' < 262144 := by rw [hlocal_def]; omega
    have hidx_eq : idx = layer * 262144 + local' := by
      rw [hlayer_def, hlocal_def]; omega
    set row := local' / 64 with hrow_def
    set col := local' % 64 with hcol_def
    have hrow_lt : row < 4096 := by rw [hrow_def]; omega
    have hcol_lt : col < 64 := by rw [hcol_def]; omega
    have hlocal_eq : local' = row * 64 + col := by rw [hrow_def, hcol_def]; omega
    set r := row / 2048 with hr_def
    set jL := row % 2048 with hjL_def
    have hr_lt : r < 2 := by rw [hr_def]; omega
    have hjL_lt : jL < 2048 := by rw [hjL_def]; omega
    have hrow_eq : row = r * 2048 + jL := by rw [hr_def, hjL_def]; omega
    -- LHS = valAt (fw_stack zL) idx = valAt (zL[layer]) local'.
    -- Unfold fw_stack.
    have hLHS_eq : valAt (fw_stack zL) idx =
        valAt (zL.getD layer (zeroTensor [4096, 64])) local' := by
      have hidx_prod : idx < prodShape (fw_stack zL).shape := by
        rw [hLHS_shape]
        simp only [prodShape, List.foldl_cons, List.foldl_nil]
        linarith [hidx_bound]
      rw [valAt_of_lt _ _ hidx_prod]
      unfold fw_stack
      simp only [Tensor.mkShape, hzL_head]
      -- shardSize = 262144.
      have hshardSize : prodShape [4096, 64] = 262144 := by decide
      -- Goal: fw_stack's mkShape val at idx = valAt (zL.getD (idx/shardSize)) (idx%shardSize).
      -- After unfold, the expression matches with shardSize computed.
      simp only [hshardSize]
      -- Now the r,localIdx match. Rewrite idx / 262144 = layer, idx % 262144 = local'.
      rw [show idx / 262144 = layer from rfl, show idx % 262144 = local' from rfl]
      rfl
    rw [hLHS_eq]
    -- Now LHS = valAt (zL[layer]) local' = valAt (allGather_0 [as[layer], bs[layer]]) local'.
    have hzL_getD_layer : zL.getD layer (zeroTensor [4096, 64]) =
        allGatherPrimDimN 0 2 0 [as.getD layer (zeroTensor [2048, 64]),
                                 bs.getD layer (zeroTensor [2048, 64])] := by
      rw [hzL_def]
      -- List.zipWith f as bs .getD layer default
      have h_layer_as : layer < as.length := hlayer_lt
      have h_layer_bs : layer < bs.length := by rw [hbs_len]; exact hlayer_lt
      have has_getD : as.getD layer (zeroTensor [2048, 64]) = as[layer]'h_layer_as := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_as]
      have hbs_getD : bs.getD layer (zeroTensor [2048, 64]) = bs[layer]'h_layer_bs := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_bs]
      rw [has_getD, hbs_getD]
      -- List.zipWith f as bs [layer] = f as[layer] bs[layer].
      have hzip_getD : (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs).getD
          layer (zeroTensor [4096, 64])
          = allGatherPrimDimN 0 2 0 [as[layer]'h_layer_as, bs[layer]'h_layer_bs] := by
        have hzip_len : (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs).length
            = as.length := by rw [List.length_zipWith]; omega
        have h_layer_zip : layer < (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b])
            as bs).length := by rw [hzip_len]; exact hlayer_lt
        simp [List.getD, List.getElem?_eq_getElem h_layer_zip,
              List.getElem_zipWith]
      exact hzip_getD
    rw [hzL_getD_layer]
    -- Now LHS = valAt (allGather_0 [as[layer], bs[layer]]) local'.
    set a_l := as.getD layer (zeroTensor [2048, 64]) with ha_l_def
    set b_l := bs.getD layer (zeroTensor [2048, 64]) with hb_l_def
    have ha_l_shape : a_l.shape = [2048, 64] := by
      rw [ha_l_def]
      have h_layer_as : layer < as.length := hlayer_lt
      have has_getD : as.getD layer (zeroTensor [2048, 64]) = as[layer]'h_layer_as := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_as]
      rw [has_getD]
      exact hAs (as[layer]'h_layer_as) (List.getElem_mem h_layer_as)
    have hb_l_shape : b_l.shape = [2048, 64] := by
      rw [hb_l_def]
      have h_layer_bs : layer < bs.length := by rw [hbs_len]; exact hlayer_lt
      have hbs_getD : bs.getD layer (zeroTensor [2048, 64]) = bs[layer]'h_layer_bs := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_bs]
      rw [hbs_getD]
      exact hBs (bs[layer]'h_layer_bs) (List.getElem_mem h_layer_bs)
    have hab_head : (([a_l, b_l] : List Tensor).head?.map (fun t => t.shape)).getD []
        = [2048, 64] := by simp [ha_l_shape]
    rw [hlocal_eq]
    have hLHS_val := allGatherPrimDimN0_valAt 2 2048 64 [a_l, b_l]
      (by omega) (by omega) (by omega) hab_head
      (by intro r' hr'; rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, ha_l_shape, hb_l_shape])
      r hr_lt jL hjL_lt col hcol_lt
    -- Need to convert local' = row * 64 + col with row = r * 2048 + jL to (r*2048+jL)*64+col.
    rw [hrow_eq]
    rw [hLHS_val]
    -- Now LHS = valAt ([a_l, b_l].getD r ...) (jL * 64 + col).
    -- RHS side: unfold allGatherPrimDimN by expanding via valAt_of_lt.
    have hidx_prod_rhs : idx < prodShape (allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs]).shape := by
      rw [hRHS_shape]
      simp only [prodShape, List.foldl_cons, List.foldl_nil]
      linarith [hidx_bound]
    rw [valAt_of_lt _ _ hidx_prod_rhs]
    unfold allGatherPrimDimN
    simp only [Tensor.mkShape, hRHS_head]
    -- Simplify shape lookups and postStride to concrete numbers.
    have h_getD_1 : ([N, 2048, 64] : List Nat).getD 1 0 = 2048 := by rfl
    have h_drop_2 : List.drop (1 + 1) ([N, 2048, 64] : List Nat) = [64] := by rfl
    have h_foldl_64 : List.foldl (fun x1 x2 => x1 * x2) 1 ([64] : List Nat) = 64 := by rfl
    simp only [h_getD_1, h_drop_2, h_foldl_64]
    -- Simplify if conditions.
    simp only [show (2048 : Nat) = 0 ↔ False by decide, show (64 : Nat) = 0 ↔ False by decide,
               show (2048 * 2 * 64 : Nat) = 0 ↔ False by decide,
               if_false, iff_false, ↓reduceIte]
    -- Compute: 2048 * 2 * 64 = 262144; 2048 * 64 = 131072.
    show valAt ([a_l, b_l].getD r (zeroTensor [2048, 64])) (jL * 64 + col) =
         valAt ([fw_stack as, fw_stack bs].getD (idx % 262144 / 64 / 2048)
                  (zeroTensor [N, 2048, 64]))
              (idx / 262144 * 131072 + idx % 262144 / 64 % 2048 * 64 + idx % 262144 % 64)
    -- Rewrite: idx % 262144 = local', local' / 64 = row, local' % 64 = col,
    -- idx / 262144 = layer, row / 2048 = r, row % 2048 = jL.
    rw [show idx % 262144 = local' from rfl,
        show idx / 262144 = layer from rfl,
        show local' / 64 = row from rfl,
        show local' % 64 = col from rfl,
        show row / 2048 = r from rfl,
        show row % 2048 = jL from rfl]
    -- Now: valAt (list.getD r) (jL*64+col) = valAt (list.getD r) (layer*131072 + jL*64 + col)
    -- where LHS list is [a_l, b_l], RHS list is [fw_stack as, fw_stack bs].
    -- Case-split on r ∈ {0, 1}. In each case:
    --   * LHS getD selects a_l (or b_l).
    --   * RHS getD selects fw_stack as (or fw_stack bs).
    --   * fw_stack.valAt(layer*131072 + jL*64 + col) reduces to (as[layer] or bs[layer]).valAt(jL*64+col).
    -- Helper: fw_stack xs .valAt (layer * 131072 + local) = xs[layer].valAt(local) for shard [2048,64].
    have hfs_valAt : ∀ (xs : List Tensor) (h_head : (xs.head?.map (fun t => t.shape)).getD [] = [2048, 64])
        (h_layer_lt : layer < xs.length),
        valAt (fw_stack xs) (layer * 131072 + jL * 64 + col) =
        valAt (xs.getD layer (zeroTensor [2048, 64])) (jL * 64 + col) := by
      intro xs h_head h_layer_lt
      have h_shape : (fw_stack xs).shape = xs.length :: [2048, 64] :=
        fw_stack_shape xs [2048, 64] h_head
      have h_prod : layer * 131072 + jL * 64 + col < prodShape (fw_stack xs).shape := by
        rw [h_shape]
        simp only [prodShape, List.foldl_cons, List.foldl_nil]
        -- xs.length * 131072 > layer * 131072 + jL * 64 + col.
        have : layer * 131072 + jL * 64 + col < xs.length * 131072 := by
          have h1 : jL * 64 + col < 131072 := by nlinarith [hjL_lt, hcol_lt]
          calc layer * 131072 + jL * 64 + col < layer * 131072 + 131072 := by omega
            _ = (layer + 1) * 131072 := by ring
            _ ≤ xs.length * 131072 := by
              apply Nat.mul_le_mul_right
              omega
        linarith [this]
      rw [valAt_of_lt _ _ h_prod]
      unfold fw_stack
      simp only [Tensor.mkShape, h_head]
      -- shardSize = prodShape [2048, 64] = 131072
      have hshard : prodShape ([2048, 64] : Shape) = 131072 := by decide
      simp only [hshard, show (131072 : Nat) = 0 ↔ False by decide, if_false, ↓reduceIte, iff_false]
      have hjLcol : jL * 64 + col < 131072 := by nlinarith [hjL_lt, hcol_lt]
      have hdiv : (layer * 131072 + jL * 64 + col) / 131072 = layer := by omega
      have hmod : (layer * 131072 + jL * 64 + col) % 131072 = jL * 64 + col := by omega
      rw [hdiv, hmod]
    -- Apply hfs_valAt to as/bs based on r.
    have h_layer_lt_as : layer < as.length := hlayer_lt
    have h_layer_lt_bs : layer < bs.length := by rw [hbs_len]; exact hlayer_lt
    rcases (by omega : r = 0 ∨ r = 1) with hr_eq | hr_eq
    · -- r = 0.
      rw [hr_eq]
      show valAt a_l (jL * 64 + col) =
           valAt (fw_stack as) (layer * 131072 + jL * 64 + col)
      rw [hfs_valAt as has_head h_layer_lt_as]
    · -- r = 1.
      rw [hr_eq]
      show valAt b_l (jL * 64 + col) =
           valAt (fw_stack bs) (layer * 131072 + jL * 64 + col)
      rw [hfs_valAt bs hbs_head h_layer_lt_bs]

/-- Chunk-gather round-trip for shape `[4096, 64]`, dim 0, 2 shards. -/
theorem allGather0_chunk0_id_4096_64 (x : Tensor) (hx : x.shape = [4096, 64]) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 0 2 r x).shape = [2048, 64] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r _ [4096, 64] hx (by omega)]
    rfl
  have hhead : (([chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [2048, 64] := by
    simp [hchunk_shape 0]
  have hG_shape : (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x]).shape
      = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hG_shape, hx]
  · intro idx hidx
    rw [hG_shape] at hidx
    have hidx_bound : idx < 262144 := by simpa [prodShape] using hidx
    have hx_prod : idx < prodShape x.shape := by rw [hx]; simpa [prodShape] using hidx_bound
    set row := idx / 64 with hrow_def
    set col := idx % 64 with hcol_def
    have hrow_lt : row < 4096 := by rw [hrow_def]; omega
    have hcol_lt : col < 64 := by rw [hcol_def]; omega
    set r := row / 2048 with hr_def
    set jL := row % 2048 with hjL_def
    have hr_lt : r < 2 := by rw [hr_def]; omega
    have hjL_lt : jL < 2048 := by rw [hjL_def]; omega
    have hidx_eq : idx = (r * 2048 + jL) * 64 + col := by
      rw [hr_def, hjL_def, hcol_def, hrow_def]; omega
    -- LHS: valAt gather at idx.
    have h_hyp : ∀ r' (_ : r' < 2),
        ([chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x].getD r' (zeroTensor [2048, 64])).shape
          = [2048, 64] := by
      intro r' _
      rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
        simp [List.getD, hchunk_shape 0, hchunk_shape 1]
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 2048 64 [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x]
        (by omega) (by omega) (by omega) hhead h_hyp r hr_lt jL hjL_lt col hcol_lt]
    -- RHS side: valAt x at ((r*2048+jL)*64+col).
    have hgetD_chunk : [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x].getD r
        (zeroTensor [2048, 64]) = chunkPrimDimN 0 2 r x := by
      rcases (by omega : r = 0 ∨ r = 1) with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_chunk]
    -- Now: valAt (chunkPrimDimN 0 2 r x) (jL * 64 + col) = valAt x ((r*2048+jL)*64+col).
    have hchunk_prod : jL * 64 + col < prodShape (chunkPrimDimN 0 2 r x).shape := by
      rw [hchunk_shape r]
      simp only [prodShape, List.foldl_cons, List.foldl_nil]
      nlinarith [hjL_lt, hcol_lt]
    rw [valAt_of_lt _ _ hchunk_prod]
    unfold chunkPrimDimN
    simp only [Tensor.mkShape, hx]
    -- Simplify concrete arithmetic.
    -- shape = [4096, 64], dimSize = 4096, numParts = 2, shardSize = 2048, postStride = 64,
    -- dimStride = 4096*64 = 262144, shardDimStride = 2048*64 = 131072.
    have h1 : ([4096, 64] : List Nat).getD 0 0 = 4096 := by rfl
    have h2 : List.drop (0 + 1) ([4096, 64] : List Nat) = [64] := by rfl
    have h3 : List.foldl (fun x1 x2 => x1 * x2) 1 ([64] : List Nat) = 64 := by rfl
    simp only [h1, h2, h3]
    -- Reduce ifs.
    simp only [show (2 : Nat) = 0 ↔ False by decide, show (64 : Nat) = 0 ↔ False by decide,
               show (2048 * 64 : Nat) = 0 ↔ False by decide,
               ↓reduceIte, iff_false]
    -- Now the chunkPrimDimN val closure: r' = 0 % 2 = 0, wait no — the closure uses "rank" param.
    -- The lemma is chunkPrimDimN 0 2 r x with r being 0 or 1.
    -- r_param = if 2 = 0 then r else r % 2 = r % 2 = r (since r < 2).
    have hr_mod : r % 2 = r := Nat.mod_eq_of_lt hr_lt
    simp only [hr_mod]
    -- Now valAt x (0 * 262144 + (r * 2048 + (jL * 64 + col) / 64) * 64 + (jL * 64 + col) % 64)
    -- We need = valAt x ((r*2048+jL)*64+col).
    have h_local_div : (jL * 64 + col) / 64 = jL := by omega
    have h_local_mod : (jL * 64 + col) % 64 = col := by omega
    -- After simp, the val closure is preIdx * dimStride + jFull * postStride + k
    -- where preIdx = (jL*64+col) / 131072 = 0, remainder = (jL*64+col) % 131072 = jL*64+col
    -- jLocal = (jL*64+col) / 64 = jL, k = (jL*64+col) % 64 = col
    -- jFull = r * 2048 + jL
    -- valAt x (0 * 262144 + (r * 2048 + jL) * 64 + col) = valAt x ((r*2048+jL)*64+col) ✓
    have hjLcol : jL * 64 + col < 131072 := by nlinarith [hjL_lt, hcol_lt]
    have hDivBig : (jL * 64 + col) / 131072 = 0 := by omega
    have hModBig : (jL * 64 + col) % 131072 = jL * 64 + col := by omega
    have hjc_div : (jL * 64 + col) / 64 = jL := h_local_div
    have hjc_mod : (jL * 64 + col) % 64 = col := h_local_mod
    -- The if-conditions from chunkPrimDimN.
    simp only [show (131072 : Nat) = 0 ↔ False by decide, ↓reduceIte, iff_false,
               hDivBig, hModBig, hjc_div, hjc_mod]
    ring_nf


/-- The 12 layer-12..23 routing members are CP zigzag-owned, so
`intermediateGoal_N` is no longer emitted for them: an ordinary dim-0 gather over
their shards is false on the full graph
(see trainverify/GOAL_3_4_LAYOUT_SPLIT.md).

This hypothesis states that ordinary-gather relation for the tids Pattern_4 needs.
It is **not** provable on the full graph and must not be discharged there. It IS
sound on this cut: `pm_goal_4` is a sliced subgraph built from `ChunkPrim` with no
`FW_maybe_shuffle` in it, so within the cut the shards really are contiguous.

Making it an explicit parameter keeps the dependency visible. Previously it was
derived silently from the emitter's incorrect goals, which is how a false
assumption reached a proof unnoticed. See PATTERN_4_ZIGZAG_DEPENDENCY.md. -/
def ZigzagCutGatherHyp (initSM initPM : Store) : Prop :=
  ∀ (ts a b : Nat), ts ∈ [5359, 5408, 5457, 5506, 5555, 5604, 5653, 5702,
                          5751, 5800, 5849, 5898] →
    initSM ts = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM a, initPM b]

theorem prove_goal_4
    (hZZ : ∀ initSM initPM, ZigzagCutGatherHyp initSM initPM) :
    goal_4_stmt_cut := by
  intro initSM initPM hSM hPM hInit
  have hZigzagGather := hZZ initSM initPM
  simp only [goal_4_cut_goal]
  have h4708_sm : (initSM 4708).shape = [4096, 64] := hSM 4708 [4096, 64] (by native_decide)
  have hpmR : pm_goal_4.numRanks = 2 := rfl
  have hscores_shape : ∀ (x : Tensor) (sh : Shape) (hx : x.shape = sh),
      (fw_topk_routing x 8 1).snd.snd.shape = sh := by
    intro x sh hx
    show (softmax x).shape = sh
    rw [softmax_shape_g18, hx]
  refine ⟨?shape_sm, ?shape_pm, ?value⟩
  case shape_sm =>
    rw [denote_sm_goal_4_4676 initSM]
    have hhead : (([(fw_topk_routing (initSM 4708) 8 1).snd.snd,
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
                    (fw_topk_routing (initSM 5898) 8 1).snd.snd] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [4096, 64] := by
      simp [hscores_shape _ [4096, 64] h4708_sm]
    rw [fw_stack_shape _ [4096, 64] hhead]
    rfl
  case shape_pm =>
    -- pmStore 4676 has shape [24, 4096, 64] via denote_pm_goal_4_4676 (allGather dim=1 on 2 shards).
    have h4708_pm : (initPM 4708).shape = [4096, 64] := hPM 4708 [4096, 64] (by native_decide)
    have hchunk_shape : ∀ (r : Nat) (x : Tensor) (_ : x.shape = [4096, 64]),
        (chunkPrimDimN 0 pm_goal_4.numRanks r x).shape = [2048, 64] := by
      intro r x hx
      rw [chunkPrimDimN_shape 0 pm_goal_4.numRanks r x [4096, 64] hx (by rw [hpmR]; omega)]
      rfl
    simp only [List.map]
    rw [denote_pm_goal_4_4676 initPM]
    -- Shape of each per-rank fw_stack shard (shape [24, 2048, 64]).
    have hstack_r0_head : (([
        (fw_topk_routing (chunkPrimDimN 0 pm_goal_4.numRanks 0 (initPM 4708)) 8 1).snd.snd,
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
        (fw_topk_routing (initPM 11621) 8 1).snd.snd] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [2048, 64] := by
      simp [hscores_shape _ [2048, 64] (hchunk_shape 0 _ h4708_pm)]
    have hstack_r0_shape := fw_stack_shape _ [2048, 64] hstack_r0_head
    -- allGather 1 with 2 shards each of shape [24, 2048, 64] → [24, 4096, 64].
    rw [hpmR]
    -- After rw [hpmR], the target has `chunkPrimDimN 0 2 r ...` (numRanks reduced).
    -- But hstack_r0_shape still has `pm_goal_4.numRanks`. Rewrite it too.
    rw [hpmR] at hstack_r0_shape
    have hRHS_head : (([
        fw_stack [(fw_topk_routing (chunkPrimDimN 0 2 0 (initPM 4708)) 8 1).snd.snd,
                  (fw_topk_routing (chunkPrimDimN 0 2 0 (initPM 4762)) 8 1).snd.snd,
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
        fw_stack [(fw_topk_routing (chunkPrimDimN 0 2 1 (initPM 4708)) 8 1).snd.snd,
                  (fw_topk_routing (chunkPrimDimN 0 2 1 (initPM 4762)) 8 1).snd.snd,
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
                  (fw_topk_routing (initPM 11622) 8 1).snd.snd]] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [24, 2048, 64] := by
      simp [hstack_r0_shape]
    rw [allGatherPrimDimN_shape 1 2 _ [24, 2048, 64] hRHS_head]
    rfl
  case value =>
    -- Unfold reconstructWithDim (singleton → identity).
    simp only [List.map, reconstructWithDim]
    -- Unfold LHS via SM machinery.
    rw [denote_sm_goal_4_4676 initSM]
    -- Unfold RHS via PM machinery.
    rw [denote_pm_goal_4_4676 initPM]
    rw [hpmR]
    -- Set up shape hypotheses for all initPM tids used in PM (layers 0/1 use initPM 4708/4762
    -- with shape [4096, 64]; layers 2..23 use initPM 7851, 7852, ..., 11621, 11622 with [2048, 64]).
    have h4708_pm : (initPM 4708).shape = [4096, 64] := hPM 4708 [4096, 64] (by native_decide)
    have h4762_pm : (initPM 4762).shape = [4096, 64] := hPM 4762 [4096, 64] (by native_decide)
    -- Extract intermediate goals: 24 total (2 singleton + 22 dual).
    have hInit' : InitGoalsHold pm_goal_4.numRanks goal_4_cut_initGoals initSM initPM := hInit
    -- Helper: extract initSM tid = expected value from intermediate goal, singleton case (layers 0/1).
    have extract_singleton : ∀ (g : LineageGoal) (_ : g ∈ goal_4_cut_initGoals)
        (tps_val : List Tensor) (h_ne : tps_val ≠ [])
        (_ : g.tps.map (fun p => initPM p.tid) = tps_val)
        (_ : g.replicated = false)
        (_ : tps_val.length = 1),
        initSM g.ts = tps_val.head h_ne := by
      intro g hg tps_val h_ne htps_eq hrep hlen
      have hgoal := hInit' g hg
      unfold InitGoalHolds at hgoal
      obtain ⟨_, _, hval⟩ := hgoal
      rw [reconstructForGoal_of_not_replicated g pm_goal_4.numRanks
            (g.tps.map (fun p => initPM p.tid)) hrep] at hval
      rw [htps_eq] at hval
      match tps_val, h_ne, hlen with
      | [x], _, _ =>
        simp only [reconstructWithDim, List.head] at hval ⊢
        exact hval
    -- Layer 0 boundary: initSM 4708 = initPM 4708.
    have hb_4708 : initSM 4708 = initPM 4708 := by
      have := extract_singleton intermediateGoal_4708 (by native_decide) [initPM 4708]
        (by simp) (by simp [intermediateGoal_4708]) (by rfl) (by rfl)
      simpa [intermediateGoal_4708, List.head] using this
    have hb_4762 : initSM 4762 = initPM 4762 := by
      have := extract_singleton intermediateGoal_4762 (by native_decide) [initPM 4762]
        (by simp) (by simp [intermediateGoal_4762]) (by rfl) (by rfl)
      simpa [intermediateGoal_4762, List.head] using this
    -- Helper for dual-piece (layers 2..23): initSM tid = allGather_0 [initPM p0, initPM p1].
    have extract_dual : ∀ (g : LineageGoal) (_ : g ∈ goal_4_cut_initGoals)
        (p0 p1 : Nat)
        (_ : g.tps.map (fun p => initPM p.tid) = [initPM p0, initPM p1])
        (_ : g.gatherDim = 0)
        (_ : g.replicated = false)
        (_ : g.tpShapes = [[2048, 64], [2048, 64]])
        (_ : (initPM p0).shape = [2048, 64]),
        initSM g.ts = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM p0, initPM p1] := by
      intro g hg p0 p1 htps hdim hrep hshapes hp0_shape
      have hgoal := hInit' g hg
      unfold InitGoalHolds at hgoal
      obtain ⟨_, _, hval⟩ := hgoal
      rw [reconstructForGoal_of_not_replicated g pm_goal_4.numRanks
            (g.tps.map (fun p => initPM p.tid)) hrep] at hval
      rw [htps, hdim] at hval
      -- reconstructWithDim on 2 elements with head shape ≠ [1] gives allGather.
      have hrec : reconstructWithDim 0 pm_goal_4.numRanks 0 [initPM p0, initPM p1]
          = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM p0, initPM p1] := by
        unfold reconstructWithDim
        -- Match unfolds; head/head?.map . shape = some [2048, 64].
        simp only [List.head?, Option.map_some, Option.getD_some, hp0_shape,
                   show ([2048, 64] : List Nat) = [1] ↔ False by decide, ↓reduceIte, iff_false]
      rw [hrec] at hval
      exact hval
    -- Layers 2..23 boundaries — 22 more extract_dual calls.
    have h7851_pm : (initPM 7851).shape = [2048, 64] := hPM 7851 [2048, 64] (by native_decide)
    have hb_4816 : initSM 4816 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 7851, initPM 7852] :=
      extract_dual intermediateGoal_4816 (by native_decide) 7851 7852
        (by simp [intermediateGoal_4816]) (by rfl) (by rfl) (by rfl) h7851_pm
    have h8037_pm : (initPM 8037).shape = [2048, 64] := hPM 8037 [2048, 64] (by native_decide)
    have hb_4870 : initSM 4870 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 8037, initPM 8038] :=
      extract_dual intermediateGoal_4870 (by native_decide) 8037 8038
        (by simp [intermediateGoal_4870]) (by rfl) (by rfl) (by rfl) h8037_pm
    have h8223_pm : (initPM 8223).shape = [2048, 64] := hPM 8223 [2048, 64] (by native_decide)
    have hb_4924 : initSM 4924 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 8223, initPM 8224] :=
      extract_dual intermediateGoal_4924 (by native_decide) 8223 8224
        (by simp [intermediateGoal_4924]) (by rfl) (by rfl) (by rfl) h8223_pm
    have h8409_pm : (initPM 8409).shape = [2048, 64] := hPM 8409 [2048, 64] (by native_decide)
    have hb_4978 : initSM 4978 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 8409, initPM 8410] :=
      extract_dual intermediateGoal_4978 (by native_decide) 8409 8410
        (by simp [intermediateGoal_4978]) (by rfl) (by rfl) (by rfl) h8409_pm
    have h8595_pm : (initPM 8595).shape = [2048, 64] := hPM 8595 [2048, 64] (by native_decide)
    have hb_5032 : initSM 5032 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 8595, initPM 8596] :=
      extract_dual intermediateGoal_5032 (by native_decide) 8595 8596
        (by simp [intermediateGoal_5032]) (by rfl) (by rfl) (by rfl) h8595_pm
    have h8781_pm : (initPM 8781).shape = [2048, 64] := hPM 8781 [2048, 64] (by native_decide)
    have hb_5086 : initSM 5086 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 8781, initPM 8782] :=
      extract_dual intermediateGoal_5086 (by native_decide) 8781 8782
        (by simp [intermediateGoal_5086]) (by rfl) (by rfl) (by rfl) h8781_pm
    have h8967_pm : (initPM 8967).shape = [2048, 64] := hPM 8967 [2048, 64] (by native_decide)
    have hb_5140 : initSM 5140 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 8967, initPM 8968] :=
      extract_dual intermediateGoal_5140 (by native_decide) 8967 8968
        (by simp [intermediateGoal_5140]) (by rfl) (by rfl) (by rfl) h8967_pm
    have h9153_pm : (initPM 9153).shape = [2048, 64] := hPM 9153 [2048, 64] (by native_decide)
    have hb_5194 : initSM 5194 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 9153, initPM 9154] :=
      extract_dual intermediateGoal_5194 (by native_decide) 9153 9154
        (by simp [intermediateGoal_5194]) (by rfl) (by rfl) (by rfl) h9153_pm
    have h9339_pm : (initPM 9339).shape = [2048, 64] := hPM 9339 [2048, 64] (by native_decide)
    have hb_5248 : initSM 5248 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 9339, initPM 9340] :=
      extract_dual intermediateGoal_5248 (by native_decide) 9339 9340
        (by simp [intermediateGoal_5248]) (by rfl) (by rfl) (by rfl) h9339_pm
    have h9525_pm : (initPM 9525).shape = [2048, 64] := hPM 9525 [2048, 64] (by native_decide)
    have hb_5302 : initSM 5302 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 9525, initPM 9526] :=
      extract_dual intermediateGoal_5302 (by native_decide) 9525 9526
        (by simp [intermediateGoal_5302]) (by rfl) (by rfl) (by rfl) h9525_pm
    have h9729_pm : (initPM 9729).shape = [2048, 64] := hPM 9729 [2048, 64] (by native_decide)
    -- tid 5359 is CP zigzag-owned; `intermediateGoal_5359` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5359 : initSM 5359 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 9729, initPM 9730] :=
      hZigzagGather 5359 9729 9730 (by decide)
    have h9901_pm : (initPM 9901).shape = [2048, 64] := hPM 9901 [2048, 64] (by native_decide)
    -- tid 5408 is CP zigzag-owned; `intermediateGoal_5408` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5408 : initSM 5408 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 9901, initPM 9902] :=
      hZigzagGather 5408 9901 9902 (by decide)
    have h10073_pm : (initPM 10073).shape = [2048, 64] := hPM 10073 [2048, 64] (by native_decide)
    -- tid 5457 is CP zigzag-owned; `intermediateGoal_5457` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5457 : initSM 5457 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 10073, initPM 10074] :=
      hZigzagGather 5457 10073 10074 (by decide)
    have h10245_pm : (initPM 10245).shape = [2048, 64] := hPM 10245 [2048, 64] (by native_decide)
    -- tid 5506 is CP zigzag-owned; `intermediateGoal_5506` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5506 : initSM 5506 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 10245, initPM 10246] :=
      hZigzagGather 5506 10245 10246 (by decide)
    have h10417_pm : (initPM 10417).shape = [2048, 64] := hPM 10417 [2048, 64] (by native_decide)
    -- tid 5555 is CP zigzag-owned; `intermediateGoal_5555` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5555 : initSM 5555 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 10417, initPM 10418] :=
      hZigzagGather 5555 10417 10418 (by decide)
    have h10589_pm : (initPM 10589).shape = [2048, 64] := hPM 10589 [2048, 64] (by native_decide)
    -- tid 5604 is CP zigzag-owned; `intermediateGoal_5604` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5604 : initSM 5604 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 10589, initPM 10590] :=
      hZigzagGather 5604 10589 10590 (by decide)
    have h10761_pm : (initPM 10761).shape = [2048, 64] := hPM 10761 [2048, 64] (by native_decide)
    -- tid 5653 is CP zigzag-owned; `intermediateGoal_5653` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5653 : initSM 5653 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 10761, initPM 10762] :=
      hZigzagGather 5653 10761 10762 (by decide)
    have h10933_pm : (initPM 10933).shape = [2048, 64] := hPM 10933 [2048, 64] (by native_decide)
    -- tid 5702 is CP zigzag-owned; `intermediateGoal_5702` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5702 : initSM 5702 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 10933, initPM 10934] :=
      hZigzagGather 5702 10933 10934 (by decide)
    have h11105_pm : (initPM 11105).shape = [2048, 64] := hPM 11105 [2048, 64] (by native_decide)
    -- tid 5751 is CP zigzag-owned; `intermediateGoal_5751` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5751 : initSM 5751 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 11105, initPM 11106] :=
      hZigzagGather 5751 11105 11106 (by decide)
    have h11277_pm : (initPM 11277).shape = [2048, 64] := hPM 11277 [2048, 64] (by native_decide)
    -- tid 5800 is CP zigzag-owned; `intermediateGoal_5800` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5800 : initSM 5800 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 11277, initPM 11278] :=
      hZigzagGather 5800 11277 11278 (by decide)
    have h11449_pm : (initPM 11449).shape = [2048, 64] := hPM 11449 [2048, 64] (by native_decide)
    -- tid 5849 is CP zigzag-owned; `intermediateGoal_5849` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5849 : initSM 5849 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 11449, initPM 11450] :=
      hZigzagGather 5849 11449 11450 (by decide)
    have h11621_pm : (initPM 11621).shape = [2048, 64] := hPM 11621 [2048, 64] (by native_decide)
    -- tid 5898 is CP zigzag-owned; `intermediateGoal_5898` is no longer emitted
    -- because an ordinary gather over its shards is FALSE (see
    -- see trainverify/GOAL_3_4_LAYOUT_SPLIT.md). Taken as an explicit
    -- hypothesis so the dependency is visible rather than silently derived.
    have hb_5898 : initSM 5898 = allGatherPrimDimN 0 pm_goal_4.numRanks 0 [initPM 11621, initPM 11622] :=
      hZigzagGather 5898 11621 11622 (by decide)
    -- Layer 0/1 special: rewrite initSM 4708/4762 = initPM 4708/4762, then softmax → allGather form.
    rw [hb_4708, hb_4762]
    -- Layer 2..23: rewrite initSM = allGather.
    rw [hb_4816, hb_4870, hb_4924, hb_4978, hb_5032, hb_5086, hb_5140, hb_5194,
        hb_5248, hb_5302, hb_5359, hb_5408, hb_5457, hb_5506, hb_5555, hb_5604,
        hb_5653, hb_5702, hb_5751, hb_5800, hb_5849, hb_5898]
    rw [hpmR]
    -- For layers 0/1, apply softmax_allGather2 after chunk-gather round-trip.
    -- softmax (initPM 4708) = softmax (allGather_0 [chunk_0 initPM 4708, chunk_1 initPM 4708])
    --                       = allGather_0 [softmax (chunk_0 initPM 4708), softmax (chunk_1 initPM 4708)]
    have hL0 : softmax (initPM 4708) =
        allGatherPrimDimN 0 2 0 [softmax (chunkPrimDimN 0 2 0 (initPM 4708)),
                                  softmax (chunkPrimDimN 0 2 1 (initPM 4708))] := by
      have hchunk0 : (chunkPrimDimN 0 2 0 (initPM 4708)).shape = [2048, 64] := by
        rw [chunkPrimDimN_shape 0 2 0 _ [4096, 64] h4708_pm (by omega)]; rfl
      have hchunk1 : (chunkPrimDimN 0 2 1 (initPM 4708)).shape = [2048, 64] := by
        rw [chunkPrimDimN_shape 0 2 1 _ [4096, 64] h4708_pm (by omega)]; rfl
      -- softmax (initPM 4708) = softmax (allGather ...) (using round-trip only on LHS).
      conv_lhs => rw [← allGather0_chunk0_id_4096_64 (initPM 4708) h4708_pm]
      exact softmax_allGather2_dim0_2048_64 _ _ hchunk0 hchunk1
    have hL1 : softmax (initPM 4762) =
        allGatherPrimDimN 0 2 0 [softmax (chunkPrimDimN 0 2 0 (initPM 4762)),
                                  softmax (chunkPrimDimN 0 2 1 (initPM 4762))] := by
      have hchunk0 : (chunkPrimDimN 0 2 0 (initPM 4762)).shape = [2048, 64] := by
        rw [chunkPrimDimN_shape 0 2 0 _ [4096, 64] h4762_pm (by omega)]; rfl
      have hchunk1 : (chunkPrimDimN 0 2 1 (initPM 4762)).shape = [2048, 64] := by
        rw [chunkPrimDimN_shape 0 2 1 _ [4096, 64] h4762_pm (by omega)]; rfl
      conv_lhs => rw [← allGather0_chunk0_id_4096_64 (initPM 4762) h4762_pm]
      exact softmax_allGather2_dim0_2048_64 _ _ hchunk0 hchunk1
    -- For layers 2..23, apply softmax_allGather2 directly.
    have hL2 := softmax_allGather2_dim0_2048_64 _ _ h7851_pm
                    (show (initPM 7852).shape = [2048, 64] from hPM 7852 [2048, 64] (by native_decide))
    have hL3 := softmax_allGather2_dim0_2048_64 _ _ h8037_pm
                    (show (initPM 8038).shape = [2048, 64] from hPM 8038 [2048, 64] (by native_decide))
    have hL4 := softmax_allGather2_dim0_2048_64 _ _ h8223_pm
                    (show (initPM 8224).shape = [2048, 64] from hPM 8224 [2048, 64] (by native_decide))
    have hL5 := softmax_allGather2_dim0_2048_64 _ _ h8409_pm
                    (show (initPM 8410).shape = [2048, 64] from hPM 8410 [2048, 64] (by native_decide))
    have hL6 := softmax_allGather2_dim0_2048_64 _ _ h8595_pm
                    (show (initPM 8596).shape = [2048, 64] from hPM 8596 [2048, 64] (by native_decide))
    have hL7 := softmax_allGather2_dim0_2048_64 _ _ h8781_pm
                    (show (initPM 8782).shape = [2048, 64] from hPM 8782 [2048, 64] (by native_decide))
    have hL8 := softmax_allGather2_dim0_2048_64 _ _ h8967_pm
                    (show (initPM 8968).shape = [2048, 64] from hPM 8968 [2048, 64] (by native_decide))
    have hL9 := softmax_allGather2_dim0_2048_64 _ _ h9153_pm
                    (show (initPM 9154).shape = [2048, 64] from hPM 9154 [2048, 64] (by native_decide))
    have hL10 := softmax_allGather2_dim0_2048_64 _ _ h9339_pm
                    (show (initPM 9340).shape = [2048, 64] from hPM 9340 [2048, 64] (by native_decide))
    have hL11 := softmax_allGather2_dim0_2048_64 _ _ h9525_pm
                    (show (initPM 9526).shape = [2048, 64] from hPM 9526 [2048, 64] (by native_decide))
    have hL12 := softmax_allGather2_dim0_2048_64 _ _ h9729_pm
                    (show (initPM 9730).shape = [2048, 64] from hPM 9730 [2048, 64] (by native_decide))
    have hL13 := softmax_allGather2_dim0_2048_64 _ _ h9901_pm
                    (show (initPM 9902).shape = [2048, 64] from hPM 9902 [2048, 64] (by native_decide))
    have hL14 := softmax_allGather2_dim0_2048_64 _ _ h10073_pm
                    (show (initPM 10074).shape = [2048, 64] from hPM 10074 [2048, 64] (by native_decide))
    have hL15 := softmax_allGather2_dim0_2048_64 _ _ h10245_pm
                    (show (initPM 10246).shape = [2048, 64] from hPM 10246 [2048, 64] (by native_decide))
    have hL16 := softmax_allGather2_dim0_2048_64 _ _ h10417_pm
                    (show (initPM 10418).shape = [2048, 64] from hPM 10418 [2048, 64] (by native_decide))
    have hL17 := softmax_allGather2_dim0_2048_64 _ _ h10589_pm
                    (show (initPM 10590).shape = [2048, 64] from hPM 10590 [2048, 64] (by native_decide))
    have hL18 := softmax_allGather2_dim0_2048_64 _ _ h10761_pm
                    (show (initPM 10762).shape = [2048, 64] from hPM 10762 [2048, 64] (by native_decide))
    have hL19 := softmax_allGather2_dim0_2048_64 _ _ h10933_pm
                    (show (initPM 10934).shape = [2048, 64] from hPM 10934 [2048, 64] (by native_decide))
    have hL20 := softmax_allGather2_dim0_2048_64 _ _ h11105_pm
                    (show (initPM 11106).shape = [2048, 64] from hPM 11106 [2048, 64] (by native_decide))
    have hL21 := softmax_allGather2_dim0_2048_64 _ _ h11277_pm
                    (show (initPM 11278).shape = [2048, 64] from hPM 11278 [2048, 64] (by native_decide))
    have hL22 := softmax_allGather2_dim0_2048_64 _ _ h11449_pm
                    (show (initPM 11450).shape = [2048, 64] from hPM 11450 [2048, 64] (by native_decide))
    have hL23 := softmax_allGather2_dim0_2048_64 _ _ h11621_pm
                    (show (initPM 11622).shape = [2048, 64] from hPM 11622 [2048, 64] (by native_decide))
    -- Rewrite fw_topk_routing .snd.snd = softmax on LHS.
    -- Then apply hL0..hL23 to convert each SM softmax to allGather form.
    -- Note: (fw_topk_routing x 8 1).snd.snd = softmax x (by unfold).
    -- Wait — we've already applied hb_XXX to substitute initSM → initPM/allGather.
    -- Now LHS is: fw_stack [(fw_topk_routing (initPM 4708) 8 1).snd.snd,
    --                       (fw_topk_routing (initPM 4762) 8 1).snd.snd,
    --                       (fw_topk_routing (allGather_0 [initPM 7851, initPM 7852]) 8 1).snd.snd, ...]
    -- Need to unfold .snd.snd = softmax and then apply hL0..hL23.
    -- Let me first show softmax = .snd.snd equality generically then rewrite.
    have hunf : ∀ x : Tensor, (fw_topk_routing x 8 1).snd.snd = softmax x := by
      intro x; rfl
    simp only [hunf]
    -- Now apply per-layer transforms.
    rw [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9, hL10, hL11,
        hL12, hL13, hL14, hL15, hL16, hL17, hL18, hL19, hL20, hL21, hL22, hL23]
    -- LHS: fw_stack of 24 allGather_0 pairs.
    -- RHS: allGather_1 [fw_stack r0_24, fw_stack r1_24].
    -- Apply Lemma B: fw_stack (zipWith f as bs) = allGather_1 [fw_stack as, fw_stack bs].
    -- First rewrite LHS in zipWith form.
    set as := [softmax (chunkPrimDimN 0 2 0 (initPM 4708)),
               softmax (chunkPrimDimN 0 2 0 (initPM 4762)),
               softmax (initPM 7851), softmax (initPM 8037), softmax (initPM 8223),
               softmax (initPM 8409), softmax (initPM 8595), softmax (initPM 8781),
               softmax (initPM 8967), softmax (initPM 9153), softmax (initPM 9339),
               softmax (initPM 9525), softmax (initPM 9729), softmax (initPM 9901),
               softmax (initPM 10073), softmax (initPM 10245), softmax (initPM 10417),
               softmax (initPM 10589), softmax (initPM 10761), softmax (initPM 10933),
               softmax (initPM 11105), softmax (initPM 11277), softmax (initPM 11449),
               softmax (initPM 11621)] with has_def
    set bs := [softmax (chunkPrimDimN 0 2 1 (initPM 4708)),
               softmax (chunkPrimDimN 0 2 1 (initPM 4762)),
               softmax (initPM 7852), softmax (initPM 8038), softmax (initPM 8224),
               softmax (initPM 8410), softmax (initPM 8596), softmax (initPM 8782),
               softmax (initPM 8968), softmax (initPM 9154), softmax (initPM 9340),
               softmax (initPM 9526), softmax (initPM 9730), softmax (initPM 9902),
               softmax (initPM 10074), softmax (initPM 10246), softmax (initPM 10418),
               softmax (initPM 10590), softmax (initPM 10762), softmax (initPM 10934),
               softmax (initPM 11106), softmax (initPM 11278), softmax (initPM 11450),
               softmax (initPM 11622)] with hbs_def
    -- Show that the LHS's 24 allGather_0 pairs equal zipWith (allGather_0) as bs.
    have h_zip_eq : List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs
        = [allGatherPrimDimN 0 2 0 [softmax (chunkPrimDimN 0 2 0 (initPM 4708)),
                                    softmax (chunkPrimDimN 0 2 1 (initPM 4708))],
           allGatherPrimDimN 0 2 0 [softmax (chunkPrimDimN 0 2 0 (initPM 4762)),
                                    softmax (chunkPrimDimN 0 2 1 (initPM 4762))],
           allGatherPrimDimN 0 2 0 [softmax (initPM 7851), softmax (initPM 7852)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 8037), softmax (initPM 8038)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 8223), softmax (initPM 8224)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 8409), softmax (initPM 8410)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 8595), softmax (initPM 8596)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 8781), softmax (initPM 8782)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 8967), softmax (initPM 8968)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 9153), softmax (initPM 9154)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 9339), softmax (initPM 9340)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 9525), softmax (initPM 9526)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 9729), softmax (initPM 9730)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 9901), softmax (initPM 9902)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 10073), softmax (initPM 10074)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 10245), softmax (initPM 10246)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 10417), softmax (initPM 10418)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 10589), softmax (initPM 10590)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 10761), softmax (initPM 10762)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 10933), softmax (initPM 10934)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 11105), softmax (initPM 11106)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 11277), softmax (initPM 11278)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 11449), softmax (initPM 11450)],
           allGatherPrimDimN 0 2 0 [softmax (initPM 11621), softmax (initPM 11622)]] := by
      rw [has_def, hbs_def]; rfl
    -- Show that as and bs have length 24 and all elements have shape [2048, 64].
    have has_len : as.length = 24 := by rw [has_def]; rfl
    have hbs_len : bs.length = 24 := by rw [hbs_def]; rfl
    have hlen_eq : as.length = bs.length := by rw [has_len, hbs_len]
    have has_ne : as ≠ [] := by rw [has_def]; simp
    -- All as elements: shape [2048, 64] (via softmax_shape_g18 + chunk shape / initPM shape).
    have h_smshape : ∀ (x : Tensor), x.shape = [2048, 64] → (softmax x).shape = [2048, 64] := by
      intro x hx; rw [softmax_shape_g18, hx]
    have h_chunk_shape_r : ∀ (r : Nat) (t : Tensor), t.shape = [4096, 64] →
        (chunkPrimDimN 0 2 r t).shape = [2048, 64] := by
      intro r t ht
      rw [chunkPrimDimN_shape 0 2 r _ [4096, 64] ht (by omega)]; rfl
    have hAs : ∀ a ∈ as, a.shape = [2048, 64] := by
      intro a ha
      rw [has_def] at ha
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
      rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals (rw [h]; apply h_smshape)
      · exact h_chunk_shape_r 0 _ h4708_pm
      · exact h_chunk_shape_r 0 _ h4762_pm
      · exact h7851_pm
      · exact h8037_pm
      · exact h8223_pm
      · exact h8409_pm
      · exact h8595_pm
      · exact h8781_pm
      · exact h8967_pm
      · exact h9153_pm
      · exact h9339_pm
      · exact h9525_pm
      · exact h9729_pm
      · exact h9901_pm
      · exact h10073_pm
      · exact h10245_pm
      · exact h10417_pm
      · exact h10589_pm
      · exact h10761_pm
      · exact h10933_pm
      · exact h11105_pm
      · exact h11277_pm
      · exact h11449_pm
      · exact h11621_pm
    have hBs : ∀ b ∈ bs, b.shape = [2048, 64] := by
      intro b hb
      rw [hbs_def] at hb
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
      have h7852_pm : (initPM 7852).shape = [2048, 64] := hPM 7852 [2048, 64] (by native_decide)
      have h8038_pm : (initPM 8038).shape = [2048, 64] := hPM 8038 [2048, 64] (by native_decide)
      have h8224_pm : (initPM 8224).shape = [2048, 64] := hPM 8224 [2048, 64] (by native_decide)
      have h8410_pm : (initPM 8410).shape = [2048, 64] := hPM 8410 [2048, 64] (by native_decide)
      have h8596_pm : (initPM 8596).shape = [2048, 64] := hPM 8596 [2048, 64] (by native_decide)
      have h8782_pm : (initPM 8782).shape = [2048, 64] := hPM 8782 [2048, 64] (by native_decide)
      have h8968_pm : (initPM 8968).shape = [2048, 64] := hPM 8968 [2048, 64] (by native_decide)
      have h9154_pm : (initPM 9154).shape = [2048, 64] := hPM 9154 [2048, 64] (by native_decide)
      have h9340_pm : (initPM 9340).shape = [2048, 64] := hPM 9340 [2048, 64] (by native_decide)
      have h9526_pm : (initPM 9526).shape = [2048, 64] := hPM 9526 [2048, 64] (by native_decide)
      have h9730_pm : (initPM 9730).shape = [2048, 64] := hPM 9730 [2048, 64] (by native_decide)
      have h9902_pm : (initPM 9902).shape = [2048, 64] := hPM 9902 [2048, 64] (by native_decide)
      have h10074_pm : (initPM 10074).shape = [2048, 64] := hPM 10074 [2048, 64] (by native_decide)
      have h10246_pm : (initPM 10246).shape = [2048, 64] := hPM 10246 [2048, 64] (by native_decide)
      have h10418_pm : (initPM 10418).shape = [2048, 64] := hPM 10418 [2048, 64] (by native_decide)
      have h10590_pm : (initPM 10590).shape = [2048, 64] := hPM 10590 [2048, 64] (by native_decide)
      have h10762_pm : (initPM 10762).shape = [2048, 64] := hPM 10762 [2048, 64] (by native_decide)
      have h10934_pm : (initPM 10934).shape = [2048, 64] := hPM 10934 [2048, 64] (by native_decide)
      have h11106_pm : (initPM 11106).shape = [2048, 64] := hPM 11106 [2048, 64] (by native_decide)
      have h11278_pm : (initPM 11278).shape = [2048, 64] := hPM 11278 [2048, 64] (by native_decide)
      have h11450_pm : (initPM 11450).shape = [2048, 64] := hPM 11450 [2048, 64] (by native_decide)
      have h11622_pm : (initPM 11622).shape = [2048, 64] := hPM 11622 [2048, 64] (by native_decide)
      rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals (rw [h]; apply h_smshape)
      · exact h_chunk_shape_r 1 _ h4708_pm
      · exact h_chunk_shape_r 1 _ h4762_pm
      · exact h7852_pm
      · exact h8038_pm
      · exact h8224_pm
      · exact h8410_pm
      · exact h8596_pm
      · exact h8782_pm
      · exact h8968_pm
      · exact h9154_pm
      · exact h9340_pm
      · exact h9526_pm
      · exact h9730_pm
      · exact h9902_pm
      · exact h10074_pm
      · exact h10246_pm
      · exact h10418_pm
      · exact h10590_pm
      · exact h10762_pm
      · exact h10934_pm
      · exact h11106_pm
      · exact h11278_pm
      · exact h11450_pm
      · exact h11622_pm
    -- Now apply Lemma B.
    have hLemmaB := stack_allGather_commute_generic_2048_64 as bs hlen_eq has_ne hAs hBs
    -- hLemmaB : fw_stack (zipWith ...) = allGather_1 [fw_stack as, fw_stack bs].
    -- Convert LHS from fw_stack [24 allGathers] to fw_stack (zipWith).
    rw [← h_zip_eq]
    -- Now goal is: fw_stack (zipWith f as bs) = allGather_1 [fw_stack as, fw_stack bs].
    exact hLemmaB

theorem prove_pattern_4
    (hZZ : ∀ initSM initPM, ZigzagCutGatherHyp initSM initPM) :
    pattern_4_stmt := by
  intro target h
  cases h
  exact prove_goal_4 hZZ

end TrainVerify.Denote.GeneratedPatterns