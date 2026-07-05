/- Pattern_3: 24-layer YOCO attention pipeline sharding-commute proof.

   Pattern: 3
   Hash: b3365746c5960899
   Goals: 3 (prereq: goal_5)
   Op flavour: full attention pipeline
     SM = 903 ops, PM = 1866 ops
     - rms_norm, per_head_mix_precision_linear, rotary_embedding
     - attn_sliding_window (windowLeft=512, intra-rank)
     - attn_zigzag (cross-rank ring-attention → uses ring semantics)
     - all2all_moe_gmm (expert-parallel MoE, same as Pattern_1)
     - fw_add, fw_mul, view, reshape, multiref, sigmoid, swiglu, mix_precision_linear
     - final fw_stack of 24 layer outputs; AllGatherPrim on dim 1

   Design decision (2026-07-04): use ring-attention semantics
   (`denoteGraph_ringAttn` + `CoarseLineageHoldsWithInit_ringAttn`) rather
   than the identity model, to be 100% faithful to Python
   `wrap_zigzag_attn_func` behavior. See Denote.lean line 20821+.

   The `goal_3_stmt_cut_ringAttn` below is the ring-attention–aware version
   of `goal_3_stmt_cut`; the plain version uses the identity model on
   FW_attn_zigzag which would make the goal false (SM=full attn ≠ PM=identity).
-/
import denote.yoco_goals.Goal_3
import denote.yoco_goals.Pattern_1  -- reuse fw_topk_routing_snd_fst_allGather0_commute_2_of (routing_map commute)

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

/-- Ring-attention–aware variant of `goal_3_stmt_cut`. Uses `denoteGraph_ringAttn`
    to model the cross-rank ring attention in `FW_attn_zigzag` faithfully. -/
def goal_3_stmt_cut_ringAttn : Prop :=
  CoarseLineageHoldsWithInit_ringAttn sm_goal_3 pm_goal_3 goal_3
    sm_goal_3InitEnv pm_goal_3InitEnv goal_3_cut_initGoals

def pattern_3_goalIds : List Nat := [3]

inductive pattern_3_target : Prop → Prop
  | goal_3 : pattern_3_target goal_3_stmt_cut_ringAttn

def pattern_3_stmt : Prop :=
  ∀ {target : Prop}, pattern_3_target target → target

/-- Prerequisite: proves `goal_3_stmt_cut_ringAttn` given all Store shape
    hypotheses, init goal hypotheses (including goal_5 as a prereq). -/
theorem prove_goal_3 : goal_3_stmt_cut_ringAttn := by
  sorry
  -- Hand-proof: uses Pattern_1's fw_all2all_moe_gmm_full_split_commute_2
  -- lemma (already proven), applied per layer, chained through 24 layers,
  -- lifted via fw_stack + AllGatherPrim on dim 1. Ring-attn semantics
  -- ensure attn commutes with token-dim chunking (via allgather-then-attn).

theorem prove_pattern_3 : pattern_3_stmt := by
  intro target ht
  cases ht
  exact prove_goal_3

/-! ### Phase 1 (fold-bridge): ring-fold prefix bridges for per-tid evaluation.

    Parallel to Pattern_1's `foldl_take_split_at_not_written` (which is stated
    for the plain `applyNode` fold), these bridge the `applyNodeRingAttn` fold
    used by `denoteGraph_ringAttn`. They let the per-tid unfolding of
    `denoteGraph_ringAttn sm_goal_3 / pm_goal_3` walk graph nodes:

    * `foldl_prefix_eq_full_ringAttn` — the single ENTRY bridge: the value of a
      tid in the full-graph ring-fold equals its value after the prefix
      `nodes.take k`, provided no node in the suffix writes it. Used once to jump
      from the (huge) full graph down to the small dependency-cone prefix.
    * `foldl_take_split_at_not_written_ringAttn` — the BODY bridge (small
      windows): post-writer preservation across a `(take k).drop j` span, exactly
      like Pattern_1's helper but for the ring fold. -/

/-- Ring-fold analogue of Pattern_1's `foldl_take_split_at_not_written`: after
    the writer of `tid` (inside `nodes.take j`), applying more non-writing nodes
    up to `k` preserves the value. The extra `hnil` hypothesis handles the ring
    branches (which write at `n.outs.getD 0 0`); every real graph node emits at
    least one output, so it is always dischargeable. -/
theorem foldl_take_split_at_not_written_ringAttn
    (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid) (j k : Nat) (hjk : j ≤ k)
    (hnil : ∀ n ∈ (nodes.take k).drop j, n.outs ≠ [])
    (h : ∀ n ∈ (nodes.take k).drop j, tid ∉ n.outs) :
    (nodes.take k).foldl (applyNodeRingAttn g) s tid =
      (nodes.take j).foldl (applyNodeRingAttn g) s tid := by
  have h_split : nodes.take k = nodes.take j ++ (nodes.take k).drop j := by
    rw [show nodes.take j = (nodes.take k).take j by rw [List.take_take, min_eq_left hjk]]
    rw [List.take_append_drop]
  rw [h_split, List.foldl_append]
  exact foldl_applyNodeRingAttn_at_not_written g _ _ tid hnil h

/-- Entry bridge: the value at `tid` in the full-graph ring-fold equals its
    value after the prefix `nodes.take k`, provided no node in the suffix
    `nodes.drop k` writes `tid`. Used once per target tid to jump from the full
    903/1866-node graph down to the small dependency-cone prefix, after which
    `foldl_take_split_at_not_written_ringAttn` handles the body. -/
theorem foldl_prefix_eq_full_ringAttn
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ nodes.drop k, n.outs ≠ [])
    (h : ∀ n ∈ nodes.drop k, tid ∉ n.outs) :
    nodes.foldl (applyNodeRingAttn g) s tid =
      (nodes.take k).foldl (applyNodeRingAttn g) s tid := by
  conv_lhs => rw [← List.take_append_drop k nodes, List.foldl_append]
  exact foldl_applyNodeRingAttn_at_not_written g _ _ tid hnil h

/-! ### Phase 3 (fold-bridge): per-tid ring-fold evaluation.

    Following Pattern_1's `denote_sm_goal_1_XXX` template, adapted to the
    ring-attention fold. Each theorem unfolds `denoteGraph_ringAttn sm_goal_3`
    at a specific tid to a closed expression in `initSM` (and, where the
    dependency cone crosses a ring-attention node, an opaque
    `applyNodeRingAttn_{sliding_window,zigzag}` call on the prefix state — this
    is exactly the intended `<op_semantic> (S <inputTid>)` form). -/

/-- Milestone: the layer-0 attention output tid `4696` evaluates to the
    ring sliding-window semantics on the take-8 prefix state. Validates the
    entry bridge + `applyNodeRingAttn_sliding_window_out`. -/
theorem denote_sm_goal_3_4696 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 4696 =
      applyNodeRingAttn_sliding_window sm_goal_3
        ((sm_goal_3.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3) initSM)
        { rank := 0, op := "OpName.FW_attn_sliding_window",
          ins := [4692, 4693, 4689, 4694, 4695], outs := [4696],
          params := [16, 4, 64, 64, 1, 512] } := by
  have hEntry : denoteGraph_ringAttn sm_goal_3 initSM 4696 =
      (sm_goal_3.nodes.take 9).foldl (applyNodeRingAttn sm_goal_3) initSM 4696 := by
    show sm_goal_3.nodes.foldl (applyNodeRingAttn sm_goal_3) initSM 4696 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4696 9
      (by decide) (by decide)
  rw [hEntry,
      show (sm_goal_3.nodes.take 9).foldl (applyNodeRingAttn sm_goal_3) initSM =
        applyNodeRingAttn sm_goal_3
          ((sm_goal_3.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3) initSM)
          { rank := 0, op := "OpName.FW_attn_sliding_window",
            ins := [4692, 4693, 4689, 4694, 4695], outs := [4696],
            params := [16, 4, 64, 64, 1, 512] } from by
        rw [show sm_goal_3.nodes.take 9 = sm_goal_3.nodes.take 8 ++
            [{ rank := 0, op := "OpName.FW_attn_sliding_window",
               ins := [4692, 4693, 4689, 4694, 4695], outs := [4696],
               params := [16, 4, 64, 64, 1, 512] }] from rfl,
            List.foldl_append, List.foldl_cons, List.foldl_nil]]
  exact applyNodeRingAttn_sliding_window_out sm_goal_3
    ((sm_goal_3.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3) initSM)
    0 4692 4693 4689 4694 4695 4696 [16, 4, 64, 64, 1, 512]

/-- Generic `FW_multiref` (2 outputs) second-output reader. Complements the
    existing `applyNode_fw_multiref2_first_out`. -/
theorem applyNode_fw_multiref2_second_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 : Tid) (h12 : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2], params := [2] } t2 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2].zip (List.replicate 2 (s xTid))) t2 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, h12]

/-- Generic `FW_multiref` (5 outputs) first-output reader. Complements the
    existing `applyNode_fw_multiref5_at_pos{1,2,3,4}_out`. -/
theorem applyNode_fw_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]


/-! ### Phase 3: generated per-tid unfolding (codegen: gen_denote.py). -/

set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_r0 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 4710 =
      ((fw_topk_routing (fw_norm_linear (fw_rms_norm (elemwiseAdd (initSM 4680) (fw_view [4096, 1024] (fw_linear (applyNodeRingAttn_sliding_window sm_goal_3 (((sm_goal_3.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }) (initSM 4699)))) (initSM 4704)) (initSM 4707)) 8 1).snd.fst) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3 initSM 4710 =
      (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4710 := by
    show sm_goal_3.nodes.foldl (applyNodeRingAttn sm_goal_3) initSM 4710 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4710 27 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3.nodes.take 27 = sm_goal_3.nodes.take 26 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 26).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8] } (by decide) (by decide)]
  rw [applyNode_fw_topk_routing_map_out sm_goal_3 (((sm_goal_3.nodes.take 26).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4708 4709 4710 4711 [8] (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4708 26 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4708 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4708 = (fw_norm_linear ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4706) (initSM 4707)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4708 23 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 23 = sm_goal_3.nodes.take 22 ++ [{ rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 22).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] } (by decide) (by decide),
      applyNode_fw_norm_linear_out sm_goal_3 (((sm_goal_3.nodes.take 22).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4706 4707 4708 [],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4706 22 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 22) initSM 4707 (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4706 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4706 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 7415) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4706 19 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 19 = sm_goal_3.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 18).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3 (((sm_goal_3.nodes.take 18).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 7415 4706 [],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 7415 18 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_7415 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 7415 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4705) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 7415 18 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 18 = sm_goal_3.nodes.take 17 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 17).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] } (by decide) (by decide),
      applyNode_fw_multiref5_first_out sm_goal_3 (((sm_goal_3.nodes.take 17).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4705 7415 7419 7423 7427 7431,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4705 17 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4705 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4705 = (fw_rms_norm ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 7404) (initSM 4704)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4705 17 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 17 = sm_goal_3.nodes.take 16 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 16).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p sm_goal_3 (((sm_goal_3.nodes.take 16).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 7404 4704 4705,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 7404 16 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 16) initSM 4704 (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_7404 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 7404 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4703) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 7404 16 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 16 = sm_goal_3.nodes.take 15 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 15).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref2_first_out sm_goal_3 (((sm_goal_3.nodes.take 15).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4703 7404 7408,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4703 15 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4703 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4703 = (elemwiseAdd ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 7387) ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4702)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4703 15 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 15 = sm_goal_3.nodes.take 14 ++ [{ rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 14).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] } (by decide) (by decide),
      applyNode_fw_add2_out sm_goal_3 (((sm_goal_3.nodes.take 14).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 7387 4702 4703,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 7387 14 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide),
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4702 14 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4702 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4702 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4701) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4702 14 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 14 = sm_goal_3.nodes.take 13 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 13).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3 (((sm_goal_3.nodes.take 13).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4701 4702 [],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4701 13 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4701 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4701 = (fw_view [4096, 1024] ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4700)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4701 13 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 13 = sm_goal_3.nodes.take 12 ++ [{ rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 12).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] } (by decide) (by decide),
      applyNode_fw_view_out sm_goal_3 (((sm_goal_3.nodes.take 12).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4096 [1024] 4700 4701,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4700 12 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4700 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4700 = (fw_linear ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4698) (initSM 4699)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4700 12 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 12 = sm_goal_3.nodes.take 11 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 11).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] } (by decide) (by decide),
      applyNode_fw_mix_precision_linear_out_1p sm_goal_3 (((sm_goal_3.nodes.take 11).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4698 4699 4700,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4698 11 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 11) initSM 4699 (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4698 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4698 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4697) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4698 11 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 11 = sm_goal_3.nodes.take 10 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [4697], outs := [4698] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 10).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [4697], outs := [4698] } (by decide) (by decide),
      applyNode_fw_reshape_out sm_goal_3 (((sm_goal_3.nodes.take 10).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4697 4698 [],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4697 10 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4697 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4697 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4696) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4697 10 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 10 = sm_goal_3.nodes.take 9 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [4696], outs := [4697] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 9).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [4696], outs := [4697] } (by decide) (by decide),
      applyNode_fw_reshape_out sm_goal_3 (((sm_goal_3.nodes.take 9).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4696 4697 [],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4696 9 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4696 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4696 = applyNodeRingAttn_sliding_window sm_goal_3 (((sm_goal_3.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] } := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4696 9 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 9 = sm_goal_3.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_sliding_window_out sm_goal_3 (((sm_goal_3.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4692 4693 4689 4694 4695 4696 [16, 4, 64, 64, 1, 512]]
  have hval_7387 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 7387 = ((((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 7387 2 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 2 = sm_goal_3.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref2_second_out sm_goal_3 (((sm_goal_3.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4681 7383 7387 (by decide),
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4681 1 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4681 : (((sm_goal_3.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3) initSM)) 4681 = (initSM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3 sm_goal_3.nodes initSM 4681 1 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3.nodes.take 1 = sm_goal_3.nodes.take 0 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3 (((sm_goal_3.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3 (((sm_goal_3.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3) initSM)) 0 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 0) initSM 4680 (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  rw [hval_4708, hval_4706, hval_7415, hval_4705, hval_7404, hval_4703, hval_4702, hval_4701, hval_4700, hval_4698, hval_4697, hval_4696, hval_7387, hval_4681]
  rfl


/-! ### Phase C1: concrete `ringAttnBuddies` structure lemmas.

    The graphs `sm_goal_3` / `pm_goal_3` are concrete literal node lists, so the
    buddy structure of every `FW_attn_zigzag` node is fully computational. We
    package the fact as a decidable bounded quantifier over the (finite) node
    list and discharge it with `native_decide`. -/

/-- Auxiliary (decidable, computational): every zigzag node in the SM graph is
    its own unique ring-attention buddy. -/
theorem sm_goal_3_zigzag_buddies_singleton_aux :
    ∀ n ∈ sm_goal_3.nodes,
      n.op = "OpName.FW_attn_zigzag" → ringAttnBuddies sm_goal_3 n = [n] := by
  native_decide

/-- For sm_goal_3 (numRanks=1), each FW_attn_zigzag node in the graph is its own
    unique ring-attention buddy (buddies list = [node itself]). -/
theorem sm_goal_3_zigzag_buddies_singleton (n : NodeDecl)
    (hn_mem : n ∈ sm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_zigzag") :
    ringAttnBuddies sm_goal_3 n = [n] :=
  sm_goal_3_zigzag_buddies_singleton_aux n hn_mem hn_op

/-- Auxiliary (decidable, computational): every zigzag node in the PM graph has
    exactly two ring-attention buddies and is a member of its own buddy list. -/
theorem pm_goal_3_zigzag_buddies_pair_aux :
    ∀ n ∈ pm_goal_3.nodes,
      n.op = "OpName.FW_attn_zigzag" →
        (ringAttnBuddies pm_goal_3 n).length = 2
        ∧ n ∈ ringAttnBuddies pm_goal_3 n := by
  native_decide

/-- For pm_goal_3 (numRanks=2), each FW_attn_zigzag node has exactly one other
    buddy (the partner at the matching layer with different rank). The buddies
    list has length 2 and includes n itself. -/
theorem pm_goal_3_zigzag_buddies_pair (n : NodeDecl)
    (hn_mem : n ∈ pm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_zigzag") :
    (ringAttnBuddies pm_goal_3 n).length = 2
    ∧ n ∈ ringAttnBuddies pm_goal_3 n :=
  pm_goal_3_zigzag_buddies_pair_aux n hn_mem hn_op

/-! ### Phase A revised (sliding_window): concrete `ringAttnBuddies` structure.

    The same buddy-structure facts, but for `FW_attn_sliding_window` nodes. These
    feed the sliding-window ring semantics (`applyNodeRingAttn_sliding_window`)
    the way the zigzag lemmas above feed `applyNodeRingAttn_zigzag`. -/

/-- Auxiliary (decidable, computational): every sliding-window node in the SM
    graph is its own unique ring-attention buddy. -/
theorem sm_goal_3_sliding_window_buddies_singleton_aux :
    ∀ n ∈ sm_goal_3.nodes,
      n.op = "OpName.FW_attn_sliding_window" → ringAttnBuddies sm_goal_3 n = [n] := by
  native_decide

/-- For sm_goal_3 (numRanks=1), each FW_attn_sliding_window node in the graph is
    its own unique ring-attention buddy (buddies list = [node itself]). -/
theorem sm_goal_3_sliding_window_buddies_singleton (n : NodeDecl)
    (hn_mem : n ∈ sm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_sliding_window") :
    ringAttnBuddies sm_goal_3 n = [n] :=
  sm_goal_3_sliding_window_buddies_singleton_aux n hn_mem hn_op

/-- Auxiliary (decidable, computational): every sliding-window node in the PM
    graph has exactly two ring-attention buddies and is a member of its own
    buddy list. -/
theorem pm_goal_3_sliding_window_buddies_pair_aux :
    ∀ n ∈ pm_goal_3.nodes,
      n.op = "OpName.FW_attn_sliding_window" →
        (ringAttnBuddies pm_goal_3 n).length = 2
        ∧ n ∈ ringAttnBuddies pm_goal_3 n := by
  native_decide

/-- For pm_goal_3 (numRanks=2), each FW_attn_sliding_window node has exactly one
    other buddy (the partner at the matching layer with different rank). The
    buddies list has length 2 and includes n itself. -/
theorem pm_goal_3_sliding_window_buddies_pair (n : NodeDecl)
    (hn_mem : n ∈ pm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_sliding_window") :
    (ringAttnBuddies pm_goal_3 n).length = 2
    ∧ n ∈ ringAttnBuddies pm_goal_3 n :=
  pm_goal_3_sliding_window_buddies_pair_aux n hn_mem hn_op

/-! ### Phase C2b: ring-attention chunk-gather reconstruction (numShards = 2).

    Core building block for the `FW_attn_zigzag` per-rank commute: gathering the
    two sequence-dim chunks of a `[2*Lshard, d1, d2]` tensor rebuilds it exactly.
    This is the Denote-level statement that `applyNodeRingAttn_zigzag` on a buddy
    *pair* (PM, numRanks=2) reconstructs the full attention output that the
    singleton (SM, numRanks=1) case computes directly:
      `allGather0 [chunk0 fullOut, chunk1 fullOut] = fullOut`. -/

/-- Local copy of the 3D allGather value-at fact (the Denote version is private). -/
private theorem gather0_3d_valAt
    (numParts Lshard d1 d2 : Nat)
    (Ws : List Tensor)
    (hparts : 0 < numParts) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard, d1, d2])
    (r : Nat) (hr : r < numParts)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1)
    (inner : Nat) (hinner : inner < d2) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws)
          (((r * Lshard + row) * d1 + col) * d2 + inner) =
      valAt (Ws.getD r (zeroTensor [Lshard, d1, d2]))
            ((row * d1 + col) * d2 + inner) := by
  have hP_pos : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have hP_ne : d1 * d2 ≠ 0 := Nat.ne_of_gt hP_pos
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * numParts * (d1 * d2) :=
    Nat.mul_pos (Nat.mul_pos hL hparts) hP_pos
  have hE_ne : Lshard * numParts * (d1 * d2) ≠ 0 := Nat.ne_of_gt hE_pos
  have hlow : col * d2 + inner < d1 * d2 := by
    calc col * d2 + inner < col * d2 + d2 := by omega
      _ = (col + 1) * d2 := by ring
      _ ≤ d1 * d2 := Nat.mul_le_mul_right _ (by omega)
  have hrr : r * Lshard + row < Lshard * numParts := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ numParts * Lshard := Nat.mul_le_mul_right _ hr
    calc r * Lshard + row < (r + 1) * Lshard := hsi
      _ ≤ numParts * Lshard := hle
      _ = Lshard * numParts := by ring
  have hidx_eq : ((r * Lshard + row) * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * (r * Lshard + row) := by ring
  have hidx_lt_E : ((r * Lshard + row) * d1 + col) * d2 + inner
      < Lshard * numParts * (d1 * d2) := by
    rw [hidx_eq]
    calc (col * d2 + inner) + (d1 * d2) * (r * Lshard + row)
        < (d1 * d2) + (d1 * d2) * (r * Lshard + row) := by omega
      _ = (d1 * d2) * (r * Lshard + row + 1) := by ring
      _ ≤ (d1 * d2) * (Lshard * numParts) := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * numParts * (d1 * d2) := by ring
  have hdiv_E : (((r * Lshard + row) * d1 + col) * d2 + inner)
      / (Lshard * numParts * (d1 * d2)) = 0 := Nat.div_eq_of_lt hidx_lt_E
  have hmod_E : (((r * Lshard + row) * d1 + col) * d2 + inner)
      % (Lshard * numParts * (d1 * d2))
      = ((r * Lshard + row) * d1 + col) * d2 + inner := Nat.mod_eq_of_lt hidx_lt_E
  have hdiv_P : (((r * Lshard + row) * d1 + col) * d2 + inner) / (d1 * d2)
      = r * Lshard + row := by
    rw [hidx_eq, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmod_P : (((r * Lshard + row) * d1 + col) * d2 + inner) % (d1 * d2)
      = col * d2 + inner := by
    rw [hidx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape
      = [Lshard * numParts, d1, d2] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [Lshard, d1, d2] hhead
    simpa using this
  have hidx_lt_prod : ((r * Lshard + row) * d1 + col) * d2 + inner
      < prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    have hpe : prodShape [Lshard * numParts, d1, d2] = Lshard * numParts * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hpe]; exact hidx_lt_E
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws)
        (((r * Lshard + row) * d1 + col) * d2 + inner)
      = (allGatherPrimDimN 0 numParts 0 Ws).val
          ⟨((r * Lshard + row) * d1 + col) * d2 + inner, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hP_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show 0 * (Lshard * (d1 * d2)) + row * (d1 * d2) + (col * d2 + inner)
        = (row * d1 + col) * d2 + inner from by ring]

/-- Chunk value-at (dim 0, numParts 2): reading local index `(row,col,inner)` of the
    r-th chunk of `T : [2*Lshard, d1, d2]` reads `T` at the full index. -/
private theorem chunk0_3d_valAt
    (Lshard d1 d2 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1, d2])
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1)
    (inner : Nat) (hinner : inner < d2) :
    valAt (chunkPrimDimN 0 2 r T) ((row * d1 + col) * d2 + inner) =
      valAt T (((r * Lshard + row) * d1 + col) * d2 + inner) := by
  have hP_pos : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have hP_ne : d1 * d2 ≠ 0 := Nat.ne_of_gt hP_pos
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hLd_pos : 0 < Lshard * (d1 * d2) := Nat.mul_pos hL hP_pos
  have hLd_ne : Lshard * (d1 * d2) ≠ 0 := Nat.ne_of_gt hLd_pos
  have hlow : col * d2 + inner < d1 * d2 := by
    calc col * d2 + inner < col * d2 + d2 := by omega
      _ = (col + 1) * d2 := by ring
      _ ≤ d1 * d2 := Nat.mul_le_mul_right _ (by omega)
  -- local index in canonical form
  have hloc_eq : (row * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * row := by ring
  have hloc_lt : (row * d1 + col) * d2 + inner < Lshard * (d1 * d2) := by
    rw [hloc_eq]
    calc (col * d2 + inner) + (d1 * d2) * row
        < (d1 * d2) + (d1 * d2) * row := by omega
      _ = (d1 * d2) * (row + 1) := by ring
      _ ≤ (d1 * d2) * Lshard := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * (d1 * d2) := by ring
  have hdiv_S : ((row * d1 + col) * d2 + inner) / (Lshard * (d1 * d2)) = 0 :=
    Nat.div_eq_of_lt hloc_lt
  have hmod_S : ((row * d1 + col) * d2 + inner) % (Lshard * (d1 * d2))
      = (row * d1 + col) * d2 + inner := Nat.mod_eq_of_lt hloc_lt
  have hdiv_P : ((row * d1 + col) * d2 + inner) / (d1 * d2) = row := by
    rw [hloc_eq, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmod_P : ((row * d1 + col) * d2 + inner) % (d1 * d2) = col * d2 + inner := by
    rw [hloc_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  -- chunk shape
  have hchunk_shape : (chunkPrimDimN 0 2 r T).shape = [Lshard, d1, d2] := by
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1, d2] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [hsh]
  have hloc_lt_prod : (row * d1 + col) * d2 + inner
      < prodShape (chunkPrimDimN 0 2 r T).shape := by
    rw [hchunk_shape]
    have hpe : prodShape [Lshard, d1, d2] = Lshard * (d1 * d2) := by simp [prodShape]; ring
    rw [hpe]; exact hloc_lt
  -- T index bound
  have hfull_eq : ((r * Lshard + row) * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * (r * Lshard + row) := by ring
  have hrr : r * Lshard + row < 2 * Lshard := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_lt_of_le hsi hle
  have hfull_lt : ((r * Lshard + row) * d1 + col) * d2 + inner < prodShape T.shape := by
    rw [hT]
    have hpe : prodShape [2 * Lshard, d1, d2] = 2 * Lshard * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hpe, hfull_eq]
    calc (col * d2 + inner) + (d1 * d2) * (r * Lshard + row)
        < (d1 * d2) + (d1 * d2) * (r * Lshard + row) := by omega
      _ = (d1 * d2) * (r * Lshard + row + 1) := by ring
      _ ≤ (d1 * d2) * (2 * Lshard) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Lshard * (d1 * d2) := by ring
  rw [valAt_of_lt _ _ hloc_lt_prod]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hT, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    show ((2:Nat) = 0) = False from by decide, ite_false,
    hsh, hrmod, hP_ne, hLd_ne]
  rw [hmod_S, hdiv_S, hdiv_P, hmod_P]
  congr 1
  ring

/-- Ring-attention reconstruction (numParts = 2, seq dim = 0):
    gathering the two seq-chunks of a `[2*Lshard, d1, d2]` tensor rebuilds it. -/
theorem allGather0_reconstruct_chunks_3d
    (Lshard d1 d2 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1, d2]) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T] = T := by
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hc_shape : ∀ r, (chunkPrimDimN 0 2 r T).shape = [Lshard, d1, d2] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1, d2] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  have hhead : (([chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].head?.map
      (fun t => t.shape)).getD []) = [Lshard, d1, d2] := by simp [hc_shape 0]
  have hgshape : (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T]).shape
      = [2 * Lshard, d1, d2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, d1, d2] hhead]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm Lshard 2]
  apply Tensor.ext
  · rw [hgshape, hT]
  · intro idx hidx
    rw [hgshape] at hidx
    have hprod : prodShape [2 * Lshard, d1, d2] = 2 * Lshard * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hprod] at hidx
    set inner := idx % d2 with hinner_def
    set col := (idx / d2) % d1 with hcol_def
    set fullrow := (idx / d2 / d1) with hfullrow_def
    have hinner : inner < d2 := by rw [hinner_def]; exact Nat.mod_lt _ hd2
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hfullrow_lt : fullrow < 2 * Lshard := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      calc idx < 2 * Lshard * (d1 * d2) := hidx
        _ = d2 * (d1 * (2 * Lshard)) := by ring
    set r := fullrow / Lshard with hr_def
    set row := fullrow % Lshard with hrow_def
    have hrow : row < Lshard := by rw [hrow_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by
      rw [hr_def]
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * Lshard + row := by
      rw [hr_def, hrow_def]; rw [Nat.mul_comm]; exact (Nat.div_add_mod fullrow Lshard).symm
    have hidx_decomp : idx = ((r * Lshard + row) * d1 + col) * d2 + inner := by
      rw [← hfullrow_split]
      rw [hinner_def, hcol_def, hfullrow_def]
      -- idx = ((idx/d2/d1)*d1 + (idx/d2)%d1)*d2 + idx%d2
      have e1 : (idx / d2 / d1) * d1 + (idx / d2) % d1 = idx / d2 := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod (idx / d2) d1
      rw [e1]
      rw [Nat.mul_comm (idx / d2) d2]
      exact (Nat.div_add_mod idx d2).symm
    rw [hidx_decomp]
    rw [gather0_3d_valAt 2 Lshard d1 d2 _ (by omega) hL hd1 hd2 hhead r hr row hrow col hcol inner hinner]
    have hgetD : [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].getD r (zeroTensor [Lshard, d1, d2])
        = chunkPrimDimN 0 2 r T := by
      interval_cases r <;> rfl
    rw [hgetD]
    exact chunk0_3d_valAt Lshard d1 d2 hL hd1 hd2 T hT r hr row hrow col hcol inner hinner


/-! ### Deliverable 1 (routing_map seq-chunk commute): usability of the existing lemma.

    Pattern_3 issues 24 `FW_topk_routing` nodes per rank. Each takes a logits
    tensor sharded on the sequence/token dim (dim 0). The routing_map output
    (`.snd.fst`, shape `[S, numExperts]`) is *row-local*: each token's top-k pick
    depends only on that token's score row (`inTopK` reads a single row `l`).
    Therefore the general shape-`[S, k]` lemma
    `Pattern_1`'s `fw_topk_routing_snd_fst_allGather0_commute_2_of` applies
    **directly** at Pattern_3's per-layer routing input shape — no specialized
    variant is needed. We record a concrete-shape `example` witnessing that the
    existing lemma type-checks at a representative Pattern_3 shape
    (per-rank shard `S = 2048`, `top_k = 8`, `numExperts = 8`). -/

example (a b : Tensor)
    (ha : a.shape = [2048, 8]) (hb : b.shape = [2048, 8]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) 8 8).snd.fst
      = allGatherPrimDimN 0 2 0
          [(fw_topk_routing a 8 8).snd.fst, (fw_topk_routing b 8 8).snd.fst] :=
  fw_topk_routing_snd_fst_allGather0_commute_2_of a b 2048 8 8
    (by norm_num) (by norm_num) ha hb

/-! ### Deliverable 2: per-attention reconstruction primitives.

    These lift a single ring-attention node from SM (numRanks=1, singleton buddy)
    to the buddy *pair* on PM (numRanks=2), showing that the SM full-attention
    output equals the all-gather of the two PM per-rank output shards. This is the
    key per-layer step that lets the 24-layer induction proceed: given the
    previous layer's commute (SM q/k/v = allGather of PM q/k/v shards), the
    attention output commutes with the sequence-dim sharding.

    Structure: SM side collapses to plain `fw_attn_varlen` (singleton lemma); PM
    side reconstructs the full output from the two seq-dim chunks
    (`allGather0_reconstruct_chunks_3d`). The two full outputs coincide by the
    bridge hypotheses. Proved separately for `FW_attn_zigzag` and
    `FW_attn_sliding_window` since the two `applyNodeRingAttn_*` defs, while
    structurally identical, are distinct constants. -/

/-- PM-side buddy-pair unfold for `applyNodeRingAttn_zigzag`: a node whose buddy
    list is `[n0, n1]` computes the seq-dim chunk (index `idx = myIdx`) of the
    full attention over the all-gathered q/k/v shards. -/
theorem applyNodeRingAttn_zigzag_pair_eq_chunk
    (g : GraphDecl) (s : Store) (n n0 n1 : NodeDecl)
    (idx : Nat)
    (hbuddy : ringAttnBuddies g n = [n0, n1])
    (hmyIdx : (([n0, n1].findIdx? (fun m => m.rank = n.rank)).getD 0) = idx) :
    applyNodeRingAttn_zigzag g s n =
      chunkPrimDimN 0 2 idx
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 0 0), s (n1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 1 0), s (n1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 2 0), s (n1.ins.getD 2 0)])
          (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
          (n.params.getD 0 1) (n.params.getD 1 1) (n.params.getD 2 1) (n.params.getD 3 1)
          (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)) := by
  unfold applyNodeRingAttn_zigzag
  rw [hbuddy]
  simp only [List.map, List.length_cons, List.length_nil, hmyIdx]

/-- PM-side buddy-pair unfold for `applyNodeRingAttn_sliding_window` (mirror of
    the zigzag version — identical reconstruction shape). -/
theorem applyNodeRingAttn_sliding_window_pair_eq_chunk
    (g : GraphDecl) (s : Store) (n n0 n1 : NodeDecl)
    (idx : Nat)
    (hbuddy : ringAttnBuddies g n = [n0, n1])
    (hmyIdx : (([n0, n1].findIdx? (fun m => m.rank = n.rank)).getD 0) = idx) :
    applyNodeRingAttn_sliding_window g s n =
      chunkPrimDimN 0 2 idx
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 0 0), s (n1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 1 0), s (n1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 2 0), s (n1.ins.getD 2 0)])
          (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
          (n.params.getD 0 1) (n.params.getD 1 1) (n.params.getD 2 1) (n.params.getD 3 1)
          (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)) := by
  unfold applyNodeRingAttn_sliding_window
  rw [hbuddy]
  simp only [List.map, List.length_cons, List.length_nil, hmyIdx]

/-- **Per-attention reconstruction (zigzag).** Given an SM ring-attention node
    `n_sm` (singleton buddy, numRanks=1) and its PM buddy pair `n_pm_r0`,
    `n_pm_r1` (numRanks=2), together with the bridge hypotheses that SM's q/k/v
    equal the all-gather of PM's q/k/v shards (from the previous layer's commute),
    the shared cu-seqlens, and matching params, the SM ring-attention output
    equals the all-gather of the two PM per-rank ring-attention outputs. -/
theorem applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard qh vd : Nat)
    (hL : 0 < Lshard) (hqh : 0 < qh) (hvd : 0 < vd)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_full : s_sm (n_sm.ins.getD 1 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
    (hv_full : s_sm (n_sm.ins.getD 2 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, qh, vd]) :
    applyNodeRingAttn_zigzag g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_zigzag g_pm s_pm n_pm_r0,
         applyNodeRingAttn_zigzag g_pm s_pm n_pm_r1] := by
  -- SM full-output shape length > 0 (needed for the singleton chunk collapse).
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    rw [hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm, hfull_shape]
    simp
  -- SM side: singleton collapse, then bridge SM inputs into the PM full attention.
  rw [applyNodeRingAttn_zigzag_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  -- PM side: unfold each rank's node to its seq-dim chunk of the full output.
  rw [applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0 hbuddy_pm hmyIdx0,
      applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1 hbuddy_pm' hmyIdx1]
  -- Normalize rank-1's cu-seqlens/params to rank-0's so both chunks share one full output.
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  -- Reconstruct the full output from its two seq-dim chunks.
  rw [allGather0_reconstruct_chunks_3d Lshard qh vd hL hqh hvd _ hfull_shape]

/-- **Per-attention reconstruction (sliding_window).** Mirror of the zigzag
    version for `FW_attn_sliding_window` nodes (identical reconstruction shape;
    the sliding window is a local attention pattern already parameterised by
    `windowLeft`, so gather-then-attend-then-chunk reproduces per-rank shards). -/
theorem applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard qh vd : Nat)
    (hL : 0 < Lshard) (hqh : 0 < qh) (hvd : 0 < vd)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_full : s_sm (n_sm.ins.getD 1 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
    (hv_full : s_sm (n_sm.ins.getD 2 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, qh, vd]) :
    applyNodeRingAttn_sliding_window g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_sliding_window g_pm s_pm n_pm_r0,
         applyNodeRingAttn_sliding_window g_pm s_pm n_pm_r1] := by
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    rw [hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm, hfull_shape]
    simp
  rw [applyNodeRingAttn_sliding_window_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  rw [applyNodeRingAttn_sliding_window_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0
        hbuddy_pm hmyIdx0,
      applyNodeRingAttn_sliding_window_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1
        hbuddy_pm' hmyIdx1]
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  rw [allGather0_reconstruct_chunks_3d Lshard qh vd hL hqh hvd _ hfull_shape]

/-! ### Deliverable 3 (Approach A): value-level per-layer residual-stream commute.

    These lemmas compose the per-op sharding-commute lemmas (from Pattern_1 and
    Phase C2a) into a single **parametric layer-step commute** at the Tensor value
    level.  They witness that one full Pattern_3 layer (structurally identical
    across all 24 layers — only the attention *kind* differs, and both kinds
    reduce to `fw_attn_varlen` at the value level via the ed31485 reconstruction
    primitives) preserves the residual-stream sharding invariant:

      residual_in_full = allGather0 [residual_in_r0, residual_in_r1]
        ⟹ residual_out_full = allGather0 [residual_out_r0, residual_out_r1].

    The layer is split into two residual sub-blocks (attention, MoE), each proven
    separately and then chained.  Everything is at the value level (no graph
    fold), so a single lemma covers both sliding_window and zigzag layers. -/

/-- Local shape helper: `fw_rms_norm` preserves shape. -/
private theorem rms_norm_shape_p3 (x w : Tensor) :
    (fw_rms_norm x w).shape = x.shape := by
  unfold fw_rms_norm
  cases hrev : x.shape.reverse with
  | nil => simp
  | cons d tl => simp [Tensor.mkShape]

/-- Local shape helper: `fw_per_head_linear` output shape `[b, hW, dW]`. -/
private theorem per_head_linear_shape_p3 (b k hW dW : Nat) (x w : Tensor)
    (hx : x.shape = [b, k]) (hw : w.shape = [hW, dW, k]) :
    (fw_per_head_linear x w).shape = [b, hW, dW] := by
  unfold fw_per_head_linear
  rw [hx, hw]
  simp [Tensor.mkShape]

/-- **Input bridge (Q/K path).** The residual-stream shard-gather commutes through
    the pre-attention `rms_norm → per_head_linear → rotary_apply` chain: the full
    (SM) rotary-applied query (or key) equals the all-gather of the two per-rank
    (PM) rotary-applied shards.  Parametric in the number of heads `nh` so it
    serves both Q (`nh = qh`) and K (`nh = kvh`). -/
theorem norm_perhead_rotary_gather_commute
    (r0 r1 wn wp cs pos0 pos1 : Tensor) (Lshard nh dW : Nat)
    (hL : 0 < Lshard) (hnh : 0 < nh) (hdW : 0 < dW)
    (hr0 : r0.shape = [Lshard, 1024]) (hr1 : r1.shape = [Lshard, 1024])
    (hwn : wn.shape = [1024])
    (hwp : wp.shape = [nh, dW, 1024])
    (hpos0 : pos0.shape = [Lshard, 1]) (hpos1 : pos1.shape = [Lshard, 1]) :
    fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
        (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wp) nh
      = allGatherPrimDimN 0 2 0
          [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wp) nh,
           fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wp) nh] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r1 wn).trans hr1
  have hph0 : (fw_per_head_linear (fw_rms_norm r0 wn) wp).shape = [Lshard, nh, dW] :=
    per_head_linear_shape_p3 Lshard 1024 nh dW _ wp hrms0 hwp
  have hph1 : (fw_per_head_linear (fw_rms_norm r1 wn) wp).shape = [Lshard, nh, dW] :=
    per_head_linear_shape_p3 Lshard 1024 nh dW _ wp hrms1 hwp
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn Lshard 1024 hL (by norm_num) hr0 hr1]
  rw [fw_per_head_mix_precision_linear_allGather0_commute_2
        (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wp Lshard 1024 nh dW
        hL (by norm_num) hnh hdW hrms0 hrms1 hwp]
  rw [fw_rotary_apply_allGather0_commute_2
        (fw_per_head_linear (fw_rms_norm r0 wn) wp) (fw_per_head_linear (fw_rms_norm r1 wn) wp)
        pos0 pos1 cs Lshard nh dW hL hnh hdW hph0 hph1 hpos0 hpos1]

/-- **Input bridge (V path).** The value projection `rms_norm → per_head_linear`
    (no rotary) commutes with the residual-stream shard-gather. -/
theorem norm_perhead_gather_commute
    (r0 r1 wn wp : Tensor) (Lshard nh dW : Nat)
    (hL : 0 < Lshard) (hnh : 0 < nh) (hdW : 0 < dW)
    (hr0 : r0.shape = [Lshard, 1024]) (hr1 : r1.shape = [Lshard, 1024])
    (hwn : wn.shape = [1024])
    (hwp : wp.shape = [nh, dW, 1024]) :
    fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wp
      = allGatherPrimDimN 0 2 0
          [fw_per_head_linear (fw_rms_norm r0 wn) wp,
           fw_per_head_linear (fw_rms_norm r1 wn) wp] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r1 wn).trans hr1
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn Lshard 1024 hL (by norm_num) hr0 hr1]
  rw [fw_per_head_mix_precision_linear_allGather0_commute_2
        (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wp Lshard 1024 nh dW
        hL (by norm_num) hnh hdW hrms0 hrms1 hwp]

/-- Local shape helper: `fw_view` yields exactly its target shape. -/
private theorem view_shape_p3 (s : Shape) (x : Tensor) : (fw_view s x).shape = s := by
  unfold fw_view; simp [Tensor.mkShape]

/-- Local value helper: `fw_view` is buffer-preserving on in-bounds indices. -/
private theorem valAt_fw_view (s : Shape) (x : Tensor) (idx : Nat) (h : idx < prodShape s) :
    valAt (fw_view s x) idx = valAt x idx := by
  have hb : idx < prodShape (fw_view s x).shape := by rw [view_shape_p3]; exact h
  rw [valAt_of_lt _ _ hb]
  unfold fw_view; simp [Tensor.mkShape]

/-- **Reshape/flatten bridge.** Flattening the last two dims of a dim-0-gathered
    `[2L, A, B]` tensor to `[2L, A*B]` commutes with the gather: it equals the
    gather of the per-rank `[L, A*B]` flattenings.  This bridges the attention
    output (3-D `[2L, qh, vd]`) into the 2-D input the output projection expects. -/
theorem view_flatten_gather_2 (L A B : Nat) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (c0 c1 : Tensor) (hc0 : c0.shape = [L, A, B]) (hc1 : c1.shape = [L, A, B]) :
    fw_view [2 * L, A * B] (allGatherPrimDimN 0 2 0 [c0, c1])
      = allGatherPrimDimN 0 2 0 [fw_view [L, A * B] c0, fw_view [L, A * B] c1] := by
  have hAB : 0 < A * B := Nat.mul_pos hA hB
  have hhead3 : (([c0, c1].head?.map (fun t => t.shape)).getD []) = [L, A, B] := by simp [hc0]
  have hG3 : (allGatherPrimDimN 0 2 0 [c0, c1]).shape = [2 * L, A, B] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, A, B] hhead3]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm L 2]
  have hv0 : (fw_view [L, A * B] c0).shape = [L, A * B] := view_shape_p3 _ _
  have hv1 : (fw_view [L, A * B] c1).shape = [L, A * B] := view_shape_p3 _ _
  have hheadv : (([fw_view [L, A * B] c0, fw_view [L, A * B] c1].head?.map
      (fun t => t.shape)).getD []) = [L, A * B] := by simp [hv0]
  have hGv : (allGatherPrimDimN 0 2 0 [fw_view [L, A * B] c0, fw_view [L, A * B] c1]).shape
      = [2 * L, A * B] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, A * B] hheadv]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm L 2]
  apply Tensor.ext
  · rw [hGv, view_shape_p3]
  · intro idx hidx
    rw [view_shape_p3] at hidx
    have hprod : prodShape [2 * L, A * B] = 2 * L * (A * B) := by simp [prodShape, Nat.mul_assoc]
    rw [hprod] at hidx
    set inner := idx % B with hinner_def
    set col := (idx / B) % A with hcol_def
    set fullrow := idx / B / A with hfullrow_def
    have hinner : inner < B := by rw [hinner_def]; exact Nat.mod_lt _ hB
    have hcol : col < A := by rw [hcol_def]; exact Nat.mod_lt _ hA
    have hfullrow_lt : fullrow < 2 * L := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul; apply Nat.div_lt_of_lt_mul
      calc idx < 2 * L * (A * B) := hidx
        _ = B * (A * (2 * L)) := by ring
    set r := fullrow / L with hr_def
    set i := fullrow % L with hi_def
    have hi : i < L := by rw [hi_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by rw [hr_def]; apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * L + i := by
      rw [hr_def, hi_def, Nat.mul_comm]; exact (Nat.div_add_mod fullrow L).symm
    set j := col * B + inner with hj_def
    have hj_lt : j < A * B := by
      rw [hj_def]
      calc col * B + inner < col * B + B := by omega
        _ = (col + 1) * B := by ring
        _ ≤ A * B := Nat.mul_le_mul_right _ (by omega)
    have hidx_3d : idx = ((r * L + i) * A + col) * B + inner := by
      rw [← hfullrow_split, hinner_def, hcol_def, hfullrow_def]
      have e1 : (idx / B / A) * A + (idx / B) % A = idx / B := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod (idx / B) A
      rw [e1, Nat.mul_comm (idx / B) B]; exact (Nat.div_add_mod idx B).symm
    have hidx_2d : idx = (r * L + i) * (A * B) + j := by
      rw [hidx_3d, hj_def]; ring
    have hLval : valAt (fw_view [2 * L, A * B] (allGatherPrimDimN 0 2 0 [c0, c1])) idx
        = valAt ([c0, c1].getD r (zeroTensor [L, A, B])) ((i * A + col) * B + inner) := by
      rw [valAt_fw_view _ _ _ (by rw [hprod]; exact hidx)]
      rw [hidx_3d]
      exact gather0_3d_valAt 2 L A B _ (by omega) hL hA hB hhead3 r hr i hi col hcol inner hinner
    have hRval : valAt (allGatherPrimDimN 0 2 0 [fw_view [L, A * B] c0, fw_view [L, A * B] c1]) idx
        = valAt ([fw_view [L, A * B] c0, fw_view [L, A * B] c1].getD r (zeroTensor [L, A * B]))
            (i * (A * B) + j) := by
      rw [hidx_2d]
      exact allGatherPrimDimN0_valAt 2 L (A * B) _ (by omega) hL hAB hheadv
          (by intro r' hr'; interval_cases r' <;> simp [List.getD, hv0, hv1]) r hr i hi j hj_lt
    rw [hLval, hRval]
    have hgetD3 : [c0, c1].getD r (zeroTensor [L, A, B]) = if r = 0 then c0 else c1 := by
      interval_cases r <;> rfl
    have hgetDv : [fw_view [L, A * B] c0, fw_view [L, A * B] c1].getD r (zeroTensor [L, A * B])
        = if r = 0 then fw_view [L, A * B] c0 else fw_view [L, A * B] c1 := by
      interval_cases r <;> rfl
    rw [hgetD3, hgetDv]
    have hlocal_eq : (i * A + col) * B + inner = i * (A * B) + j := by rw [hj_def]; ring
    rw [hlocal_eq]
    have hview_val : ∀ c : Tensor,
        valAt (fw_view [L, A * B] c) (i * (A * B) + j) = valAt c (i * (A * B) + j) := by
      intro c
      apply valAt_fw_view
      have hp : prodShape [L, A * B] = L * (A * B) := by simp [prodShape, Nat.mul_assoc]
      rw [hp]
      calc i * (A * B) + j < i * (A * B) + A * B := by omega
        _ = (i + 1) * (A * B) := by ring
        _ ≤ L * (A * B) := Nat.mul_le_mul_right _ (by omega)
    clear_value r
    rcases (by omega : r = 0 ∨ r = 1) with hr0' | hr1'
    · simp only [hr0', if_true]; rw [hview_val c0]
    · simp only [hr1', if_false, Nat.one_ne_zero]; rw [hview_val c1]

/-- Local shape helper: 2-D `fw_linear` output shape `[b, o]`. -/
private theorem linear_shape_p3 (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  unfold fw_linear; rw [hx, hw]; simp [Tensor.mkShape]

/-- **Reshape/flatten bridge (chunk form).** Flattening `[2L, A, B] → [2L, A*B]` of
    a tensor `T` equals the dim-0 gather of the per-rank flattened seq-chunks of
    `T`.  Direct corollary of `view_flatten_gather_2` composed with the chunk
    reconstruction (`allGather0_reconstruct_chunks_3d`). -/
theorem view_flatten_chunks (L A B : Nat) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (T : Tensor) (hT : T.shape = [2 * L, A, B]) :
    fw_view [2 * L, A * B] T
      = allGatherPrimDimN 0 2 0
          [fw_view [L, A * B] (chunkPrimDimN 0 2 0 T),
           fw_view [L, A * B] (chunkPrimDimN 0 2 1 T)] := by
  have hchunk : ∀ r, (chunkPrimDimN 0 2 r T).shape = [L, A, B] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * L, A, B] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [show 2 * L / 2 = L from by omega]
  rw [show fw_view [2 * L, A * B] T
        = fw_view [2 * L, A * B]
            (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T])
      from by rw [allGather0_reconstruct_chunks_3d L A B hL hA hB T hT]]
  exact view_flatten_gather_2 L A B hL hA hB
    (chunkPrimDimN 0 2 0 T) (chunkPrimDimN 0 2 1 T) (hchunk 0) (hchunk 1)

/-- **Output bridge (attention).** The post-attention output projection and
    residual add commute with the residual-stream shard-gather: given the full
    attention output `af : [4096, qh, vd]` (whose per-rank ring shards are its two
    seq-chunks), the full residual output equals the dim-0 gather of the two
    per-rank residual outputs.  Chains `view_flatten_chunks`,
    `fw_mix_precision_linear_allGather0_commute_2`, and the `[2048,1024]` residual
    add commute. -/
theorem attn_output_residual_commute
    (r0 r1 wo af : Tensor) (qh vd : Nat)
    (hqh : 0 < qh) (hvd : 0 < vd)
    (hr0 : r0.shape = [2048, 1024]) (hr1 : r1.shape = [2048, 1024])
    (hwo : wo.shape = [1024, qh * vd])
    (haf : af.shape = [2 * 2048, qh, vd]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd] af) wo)
      = allGatherPrimDimN 0 2 0
          [elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)) wo),
           elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo)] := by
  have hqhvd : 0 < qh * vd := Nat.mul_pos hqh hvd
  have hv0 : (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)).shape = [2048, qh * vd] :=
    view_shape_p3 _ _
  have hv1 : (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)).shape = [2048, qh * vd] :=
    view_shape_p3 _ _
  have hproj0 : (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)) wo).shape
      = [2048, 1024] := linear_shape_p3 2048 (qh * vd) 1024 _ wo hv0 hwo
  have hproj1 : (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo).shape
      = [2048, 1024] := linear_shape_p3 2048 (qh * vd) 1024 _ wo hv1 hwo
  rw [view_flatten_chunks 2048 qh vd (by norm_num) hqh hvd af haf]
  rw [fw_mix_precision_linear_allGather0_commute_2
        (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af))
        (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo
        2048 (qh * vd) 1024 (by norm_num) hqhvd (by norm_num) hv0 hv1 hwo]
  rw [fw_add_allGather0_commute_2_2048_1024 r0 r1
        (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)) wo)
        (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo)
        hr0 hr1 hproj0 hproj1]

/-- **Layer attention sub-block residual commute (Approach A, value level).**

    Ties the input bridges (`norm_perhead_rotary_gather_commute` for Q/K,
    `norm_perhead_gather_commute` for V) to the output bridge
    (`attn_output_residual_commute`).  The left-hand side is the SM (full,
    numRanks=1) attention sub-block computed over the gathered residual stream;
    the right-hand side is the dim-0 gather of the two PM (numRanks=2) per-rank
    sub-blocks, whose ring-attention output shard is the corresponding seq-chunk
    of the full attention.  Covers both sliding_window and zigzag layers (both
    reduce to `fw_attn_varlen`).  `qh * vd = 1024` is the model dimension. -/
theorem layer_attn_block_commute
    (r0 r1 wn wq wk wv cs pos0 pos1 wo cuQ cuK : Tensor)
    (qh kh d vd : Nat) (causal : Bool) (windowLeft : Nat)
    (hqh : 0 < qh) (hkh : 0 < kh) (hd : 0 < d) (hvd : 0 < vd)
    (hr0 : r0.shape = [2048, 1024]) (hr1 : r1.shape = [2048, 1024])
    (hwn : wn.shape = [1024])
    (hwq : wq.shape = [qh, d, 1024]) (hwk : wk.shape = [kh, d, 1024])
    (hwv : wv.shape = [kh, vd, 1024])
    (hpos0 : pos0.shape = [2048, 1]) (hpos1 : pos1.shape = [2048, 1])
    (hwo : wo.shape = [1024, qh * vd])
    (haf : (fw_attn_varlen
              (allGatherPrimDimN 0 2 0
                 [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wq) qh,
                  fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wq) qh])
              (allGatherPrimDimN 0 2 0
                 [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wk) kh,
                  fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wk) kh])
              (allGatherPrimDimN 0 2 0
                 [fw_per_head_linear (fw_rms_norm r0 wn) wv,
                  fw_per_head_linear (fw_rms_norm r1 wn) wv])
              cuQ cuK qh kh d vd causal windowLeft).shape = [2 * 2048, qh, vd]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wv)
            cuQ cuK qh kh d vd causal windowLeft)) wo)
      = allGatherPrimDimN 0 2 0
          [elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0
              (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn) wv,
                    fw_per_head_linear (fw_rms_norm r1 wn) wv])
                cuQ cuK qh kh d vd causal windowLeft))) wo),
           elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1
              (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn) wv,
                    fw_per_head_linear (fw_rms_norm r1 wn) wv])
                cuQ cuK qh kh d vd causal windowLeft))) wo)] := by
  rw [norm_perhead_rotary_gather_commute r0 r1 wn wq cs pos0 pos1 2048 qh d
        (by norm_num) hqh hd hr0 hr1 hwn hwq hpos0 hpos1]
  rw [norm_perhead_rotary_gather_commute r0 r1 wn wk cs pos0 pos1 2048 kh d
        (by norm_num) hkh hd hr0 hr1 hwn hwk hpos0 hpos1]
  rw [norm_perhead_gather_commute r0 r1 wn wv 2048 kh vd
        (by norm_num) hkh hvd hr0 hr1 hwn hwv]
  exact attn_output_residual_commute r0 r1 wo _ qh vd hqh hvd hr0 hr1 hwo haf

/-- Local shape helper: broadcast `[2048,1] * [2048,1024]` has shape `[2048,1024]`. -/
private theorem mul_broadcast_shape_p3 (x y : Tensor)
    (hx : x.shape = [2048, 1]) (hy : y.shape = [2048, 1024]) :
    (elemwiseMul x y).shape = [2048, 1024] := by
  unfold elemwiseMul Tensor.mkShape
  change outShape2 x y = [2048, 1024]
  simp [outShape2, hx, hy]

/-- **MoE combine tail residual commute.** The MoE sub-block's combine tail
    (`gate ⊙ swiglu_proj`, add MoE-GMM output, add residual carry) commutes with
    the residual-stream shard-gather, given that the MoE-GMM output, swiglu
    projection, gate, and residual carry already commute (each equals the dim-0
    gather of its two per-rank shards).  Chains the broadcast-mul commute and two
    `[2048,1024]` add commutes.  Together with the attention sub-block, this
    completes the algebraic residual invariant modulo the per-rank MoE-GMM /
    swiglu / router commutes (which reduce to Pattern_1's proven op lemmas). -/
theorem moe_combine_tail_commute
    (carry0 carry1 moe0 moe1 gate0 gate1 sw0 sw1 : Tensor)
    (hc0 : carry0.shape = [2048, 1024]) (hc1 : carry1.shape = [2048, 1024])
    (hmoe0 : moe0.shape = [2048, 1024]) (hmoe1 : moe1.shape = [2048, 1024])
    (hg0 : gate0.shape = [2048, 1]) (hg1 : gate1.shape = [2048, 1])
    (hsw0 : sw0.shape = [2048, 1024]) (hsw1 : sw1.shape = [2048, 1024]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [carry0, carry1])
        (elemwiseAdd (allGatherPrimDimN 0 2 0 [moe0, moe1])
          (elemwiseMul (allGatherPrimDimN 0 2 0 [gate0, gate1])
                       (allGatherPrimDimN 0 2 0 [sw0, sw1])))
      = allGatherPrimDimN 0 2 0
          [elemwiseAdd carry0 (elemwiseAdd moe0 (elemwiseMul gate0 sw0)),
           elemwiseAdd carry1 (elemwiseAdd moe1 (elemwiseMul gate1 sw1))] := by
  have hmul0 : (elemwiseMul gate0 sw0).shape = [2048, 1024] := mul_broadcast_shape_p3 _ _ hg0 hsw0
  have hmul1 : (elemwiseMul gate1 sw1).shape = [2048, 1024] := mul_broadcast_shape_p3 _ _ hg1 hsw1
  have hadd0 : (elemwiseAdd moe0 (elemwiseMul gate0 sw0)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ _ hmoe0 hmul0
  have hadd1 : (elemwiseAdd moe1 (elemwiseMul gate1 sw1)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ _ hmoe1 hmul1
  rw [fw_mul_allGather0_commute_2_of_broadcast gate0 gate1 sw0 sw1 2048 1024
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hg0 hg1 hsw0 hsw1]
  rw [fw_add_allGather0_commute_2_2048_1024 moe0 moe1
        (elemwiseMul gate0 sw0) (elemwiseMul gate1 sw1) hmoe0 hmoe1 hmul0 hmul1]
  rw [fw_add_allGather0_commute_2_2048_1024 carry0 carry1
        (elemwiseAdd moe0 (elemwiseMul gate0 sw0)) (elemwiseAdd moe1 (elemwiseMul gate1 sw1))
        hc0 hc1 hadd0 hadd1]

/-- Local shape helper: 2-D `fw_norm_linear` output shape `[b, n]` (`w : [n, k]`). -/
private theorem norm_linear_shape_p3 (b k n : Nat) (x w : Tensor)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    (fw_norm_linear x w).shape = [b, n] := by
  unfold fw_norm_linear; rw [hx, hw]; simp [Tensor.mkShape]

/-- Local shape helper: `fw_topk_routing` routing-probs (`.fst`) has shape
    `[S, numExp]` when the logits have shape `[S, numExp]`. -/
private theorem topk_fst_shape_p3 (x : Tensor) (S topK numExp : Nat)
    (hx : x.shape = [S, numExp]) :
    (fw_topk_routing x topK numExp).fst.shape = [S, numExp] := by
  unfold fw_topk_routing; simp [Tensor.mkShape]; rw [hx]; rfl

/-- Local shape helper: `fw_topk_routing` routing-map (`.snd.fst`) has shape
    `[S, numExp]` when the logits have shape `[S, numExp]`. -/
private theorem topk_snd_fst_shape_p3 (x : Tensor) (S topK numExp : Nat)
    (hx : x.shape = [S, numExp]) :
    (fw_topk_routing x topK numExp).snd.fst.shape = [S, numExp] := by
  unfold fw_topk_routing; simp [Tensor.mkShape]; rw [hx]; rfl

/-- **MoE-GMM path residual commute.**  The MoE sub-block's expert-FFN branch —
    routing logits (`rms_norm → norm_linear`, `FW_float` being identity),
    top-k routing (scores `.fst` and map `.snd.fst`), and the fused all-to-all
    grouped-MM expert layer on the normed activation — commutes with the
    residual-stream shard-gather: the full (SM, numRanks=1) MoE-GMM output over
    the gathered residual equals the dim-0 gather of the two per-rank
    (PM, numRanks=2) MoE-GMM outputs, with `w13 / w2` expert weights replicated
    across ranks.  Chains Pattern_1's proven `fw_rms_norm`, `fw_norm_linear`,
    `fw_topk_routing_fst` / `_snd_fst`, and `fw_all2all_moe_gmm_full_split`
    sharding-commutes (`dModel` = model dim, `E_shard * 2` = total experts). -/
theorem moe_gmm_output_commute
    (r0 r1 wn wr w13a w13b w2a w2b : Tensor)
    (L dModel E_shard topK t_dim d_dim : Nat) (swigluLimit : Scalar)
    (hL : 0 < L) (hdM : 0 < dModel) (hE : 0 < E_shard) (ht : 0 < t_dim) (hd : 0 < d_dim)
    (ht_even : t_dim = 2 * d_dim)
    (hr0 : r0.shape = [L, dModel]) (hr1 : r1.shape = [L, dModel])
    (hwr : wr.shape = [E_shard * 2, dModel])
    (hw13a : w13a.shape = [E_shard, t_dim, dModel]) (hw13b : w13b.shape = [E_shard, t_dim, dModel])
    (hw2a : w2a.shape = [E_shard, dModel, d_dim]) (hw2b : w2b.shape = [E_shard, dModel, d_dim]) :
    fw_all2all_moe_gmm_full
        (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn)
        ((fw_topk_routing
            (fw_norm_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wr)
            topK (E_shard * 2)).fst)
        ((fw_topk_routing
            (fw_norm_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wr)
            topK (E_shard * 2)).snd.fst)
        [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit
      = allGatherPrimDimN 0 2 0
          [fw_all2all_moe_gmm_full (fw_rms_norm r0 wn)
              ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).fst)
              ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).snd.fst)
              [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit,
           fw_all2all_moe_gmm_full (fw_rms_norm r1 wn)
              ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).fst)
              ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).snd.fst)
              [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [L, dModel] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [L, dModel] := (rms_norm_shape_p3 r1 wn).trans hr1
  have hlog0 : (fw_norm_linear (fw_rms_norm r0 wn) wr).shape = [L, E_shard * 2] :=
    norm_linear_shape_p3 L dModel (E_shard * 2) _ wr hrms0 hwr
  have hlog1 : (fw_norm_linear (fw_rms_norm r1 wn) wr).shape = [L, E_shard * 2] :=
    norm_linear_shape_p3 L dModel (E_shard * 2) _ wr hrms1 hwr
  have hsc0 : (fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).fst.shape
      = [L, E_shard * 2] := topk_fst_shape_p3 _ L topK (E_shard * 2) hlog0
  have hsc1 : (fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).fst.shape
      = [L, E_shard * 2] := topk_fst_shape_p3 _ L topK (E_shard * 2) hlog1
  have hmap0 : (fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).snd.fst.shape
      = [L, E_shard * 2] := topk_snd_fst_shape_p3 _ L topK (E_shard * 2) hlog0
  have hmap1 : (fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).snd.fst.shape
      = [L, E_shard * 2] := topk_snd_fst_shape_p3 _ L topK (E_shard * 2) hlog1
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn L dModel hL hdM hr0 hr1]
  rw [fw_norm_linear_allGather0_commute_2 (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wr
        L dModel (E_shard * 2) hL hdM (by omega) hrms0 hrms1 hwr]
  rw [fw_topk_routing_fst_allGather0_commute_2_of
        (fw_norm_linear (fw_rms_norm r0 wn) wr) (fw_norm_linear (fw_rms_norm r1 wn) wr)
        L topK (E_shard * 2) hL (by omega) hlog0 hlog1]
  rw [fw_topk_routing_snd_fst_allGather0_commute_2_of
        (fw_norm_linear (fw_rms_norm r0 wn) wr) (fw_norm_linear (fw_rms_norm r1 wn) wr)
        L topK (E_shard * 2) hL (by omega) hlog0 hlog1]
  exact fw_all2all_moe_gmm_full_split_commute_2
    (fw_rms_norm r0 wn) (fw_rms_norm r1 wn)
    ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).fst)
    ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).fst)
    ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).snd.fst)
    ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).snd.fst)
    w13a w13b w2a w2b
    L dModel E_shard topK t_dim d_dim swigluLimit
    hL hdM hE ht hd ht_even hrms0 hrms1 hsc0 hsc1 hmap0 hmap1 hw13a hw13b hw2a hw2b

/-- Local shape helper: `fw_swiglu g u` inherits the `up` argument's shape `[b, h]`. -/
private theorem swiglu_shape_p3 (g u : Tensor) (b h : Nat) (hu : u.shape = [b, h]) :
    (fw_swiglu g u).shape = [b, h] := by
  unfold fw_swiglu Tensor.mkShape; simp; exact hu

/-- **MoE gate path residual commute.**  The sigmoid gate branch
    (`rms_norm → mix_precision_linear → view → sigmoid`, `FW_reshape` being
    identity) commutes with the residual-stream shard-gather.  The gate weight
    `wg : [1, dModel]` projects each token to a scalar gate.  Chains
    `fw_rms_norm`, `fw_mix_precision_linear`, `fw_view`, `fw_sigmoid`
    sharding-commutes. -/
theorem moe_gate_path_commute
    (r0 r1 wn wg : Tensor) (L dModel : Nat)
    (hL : 0 < L) (hdM : 0 < dModel)
    (hr0 : r0.shape = [L, dModel]) (hr1 : r1.shape = [L, dModel])
    (hwg : wg.shape = [1, dModel]) :
    fw_sigmoid (fw_view [L * 2, 1]
        (fw_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wg))
      = allGatherPrimDimN 0 2 0
          [fw_sigmoid (fw_view [L, 1] (fw_linear (fw_rms_norm r0 wn) wg)),
           fw_sigmoid (fw_view [L, 1] (fw_linear (fw_rms_norm r1 wn) wg))] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [L, dModel] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [L, dModel] := (rms_norm_shape_p3 r1 wn).trans hr1
  have hlin0 : (fw_linear (fw_rms_norm r0 wn) wg).shape = [L, 1] :=
    linear_shape_p3 L dModel 1 _ wg hrms0 hwg
  have hlin1 : (fw_linear (fw_rms_norm r1 wn) wg).shape = [L, 1] :=
    linear_shape_p3 L dModel 1 _ wg hrms1 hwg
  have hview0 : (fw_view [L, 1] (fw_linear (fw_rms_norm r0 wn) wg)).shape = [L, 1] :=
    view_shape_p3 _ _
  have hview1 : (fw_view [L, 1] (fw_linear (fw_rms_norm r1 wn) wg)).shape = [L, 1] :=
    view_shape_p3 _ _
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn L dModel hL hdM hr0 hr1]
  rw [fw_mix_precision_linear_allGather0_commute_2 (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wg
        L dModel 1 hL hdM (by norm_num) hrms0 hrms1 hwg]
  rw [fw_view_allGather0_commute_2_of
        (fw_linear (fw_rms_norm r0 wn) wg) (fw_linear (fw_rms_norm r1 wn) wg) L 1 hL hlin0 hlin1]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [L, 1] (fw_linear (fw_rms_norm r0 wn) wg))
        (fw_view [L, 1] (fw_linear (fw_rms_norm r1 wn) wg)) L 1 hL (by norm_num) hview0 hview1]

/-- **MoE SwiGLU-projection path residual commute.**  The SwiGLU FFN branch
    feeding the gate multiply (`rms_norm → up/gate mix_precision_linear → view →
    swiglu → down mix_precision_linear → view`, `FW_reshape` being identity)
    commutes with the residual-stream shard-gather.  `wu, wv : [dInner, dModel]`
    are the up/gate projections and `wd : [dModel, dInner]` the down projection.
    Chains `fw_rms_norm`, `fw_mix_precision_linear`, `fw_view`, `fw_swiglu`
    sharding-commutes. -/
theorem moe_swiglu_path_commute
    (r0 r1 wn wu wv wd : Tensor) (L dModel dInner : Nat)
    (hL : 0 < L) (hdM : 0 < dModel) (hdI : 0 < dInner)
    (hr0 : r0.shape = [L, dModel]) (hr1 : r1.shape = [L, dModel])
    (hwu : wu.shape = [dInner, dModel]) (hwv : wv.shape = [dInner, dModel])
    (hwd : wd.shape = [dModel, dInner]) :
    fw_view [L * 2, dModel]
        (fw_linear (fw_swiglu
          (fw_view [L * 2, dInner]
            (fw_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wu))
          (fw_view [L * 2, dInner]
            (fw_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wv))) wd)
      = allGatherPrimDimN 0 2 0
          [fw_view [L, dModel] (fw_linear (fw_swiglu
              (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
              (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv))) wd),
           fw_view [L, dModel] (fw_linear (fw_swiglu
              (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
              (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv))) wd)] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [L, dModel] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [L, dModel] := (rms_norm_shape_p3 r1 wn).trans hr1
  have hlinu0 : (fw_linear (fw_rms_norm r0 wn) wu).shape = [L, dInner] :=
    linear_shape_p3 L dModel dInner _ wu hrms0 hwu
  have hlinu1 : (fw_linear (fw_rms_norm r1 wn) wu).shape = [L, dInner] :=
    linear_shape_p3 L dModel dInner _ wu hrms1 hwu
  have hlinv0 : (fw_linear (fw_rms_norm r0 wn) wv).shape = [L, dInner] :=
    linear_shape_p3 L dModel dInner _ wv hrms0 hwv
  have hlinv1 : (fw_linear (fw_rms_norm r1 wn) wv).shape = [L, dInner] :=
    linear_shape_p3 L dModel dInner _ wv hrms1 hwv
  have hvu0 : (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu)).shape = [L, dInner] :=
    view_shape_p3 _ _
  have hvu1 : (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu)).shape = [L, dInner] :=
    view_shape_p3 _ _
  have hvv0 : (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv)).shape = [L, dInner] :=
    view_shape_p3 _ _
  have hvv1 : (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv)).shape = [L, dInner] :=
    view_shape_p3 _ _
  have hsw0 : (fw_swiglu (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
                (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv))).shape = [L, dInner] :=
    swiglu_shape_p3 _ _ L dInner hvv0
  have hsw1 : (fw_swiglu (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
                (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv))).shape = [L, dInner] :=
    swiglu_shape_p3 _ _ L dInner hvv1
  have hproj0 : (fw_linear (fw_swiglu
      (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
      (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv))) wd).shape = [L, dModel] :=
    linear_shape_p3 L dInner dModel _ wd hsw0 hwd
  have hproj1 : (fw_linear (fw_swiglu
      (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
      (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv))) wd).shape = [L, dModel] :=
    linear_shape_p3 L dInner dModel _ wd hsw1 hwd
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn L dModel hL hdM hr0 hr1]
  rw [fw_mix_precision_linear_allGather0_commute_2 (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wu
        L dModel dInner hL hdM hdI hrms0 hrms1 hwu]
  rw [fw_mix_precision_linear_allGather0_commute_2 (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wv
        L dModel dInner hL hdM hdI hrms0 hrms1 hwv]
  rw [fw_view_allGather0_commute_2_of
        (fw_linear (fw_rms_norm r0 wn) wu) (fw_linear (fw_rms_norm r1 wn) wu) L dInner hL hlinu0 hlinu1]
  rw [fw_view_allGather0_commute_2_of
        (fw_linear (fw_rms_norm r0 wn) wv) (fw_linear (fw_rms_norm r1 wn) wv) L dInner hL hlinv0 hlinv1]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
        (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
        (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv))
        (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv))
        L dInner hL hdI hvu0 hvu1 hvv0 hvv1]
  rw [fw_mix_precision_linear_allGather0_commute_2
        (fw_swiglu (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
          (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv)))
        (fw_swiglu (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
          (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv)))
        wd L dInner dModel hL hdI hdM hsw0 hsw1 hwd]
  rw [fw_view_allGather0_commute_2_of
        (fw_linear (fw_swiglu (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
          (fw_view [L, dInner] (fw_linear (fw_rms_norm r0 wn) wv))) wd)
        (fw_linear (fw_swiglu (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
          (fw_view [L, dInner] (fw_linear (fw_rms_norm r1 wn) wv))) wd)
        L dModel hL hproj0 hproj1]

/-- **Full MoE sub-block residual commute (Approach A, value level).**

    Ties the three residual-commuting branches of a layer's MoE sub-block —
    the expert-FFN (`moe_gmm_output_commute`), the sigmoid gate
    (`moe_gate_path_commute`), and the SwiGLU projection
    (`moe_swiglu_path_commute`) — to the combine tail (`moe_combine_tail_commute`,
    from `405ddf6`).  The left-hand side is the SM (full, numRanks=1) MoE
    sub-block computed over the gathered residual stream `r_L`; the right-hand
    side is the dim-0 gather of the two PM (numRanks=2) per-rank sub-blocks
    (`FW_float` / `FW_reshape` being identities in the model).  `dModel = 1024`
    is the model dim, `E_shard * 2` the total experts, `dInner` the SwiGLU inner
    width.  Together with `layer_attn_block_commute` this completes the algebraic
    per-layer residual invariant. -/
theorem layer_moe_block_commute
    (r0 r1 wn wr wg wu wv wd w13a w13b w2a w2b : Tensor)
    (E_shard topK t_dim d_dim dInner : Nat) (swigluLimit : Scalar)
    (hE : 0 < E_shard) (ht : 0 < t_dim) (hd : 0 < d_dim) (hdI : 0 < dInner)
    (ht_even : t_dim = 2 * d_dim)
    (hr0 : r0.shape = [2048, 1024]) (hr1 : r1.shape = [2048, 1024])
    (hwr : wr.shape = [E_shard * 2, 1024]) (hwg : wg.shape = [1, 1024])
    (hwu : wu.shape = [dInner, 1024]) (hwv : wv.shape = [dInner, 1024])
    (hwd : wd.shape = [1024, dInner])
    (hw13a : w13a.shape = [E_shard, t_dim, 1024]) (hw13b : w13b.shape = [E_shard, t_dim, 1024])
    (hw2a : w2a.shape = [E_shard, 1024, d_dim]) (hw2b : w2b.shape = [E_shard, 1024, d_dim]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (elemwiseAdd
          (fw_all2all_moe_gmm_full
            (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wr)
                topK (E_shard * 2)).fst)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wr)
                topK (E_shard * 2)).snd.fst)
            [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit)
          (elemwiseMul
            (fw_sigmoid (fw_view [2048 * 2, 1]
              (fw_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wg)))
            (fw_view [2048 * 2, 1024]
              (fw_linear (fw_swiglu
                (fw_view [2048 * 2, dInner]
                  (fw_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wu))
                (fw_view [2048 * 2, dInner]
                  (fw_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wv))) wd))))
      = allGatherPrimDimN 0 2 0
          [elemwiseAdd r0
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (fw_rms_norm r0 wn)
                ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).fst)
                ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).snd.fst)
                [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit)
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_rms_norm r0 wn) wg)))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu
                  (fw_view [2048, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
                  (fw_view [2048, dInner] (fw_linear (fw_rms_norm r0 wn) wv))) wd)))),
           elemwiseAdd r1
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (fw_rms_norm r1 wn)
                ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).fst)
                ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).snd.fst)
                [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit)
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_rms_norm r1 wn) wg)))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu
                  (fw_view [2048, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
                  (fw_view [2048, dInner] (fw_linear (fw_rms_norm r1 wn) wv))) wd))))] := by
  rw [moe_gmm_output_commute r0 r1 wn wr w13a w13b w2a w2b
        2048 1024 E_shard topK t_dim d_dim swigluLimit
        (by norm_num) (by norm_num) hE ht hd ht_even hr0 hr1 hwr hw13a hw13b hw2a hw2b]
  rw [moe_gate_path_commute r0 r1 wn wg 2048 1024 (by norm_num) (by norm_num) hr0 hr1 hwg]
  rw [moe_swiglu_path_commute r0 r1 wn wu wv wd 2048 1024 dInner
        (by norm_num) (by norm_num) hdI hr0 hr1 hwu hwv hwd]
  -- Per-rank branch-output shapes for the combine tail.
  have hrms0 : (fw_rms_norm r0 wn).shape = [2048, 1024] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [2048, 1024] := (rms_norm_shape_p3 r1 wn).trans hr1
  have hmoe0 : (fw_all2all_moe_gmm_full (fw_rms_norm r0 wn)
      ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).fst)
      ((fw_topk_routing (fw_norm_linear (fw_rms_norm r0 wn) wr) topK (E_shard * 2)).snd.fst)
      [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit).shape = [2048, 1024] :=
    fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hrms0]; rfl) (by rw [hrms0]; rfl)
  have hmoe1 : (fw_all2all_moe_gmm_full (fw_rms_norm r1 wn)
      ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).fst)
      ((fw_topk_routing (fw_norm_linear (fw_rms_norm r1 wn) wr) topK (E_shard * 2)).snd.fst)
      [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit).shape = [2048, 1024] :=
    fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hrms1]; rfl) (by rw [hrms1]; rfl)
  have hgate0 : (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_rms_norm r0 wn) wg))).shape = [2048, 1] := by
    unfold fw_sigmoid Tensor.mkShape; simp [view_shape_p3]
  have hgate1 : (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_rms_norm r1 wn) wg))).shape = [2048, 1] := by
    unfold fw_sigmoid Tensor.mkShape; simp [view_shape_p3]
  have hswp0 : (fw_view [2048, 1024] (fw_linear (fw_swiglu
      (fw_view [2048, dInner] (fw_linear (fw_rms_norm r0 wn) wu))
      (fw_view [2048, dInner] (fw_linear (fw_rms_norm r0 wn) wv))) wd)).shape = [2048, 1024] :=
    view_shape_p3 _ _
  have hswp1 : (fw_view [2048, 1024] (fw_linear (fw_swiglu
      (fw_view [2048, dInner] (fw_linear (fw_rms_norm r1 wn) wu))
      (fw_view [2048, dInner] (fw_linear (fw_rms_norm r1 wn) wv))) wd)).shape = [2048, 1024] :=
    view_shape_p3 _ _
  exact moe_combine_tail_commute r0 r1 _ _ _ _ _ _
    hr0 hr1 hmoe0 hmoe1 hgate0 hgate1 hswp0 hswp1

set_option maxHeartbeats 2000000 in
/-- **Single-layer residual step commute (Pattern_3 layer induction).**

    Composes the attention sub-block residual commute (`layer_attn_block_commute`)
    with the MoE sub-block residual commute (`layer_moe_block_commute`) into the
    full layer L → L+1 residual invariant.  Given a residual input at layer L
    whose PM shards gather to the SM residual (`allGatherPrimDimN 0 2 0 [r0, r1]`)
    plus replicated weights, the residual output at layer L+1 also PM-shards:
    the SM layer step (attention residual add, then MoE residual add) equals the
    dim-0 gather of the two per-rank layer steps.  Unified over both attention
    types (zigzag / sliding_window) since both reduce to `fw_attn_varlen`.
    Proof: rewrite the attention intermediate via `layer_attn_block_commute`,
    then apply `layer_moe_block_commute` to the two per-rank intermediate shards
    (whose `[2048,1024]` shapes are discharged locally). -/
theorem layer_step_commute
    (r0 r1 : Tensor)
    (wn_a wq wk wv_a cs pos0 pos1 wo cuQ cuK : Tensor)
    (wn_m wr wg wu wv_m wd w13a w13b w2a w2b : Tensor)
    (qh kh d vd : Nat) (causal : Bool) (windowLeft : Nat)
    (E_shard topK t_dim d_dim dInner : Nat) (swigluLimit : Scalar)
    (hqh : 0 < qh) (hkh : 0 < kh) (hd : 0 < d) (hvd : 0 < vd)
    (hE : 0 < E_shard) (ht : 0 < t_dim) (hd_dim : 0 < d_dim) (hdI : 0 < dInner)
    (ht_even : t_dim = 2 * d_dim)
    (hr0 : r0.shape = [2048, 1024]) (hr1 : r1.shape = [2048, 1024])
    (hwn_a : wn_a.shape = [1024])
    (hwq : wq.shape = [qh, d, 1024]) (hwk : wk.shape = [kh, d, 1024])
    (hwv_a : wv_a.shape = [kh, vd, 1024])
    (hpos0 : pos0.shape = [2048, 1]) (hpos1 : pos1.shape = [2048, 1])
    (hwo : wo.shape = [1024, qh * vd])
    (hwr : wr.shape = [E_shard * 2, 1024]) (hwg : wg.shape = [1, 1024])
    (hwu : wu.shape = [dInner, 1024]) (hwv_m : wv_m.shape = [dInner, 1024])
    (hwd : wd.shape = [1024, dInner])
    (hw13a : w13a.shape = [E_shard, t_dim, 1024]) (hw13b : w13b.shape = [E_shard, t_dim, 1024])
    (hw2a : w2a.shape = [E_shard, 1024, d_dim]) (hw2b : w2b.shape = [E_shard, 1024, d_dim])
    (haf : (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft).shape = [2 * 2048, qh, vd]) :
    (elemwiseAdd (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo))
        (elemwiseAdd
          (fw_all2all_moe_gmm_full
            (fw_rms_norm (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo)) wn_m)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo)) wn_m) wr)
                topK (E_shard * 2)).fst)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo)) wn_m) wr)
                topK (E_shard * 2)).snd.fst)
            [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit)
          (elemwiseMul
            (fw_sigmoid (fw_view [2048 * 2, 1]
              (fw_linear (fw_rms_norm (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo)) wn_m) wg)))
            (fw_view [2048 * 2, 1024]
              (fw_linear (fw_swiglu
                (fw_view [2048 * 2, dInner]
                  (fw_linear (fw_rms_norm (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo)) wn_m) wu))
                (fw_view [2048 * 2, dInner]
                  (fw_linear (fw_rms_norm (elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn_a) wv_a)
            cuQ cuK qh kh d vd causal windowLeft)) wo)) wn_m) wv_m))) wd)))))
      = allGatherPrimDimN 0 2 0
          [(elemwiseAdd (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo))
        (elemwiseAdd
          (fw_all2all_moe_gmm_full
            (fw_rms_norm (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wr)
                topK (E_shard * 2)).fst)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wr)
                topK (E_shard * 2)).snd.fst)
            [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit)
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1]
              (fw_linear (fw_rms_norm (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wg)))
            (fw_view [2048, 1024]
              (fw_linear (fw_swiglu
                (fw_view [2048, dInner]
                  (fw_linear (fw_rms_norm (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wu))
                (fw_view [2048, dInner]
                  (fw_linear (fw_rms_norm (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wv_m))) wd))))),
           (elemwiseAdd (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo))
        (elemwiseAdd
          (fw_all2all_moe_gmm_full
            (fw_rms_norm (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wr)
                topK (E_shard * 2)).fst)
            ((fw_topk_routing
                (fw_norm_linear (fw_rms_norm (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wr)
                topK (E_shard * 2)).snd.fst)
            [w13a, w13b] [w2a, w2b] (E_shard * 2) topK swigluLimit)
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1]
              (fw_linear (fw_rms_norm (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wg)))
            (fw_view [2048, 1024]
              (fw_linear (fw_swiglu
                (fw_view [2048, dInner]
                  (fw_linear (fw_rms_norm (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wu))
                (fw_view [2048, dInner]
                  (fw_linear (fw_rms_norm (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) wn_m) wv_m))) wd)))))] := by
  have h_attn := layer_attn_block_commute r0 r1 wn_a wq wk wv_a cs pos0 pos1 wo cuQ cuK
      qh kh d vd causal windowLeft hqh hkh hd hvd hr0 hr1 hwn_a hwq hwk hwv_a
      hpos0 hpos1 hwo haf
  rw [h_attn]
  have hv0 : (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))).shape = [2048, qh * vd] :=
    view_shape_p3 _ _
  have hv1 : (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))).shape = [2048, qh * vd] :=
    view_shape_p3 _ _
  have hproj0 : (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo).shape = [2048, 1024] :=
    linear_shape_p3 2048 (qh * vd) 1024 _ wo hv0 hwo
  have hproj1 : (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo).shape = [2048, 1024] :=
    linear_shape_p3 2048 (qh * vd) 1024 _ wo hv1 hwo
  have hi0 : (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ _ hr0 hproj0
  have hi1 : (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ _ hr1 hproj1
  exact layer_moe_block_commute (elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo)) (elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn_a) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn_a) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn_a) wv_a,
                    fw_per_head_linear (fw_rms_norm r1 wn_a) wv_a])
                cuQ cuK qh kh d vd causal windowLeft))) wo))
    wn_m wr wg wu wv_m wd w13a w13b w2a w2b
    E_shard topK t_dim d_dim dInner swigluLimit
    hE ht hd_dim hdI ht_even hi0 hi1 hwr hwg hwu hwv_m hwd hw13a hw13b hw2a hw2b

end TrainVerify.Denote.GeneratedPatterns
