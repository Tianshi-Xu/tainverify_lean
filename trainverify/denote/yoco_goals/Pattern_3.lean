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

end TrainVerify.Denote.GeneratedPatterns
