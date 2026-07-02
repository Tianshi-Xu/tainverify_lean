/- Hand proof for Pattern_1: MoE FF block + norm + inner_chunk_ce over context-parallel.
   Pattern: 1
   SM=25 ops, PM=53 ops, 1124 prereqs (only 13 boundary + intermediateGoals relevant to sm_goal_1).
-/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.Pattern_4  -- reuse topk_routing helpers

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_1_goalIds : List Nat := [1]
inductive pattern_1_target : Prop → Prop
  | goal_1 : pattern_1_target goal_1_stmt_cut

def pattern_1_stmt : Prop :=
  ∀ {target : Prop}, pattern_1_target target → target

/-- If tid X isn't written by any node in the suffix, then folding the suffix
    preserves the value of X. -/
private theorem foldl_suffix_preserves_at (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid)
    (h : ∀ n ∈ nodes, tid ∉ n.outs) :
    (nodes.foldl (applyNode g) s) tid = s tid :=
  foldl_applyNode_at_not_written g nodes s tid h

/-- Post-writer preservation: after applying the writer of X (nodes.take j+1) plus more nodes
    that don't write X, the value at X equals the value right after the writer applied. -/
private theorem foldl_take_split_at_not_written (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid) (j k : Nat) (hjk : j ≤ k)
    (h : ∀ n ∈ (nodes.take k).drop j, tid ∉ n.outs) :
    (nodes.take k).foldl (applyNode g) s tid =
      (nodes.take j).foldl (applyNode g) s tid := by
  -- Split take k = take j ++ drop-and-take.
  have h_split : nodes.take k = nodes.take j ++ (nodes.take k).drop j := by
    rw [show nodes.take j = (nodes.take k).take j by rw [List.take_take, min_eq_left hjk]]
    rw [List.take_append_drop]
  rw [h_split, List.foldl_append]
  exact foldl_applyNode_at_not_written g _ _ tid h

/-- Fold form: if the tid isn't in ANY node's outs, then folding leaves it at initial. -/
private theorem sm_fold_boundary_read (initSM : Store) (tid : Tid)
    (h : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs) :
    (sm_goal_1.nodes.foldl (applyNode sm_goal_1) initSM) tid = initSM tid :=
  foldl_applyNode_at_not_written sm_goal_1 sm_goal_1.nodes initSM tid h

/-! ## SM machinery

`sm_goal_1` has 25 nodes computing final loss `[4096]` from boundary inputs
{4678, 5893, 5895, 5898, 5902, 5903, 5906, 5911, 5915, 5920, 5927, 5929, 5931}.
All FW_reshape / FW_float are identity (verified via intermediate shape checks).
-/

/-- Full unfolding of `denoteGraph sm_goal_1 initSM 4673` in terms of `initSM` values. -/
theorem denote_sm_goal_1_4673 (initSM : Store) :
    denoteGraph sm_goal_1 initSM 4673 =
      (fw_inner_chunk_ce
        (fw_rms_norm
          (fw_maybe_unshuffle (elemwiseAdd (initSM 5893)
              (elemwiseAdd
                (fw_all2all_moe_gmm (initSM 5895)
                  ((fw_topk_routing (initSM 5898) 8 1).fst)
                  ((fw_topk_routing (initSM 5898) 8 1).snd.fst)
                  (initSM 5902) (initSM 5903) 64 0 64 8 ((((10 : Nat) : Scalar))))
                (elemwiseMul
                  (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906))))
                  (fw_view [4096, 1024]
                    (fw_linear
                      (fw_swiglu
                        (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
                        (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
                      (initSM 5920))))))
            1 0 [initSM 5927])
          (initSM 5929))
        (initSM 5931) (initSM 4678)
        (((initSM 5931).shape.head?).getD 0)
        ((((0 : Nat) : Scalar)))).fst := by
  -- Split fold: first 24 nodes → S24, then apply node 24 (inner_chunk_ce).
  have h_split : sm_goal_1.nodes = sm_goal_1.nodes.take 24 ++
      [{ rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678], outs := [4673, 4674], params := [1024] }] := by
    show sm_goal_1.nodes = _
    rfl
  unfold denoteGraph
  rw [h_split, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set S24 : Store := (sm_goal_1.nodes.take 24).foldl (applyNode sm_goal_1) initSM
  rw [applyNode_fw_inner_chunk_ce_fst_out sm_goal_1 S24 0 5930 5931 4678 4673 4674 [1024]]
  -- Now: (fw_inner_chunk_ce (S24 5930) (S24 5931) (S24 4678) ...).fst = <RHS>
  -- Reduce S24 5931 = initSM 5931 (5931 is boundary — not written by any of first 24 nodes).
  have hS24_5931 : S24 5931 = initSM 5931 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 24) initSM 5931
      (by intro n hn; fin_cases hn <;> decide)
  have hS24_4678 : S24 4678 = initSM 4678 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 24) initSM 4678
      (by intro n hn; fin_cases hn <;> decide)
  -- S24 5930: written by node 23 (fw_rms_norm ins=[5928, 5929]).
  have h_take24 : sm_goal_1.nodes.take 24 = sm_goal_1.nodes.take 23 ++
      [{ rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] }] := by rfl
  set S23 : Store := (sm_goal_1.nodes.take 23).foldl (applyNode sm_goal_1) initSM
  have hS24_eq : S24 = applyNode sm_goal_1 S23 { rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] } := by
    show (sm_goal_1.nodes.take 24).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take24, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS24_5930 : S24 5930 = fw_rms_norm (S23 5928) (S23 5929) := by
    rw [hS24_eq]
    exact applyNode_fw_rms_norm_out sm_goal_1 S23 0 5928 5929 5930
  rw [hS24_5931, hS24_4678, hS24_5930]
  -- S23 5928 (via node 22: fw_maybe_unshuffle), S23 5929 (unwritten)
  have hS23_5929 : S23 5929 = initSM 5929 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 23) initSM 5929
      (by intro n hn; fin_cases hn <;> decide)
  have h_take23 : sm_goal_1.nodes.take 23 = sm_goal_1.nodes.take 22 ++
      [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] }] := by rfl
  set S22 : Store := (sm_goal_1.nodes.take 22).foldl (applyNode sm_goal_1) initSM
  have hS23_eq : S23 = applyNode sm_goal_1 S22 { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] } := by
    show (sm_goal_1.nodes.take 23).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take23, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS23_5928 : S23 5928 = fw_maybe_unshuffle (S22 5926) 1 0 [S22 5927] := by
    rw [hS23_eq]
    exact applyNode_fw_maybe_unshuffle_out sm_goal_1 S22 0 5926 5927 5928 [1, 0]
  rw [hS23_5929, hS23_5928]
  -- S22 5927 = initSM 5927 (boundary, not written)
  have hS22_5927 : S22 5927 = initSM 5927 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 22) initSM 5927
      (by intro n hn; fin_cases hn <;> decide)
  rw [hS22_5927]
  sorry

theorem prove_pattern_1 : pattern_1_stmt := by
  sorry -- WIP

end TrainVerify.Denote.GeneratedPatterns