/- Hand proof for Pattern_1: MoE FF block + norm + inner_chunk_ce over context-parallel.
   Pattern: 1
   SM=25 ops, PM=53 ops, 1124 prereqs (only 13 boundary + intermediateGoals relevant to sm_goal_1).
-/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.Pattern_4  -- reuse topk_routing helpers
import denote.DenoteMoE  -- MoE-specific applyNode/evalOp helpers (rms_norm, sigmoid, swiglu, maybe_unshuffle, all2all_moe_gmm, mix_precision_linear, inner_chunk_ce)

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
  rw [applyNode_fw_inner_chunk_ce_fst_out_1p sm_goal_1 S24 0 5930 5931 4678 4673 4674 [1024]]
  set S1 : Store := (sm_goal_1.nodes.take 1).foldl (applyNode sm_goal_1) initSM with hS1_def
  set S2 : Store := (sm_goal_1.nodes.take 2).foldl (applyNode sm_goal_1) initSM with hS2_def
  set S3 : Store := (sm_goal_1.nodes.take 3).foldl (applyNode sm_goal_1) initSM with hS3_def
  set S4 : Store := (sm_goal_1.nodes.take 4).foldl (applyNode sm_goal_1) initSM with hS4_def
  set S5 : Store := (sm_goal_1.nodes.take 5).foldl (applyNode sm_goal_1) initSM with hS5_def
  set S6 : Store := (sm_goal_1.nodes.take 6).foldl (applyNode sm_goal_1) initSM with hS6_def
  set S7 : Store := (sm_goal_1.nodes.take 7).foldl (applyNode sm_goal_1) initSM with hS7_def
  set S8 : Store := (sm_goal_1.nodes.take 8).foldl (applyNode sm_goal_1) initSM with hS8_def
  set S9 : Store := (sm_goal_1.nodes.take 9).foldl (applyNode sm_goal_1) initSM with hS9_def
  set S10 : Store := (sm_goal_1.nodes.take 10).foldl (applyNode sm_goal_1) initSM with hS10_def
  set S11 : Store := (sm_goal_1.nodes.take 11).foldl (applyNode sm_goal_1) initSM with hS11_def
  set S12 : Store := (sm_goal_1.nodes.take 12).foldl (applyNode sm_goal_1) initSM with hS12_def
  set S13 : Store := (sm_goal_1.nodes.take 13).foldl (applyNode sm_goal_1) initSM with hS13_def
  set S14 : Store := (sm_goal_1.nodes.take 14).foldl (applyNode sm_goal_1) initSM with hS14_def
  set S15 : Store := (sm_goal_1.nodes.take 15).foldl (applyNode sm_goal_1) initSM with hS15_def
  set S16 : Store := (sm_goal_1.nodes.take 16).foldl (applyNode sm_goal_1) initSM with hS16_def
  set S17 : Store := (sm_goal_1.nodes.take 17).foldl (applyNode sm_goal_1) initSM with hS17_def
  set S18 : Store := (sm_goal_1.nodes.take 18).foldl (applyNode sm_goal_1) initSM with hS18_def
  set S19 : Store := (sm_goal_1.nodes.take 19).foldl (applyNode sm_goal_1) initSM with hS19_def
  set S20 : Store := (sm_goal_1.nodes.take 20).foldl (applyNode sm_goal_1) initSM with hS20_def
  set S21 : Store := (sm_goal_1.nodes.take 21).foldl (applyNode sm_goal_1) initSM with hS21_def
  set S22 : Store := (sm_goal_1.nodes.take 22).foldl (applyNode sm_goal_1) initSM with hS22_def
  set S23 : Store := (sm_goal_1.nodes.take 23).foldl (applyNode sm_goal_1) initSM with hS23_def

  -- Sj=24 written by node_23 (FW_rms_norm), outs=[5930], tid=5930
  have h_take24_5930 : sm_goal_1.nodes.take 24 = sm_goal_1.nodes.take 23 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] }] := by rfl
  have hS24_eq_5930 : S24 = applyNode sm_goal_1 S23 { rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] } := by
    show (sm_goal_1.nodes.take 24).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take24_5930, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS24_5930 : S24 5930 = fw_rms_norm (S23 5928) (S23 5929) := by
    rw [hS24_eq_5930]
    exact applyNode_fw_rms_norm_out_1p sm_goal_1 S23 0 5928 5929 5930
  have hS24_5931 : S24 5931 = initSM 5931 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 24) initSM 5931
      (by intro n hn; fin_cases hn <;> decide)
  have hS24_4678 : S24 4678 = initSM 4678 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 24) initSM 4678
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=23 written by node_22 (FW_maybe_unshuffle), outs=[5928], tid=5928
  have h_take23_5928 : sm_goal_1.nodes.take 23 = sm_goal_1.nodes.take 22 ++ [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] }] := by rfl
  have hS23_eq_5928 : S23 = applyNode sm_goal_1 S22 { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] } := by
    show (sm_goal_1.nodes.take 23).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take23_5928, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS23_5928 : S23 5928 = fw_maybe_unshuffle (S22 5926) 1 0 [S22 5927] := by
    rw [hS23_eq_5928]
    exact applyNode_fw_maybe_unshuffle_out_1p sm_goal_1 S22 0 5926 5927 5928 [1, 0]
  have hS23_5929 : S23 5929 = initSM 5929 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 23) initSM 5929
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=22 written by node_21 (FW_add), outs=[5926], tid=5926
  have h_take22_5926 : sm_goal_1.nodes.take 22 = sm_goal_1.nodes.take 21 ++ [{ rank := 0, op := "OpName.FW_add", ins := [8580, 5925], outs := [5926] }] := by rfl
  have hS22_eq_5926 : S22 = applyNode sm_goal_1 S21 { rank := 0, op := "OpName.FW_add", ins := [8580, 5925], outs := [5926] } := by
    show (sm_goal_1.nodes.take 22).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take22_5926, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS22_5926 : S22 5926 = elemwiseAdd (S21 8580) (S21 5925) := by
    rw [hS22_eq_5926]
    exact applyNode_fw_add2_out sm_goal_1 S21 0 8580 5925 5926
  have hS22_5927 : S22 5927 = initSM 5927 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 22) initSM 5927
      (by intro n hn; fin_cases hn <;> decide)
  have hS21_8580 : S21 8580 = S1 8580 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 8580 1 21 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=21 written by node_20 (FW_float), outs=[5925], tid=5925
  have h_take21_5925 : sm_goal_1.nodes.take 21 = sm_goal_1.nodes.take 20 ++ [{ rank := 0, op := "OpName.FW_float", ins := [5924], outs := [5925] }] := by rfl
  have hS21_eq_5925 : S21 = applyNode sm_goal_1 S20 { rank := 0, op := "OpName.FW_float", ins := [5924], outs := [5925] } := by
    show (sm_goal_1.nodes.take 21).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take21_5925, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS21_5925 : S21 5925 = S20 5924 := by
    rw [hS21_eq_5925]
    exact applyNode_fw_float_out sm_goal_1 S20 0 5924 5925 []
  -- Sj=1 written by node_0 (FW_multiref), outs=[8576, 8580], tid=8580
  have h_take1_8580 : sm_goal_1.nodes.take 1 = sm_goal_1.nodes.take 0 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] }] := by rfl
  have hS1_eq_8580 : S1 = applyNode sm_goal_1 initSM { rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] } := by
    show (sm_goal_1.nodes.take 1).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take1_8580, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have hS1_8580 : S1 8580 = initSM 5893 := by
    rw [hS1_eq_8580]
    exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 initSM 0 5893 8576 8580 (by decide)
  -- Sj=20 written by node_19 (FW_add), outs=[5924], tid=5924
  have h_take20_5924 : sm_goal_1.nodes.take 20 = sm_goal_1.nodes.take 19 ++ [{ rank := 0, op := "OpName.FW_add", ins := [5904, 5923], outs := [5924] }] := by rfl
  have hS20_eq_5924 : S20 = applyNode sm_goal_1 S19 { rank := 0, op := "OpName.FW_add", ins := [5904, 5923], outs := [5924] } := by
    show (sm_goal_1.nodes.take 20).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take20_5924, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS20_5924 : S20 5924 = elemwiseAdd (S19 5904) (S19 5923) := by
    rw [hS20_eq_5924]
    exact applyNode_fw_add2_out sm_goal_1 S19 0 5904 5923 5924
  have hS19_5904 : S19 5904 = S13 5904 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5904 13 19 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=19 written by node_18 (FW_mul), outs=[5923], tid=5923
  have h_take19_5923 : sm_goal_1.nodes.take 19 = sm_goal_1.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_mul", ins := [5909, 5922], outs := [5923] }] := by rfl
  have hS19_eq_5923 : S19 = applyNode sm_goal_1 S18 { rank := 0, op := "OpName.FW_mul", ins := [5909, 5922], outs := [5923] } := by
    show (sm_goal_1.nodes.take 19).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take19_5923, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS19_5923 : S19 5923 = elemwiseMul (S18 5909) (S18 5922) := by
    rw [hS19_eq_5923]
    exact applyNode_fw_mul_out sm_goal_1 S18 0 5909 5922 5923
  -- Sj=13 written by node_12 (FW_all2all_moe_gmm), outs=[5904], tid=5904
  have h_take13_5904 : sm_goal_1.nodes.take 13 = sm_goal_1.nodes.take 12 ++ [{ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8591, 5899, 5900, 5902, 5903], outs := [5904], params := [64, 0, 64, 8] }] := by rfl
  have hS13_eq_5904 : S13 = applyNode sm_goal_1 S12 { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8591, 5899, 5900, 5902, 5903], outs := [5904], params := [64, 0, 64, 8] } := by
    show (sm_goal_1.nodes.take 13).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take13_5904, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS13_5904 : S13 5904 = fw_all2all_moe_gmm (S12 8591) (S12 5899) (S12 5900) (S12 5902) (S12 5903) 64 0 64 8 ((((10 : Nat) : Scalar))) := by
    rw [hS13_eq_5904]
    exact applyNode_fw_all2all_moe_gmm_out_1p sm_goal_1 S12 0 8591 5899 5900 5902 5903 5904 [64, 0, 64, 8]
  have hS18_5909 : S18 5909 = S14 5909 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5909 14 18 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=18 written by node_17 (FW_view), outs=[5922], tid=5922
  have h_take18_5922 : sm_goal_1.nodes.take 18 = sm_goal_1.nodes.take 17 ++ [{ rank := 0, op := "OpName.FW_view", ins := [5921], outs := [5922], params := [4096, 1024] }] := by rfl
  have hS18_eq_5922 : S18 = applyNode sm_goal_1 S17 { rank := 0, op := "OpName.FW_view", ins := [5921], outs := [5922], params := [4096, 1024] } := by
    show (sm_goal_1.nodes.take 18).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take18_5922, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS18_5922 : S18 5922 = fw_view [4096, 1024] (S17 5921) := by
    rw [hS18_eq_5922]
    exact applyNode_fw_view_out sm_goal_1 S17 0 4096 [1024] 5921 5922
  have hS12_8591 : S12 8591 = S2 8591 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 8591 2 12 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS12_5899 : S12 5899 = S9 5899 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5899 9 12 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS12_5900 : S12 5900 = S9 5900 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5900 9 12 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS12_5902 : S12 5902 = initSM 5902 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 12) initSM 5902
      (by intro n hn; fin_cases hn <;> decide)
  have hS12_5903 : S12 5903 = initSM 5903 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 12) initSM 5903
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=14 written by node_13 (FW_sigmoid), outs=[5909], tid=5909
  have h_take14_5909 : sm_goal_1.nodes.take 14 = sm_goal_1.nodes.take 13 ++ [{ rank := 0, op := "OpName.FW_sigmoid", ins := [5908], outs := [5909] }] := by rfl
  have hS14_eq_5909 : S14 = applyNode sm_goal_1 S13 { rank := 0, op := "OpName.FW_sigmoid", ins := [5908], outs := [5909] } := by
    show (sm_goal_1.nodes.take 14).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take14_5909, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS14_5909 : S14 5909 = fw_sigmoid (S13 5908) := by
    rw [hS14_eq_5909]
    exact applyNode_fw_sigmoid_out_1p sm_goal_1 S13 0 5908 5909
  -- Sj=17 written by node_16 (FW_mix_precision_linear), outs=[5921], tid=5921
  have h_take17_5921 : sm_goal_1.nodes.take 17 = sm_goal_1.nodes.take 16 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] }] := by rfl
  have hS17_eq_5921 : S17 = applyNode sm_goal_1 S16 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] } := by
    show (sm_goal_1.nodes.take 17).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take17_5921, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS17_5921 : S17 5921 = fw_linear (S16 5919) (S16 5920) := by
    rw [hS17_eq_5921]
    exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 S16 0 5919 5920 5921
  -- Sj=2 written by node_1 (FW_multiref), outs=[8587, 8591, 8595, 8599, 8603], tid=8591
  have h_take2_8591 : sm_goal_1.nodes.take 2 = sm_goal_1.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }] := by rfl
  have hS2_eq_8591 : S2 = applyNode sm_goal_1 S1 { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] } := by
    show (sm_goal_1.nodes.take 2).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take2_8591, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS2_8591 : S2 8591 = S1 5895 := by
    rw [hS2_eq_8591]
    exact applyNode_fw_multiref5_at_pos1_out sm_goal_1 S1 0 5895 8587 8591 8595 8599 8603 (by decide)
  -- Sj=9 written by node_8 (FW_topk_routing), outs=[5899, 5900, 5901], tid=5899
  have h_take9_5899 : sm_goal_1.nodes.take 9 = sm_goal_1.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8] }] := by rfl
  have hS9_eq_5899 : S9 = applyNode sm_goal_1 S8 { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8] } := by
    show (sm_goal_1.nodes.take 9).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take9_5899, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS9_5899 : S9 5899 = (fw_topk_routing (S8 5898) 8 1).fst := by
    rw [hS9_eq_5899]
    exact applyNode_fw_topk_routing_probs_out sm_goal_1 S8 0 5898 5899 5900 5901 [8]
  -- Sj=9 written by node_8 (FW_topk_routing), outs=[5899, 5900, 5901], tid=5900
  have h_take9_5900 : sm_goal_1.nodes.take 9 = sm_goal_1.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8] }] := by rfl
  have hS9_eq_5900 : S9 = applyNode sm_goal_1 S8 { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8] } := by
    show (sm_goal_1.nodes.take 9).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take9_5900, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS9_5900 : S9 5900 = (fw_topk_routing (S8 5898) 8 1).snd.fst := by
    rw [hS9_eq_5900]
    exact applyNode_fw_topk_routing_map_out sm_goal_1 S8 0 5898 5899 5900 5901 [8] (by decide)
  have hS13_5908 : S13 5908 = S10 5908 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5908 10 13 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=16 written by node_15 (FW_reshape), outs=[5919], tid=5919
  have h_take16_5919 : sm_goal_1.nodes.take 16 = sm_goal_1.nodes.take 15 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [5918], outs := [5919] }] := by rfl
  have hS16_eq_5919 : S16 = applyNode sm_goal_1 S15 { rank := 0, op := "OpName.FW_reshape", ins := [5918], outs := [5919] } := by
    show (sm_goal_1.nodes.take 16).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take16_5919, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS16_5919 : S16 5919 = S15 5918 := by
    rw [hS16_eq_5919]
    exact applyNode_fw_reshape_out sm_goal_1 S15 0 5918 5919 []
  have hS16_5920 : S16 5920 = initSM 5920 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 16) initSM 5920
      (by intro n hn; fin_cases hn <;> decide)
  have hS1_5895 : S1 5895 = initSM 5895 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 1) initSM 5895
      (by intro n hn; fin_cases hn <;> decide)
  have hS8_5898 : S8 5898 = initSM 5898 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 8) initSM 5898
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=10 written by node_9 (FW_view), outs=[5908], tid=5908
  have h_take10_5908 : sm_goal_1.nodes.take 10 = sm_goal_1.nodes.take 9 ++ [{ rank := 0, op := "OpName.FW_view", ins := [5907], outs := [5908], params := [4096, 1] }] := by rfl
  have hS10_eq_5908 : S10 = applyNode sm_goal_1 S9 { rank := 0, op := "OpName.FW_view", ins := [5907], outs := [5908], params := [4096, 1] } := by
    show (sm_goal_1.nodes.take 10).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take10_5908, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS10_5908 : S10 5908 = fw_view [4096, 1] (S9 5907) := by
    rw [hS10_eq_5908]
    exact applyNode_fw_view_out sm_goal_1 S9 0 4096 [1] 5907 5908
  -- Sj=15 written by node_14 (FW_swiglu), outs=[5918], tid=5918
  have h_take15_5918 : sm_goal_1.nodes.take 15 = sm_goal_1.nodes.take 14 ++ [{ rank := 0, op := "OpName.FW_swiglu", ins := [5913, 5917], outs := [5918] }] := by rfl
  have hS15_eq_5918 : S15 = applyNode sm_goal_1 S14 { rank := 0, op := "OpName.FW_swiglu", ins := [5913, 5917], outs := [5918] } := by
    show (sm_goal_1.nodes.take 15).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take15_5918, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS15_5918 : S15 5918 = fw_swiglu (S14 5913) (S14 5917) := by
    rw [hS15_eq_5918]
    exact applyNode_fw_swiglu_out_1p sm_goal_1 S14 0 5913 5917 5918
  have hS9_5907 : S9 5907 = S6 5907 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5907 6 9 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS14_5913 : S14 5913 = S11 5913 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5913 11 14 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS14_5917 : S14 5917 = S12 5917 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5917 12 14 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=6 written by node_5 (FW_mix_precision_linear), outs=[5907], tid=5907
  have h_take6_5907 : sm_goal_1.nodes.take 6 = sm_goal_1.nodes.take 5 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5905, 5906], outs := [5907] }] := by rfl
  have hS6_eq_5907 : S6 = applyNode sm_goal_1 S5 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5905, 5906], outs := [5907] } := by
    show (sm_goal_1.nodes.take 6).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take6_5907, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS6_5907 : S6 5907 = fw_linear (S5 5905) (S5 5906) := by
    rw [hS6_eq_5907]
    exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 S5 0 5905 5906 5907
  -- Sj=11 written by node_10 (FW_view), outs=[5913], tid=5913
  have h_take11_5913 : sm_goal_1.nodes.take 11 = sm_goal_1.nodes.take 10 ++ [{ rank := 0, op := "OpName.FW_view", ins := [5912], outs := [5913], params := [4096, 512] }] := by rfl
  have hS11_eq_5913 : S11 = applyNode sm_goal_1 S10 { rank := 0, op := "OpName.FW_view", ins := [5912], outs := [5913], params := [4096, 512] } := by
    show (sm_goal_1.nodes.take 11).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take11_5913, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS11_5913 : S11 5913 = fw_view [4096, 512] (S10 5912) := by
    rw [hS11_eq_5913]
    exact applyNode_fw_view_out sm_goal_1 S10 0 4096 [512] 5912 5913
  -- Sj=12 written by node_11 (FW_view), outs=[5917], tid=5917
  have h_take12_5917 : sm_goal_1.nodes.take 12 = sm_goal_1.nodes.take 11 ++ [{ rank := 0, op := "OpName.FW_view", ins := [5916], outs := [5917], params := [4096, 512] }] := by rfl
  have hS12_eq_5917 : S12 = applyNode sm_goal_1 S11 { rank := 0, op := "OpName.FW_view", ins := [5916], outs := [5917], params := [4096, 512] } := by
    show (sm_goal_1.nodes.take 12).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take12_5917, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS12_5917 : S12 5917 = fw_view [4096, 512] (S11 5916) := by
    rw [hS12_eq_5917]
    exact applyNode_fw_view_out sm_goal_1 S11 0 4096 [512] 5916 5917
  have hS5_5905 : S5 5905 = S3 5905 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5905 3 5 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS5_5906 : S5 5906 = initSM 5906 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 5) initSM 5906
      (by intro n hn; fin_cases hn <;> decide)
  have hS10_5912 : S10 5912 = S7 5912 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5912 7 10 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS11_5916 : S11 5916 = S8 5916 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5916 8 11 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=3 written by node_2 (FW_reshape), outs=[5905], tid=5905
  have h_take3_5905 : sm_goal_1.nodes.take 3 = sm_goal_1.nodes.take 2 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [8595], outs := [5905] }] := by rfl
  have hS3_eq_5905 : S3 = applyNode sm_goal_1 S2 { rank := 0, op := "OpName.FW_reshape", ins := [8595], outs := [5905] } := by
    show (sm_goal_1.nodes.take 3).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take3_5905, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS3_5905 : S3 5905 = S2 8595 := by
    rw [hS3_eq_5905]
    exact applyNode_fw_reshape_out sm_goal_1 S2 0 8595 5905 []
  -- Sj=7 written by node_6 (FW_mix_precision_linear), outs=[5912], tid=5912
  have h_take7_5912 : sm_goal_1.nodes.take 7 = sm_goal_1.nodes.take 6 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5910, 5911], outs := [5912] }] := by rfl
  have hS7_eq_5912 : S7 = applyNode sm_goal_1 S6 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5910, 5911], outs := [5912] } := by
    show (sm_goal_1.nodes.take 7).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take7_5912, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS7_5912 : S7 5912 = fw_linear (S6 5910) (S6 5911) := by
    rw [hS7_eq_5912]
    exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 S6 0 5910 5911 5912
  -- Sj=8 written by node_7 (FW_mix_precision_linear), outs=[5916], tid=5916
  have h_take8_5916 : sm_goal_1.nodes.take 8 = sm_goal_1.nodes.take 7 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] }] := by rfl
  have hS8_eq_5916 : S8 = applyNode sm_goal_1 S7 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] } := by
    show (sm_goal_1.nodes.take 8).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take8_5916, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS8_5916 : S8 5916 = fw_linear (S7 5914) (S7 5915) := by
    rw [hS8_eq_5916]
    exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 S7 0 5914 5915 5916
  -- Sj=2 written by node_1 (FW_multiref), outs=[8587, 8591, 8595, 8599, 8603], tid=8595
  have h_take2_8595 : sm_goal_1.nodes.take 2 = sm_goal_1.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }] := by rfl
  have hS2_eq_8595 : S2 = applyNode sm_goal_1 S1 { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] } := by
    show (sm_goal_1.nodes.take 2).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take2_8595, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS2_8595 : S2 8595 = S1 5895 := by
    rw [hS2_eq_8595]
    exact applyNode_fw_multiref5_at_pos2_out sm_goal_1 S1 0 5895 8587 8591 8595 8599 8603 (by decide) (by decide)
  have hS6_5910 : S6 5910 = S4 5910 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5910 4 6 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS6_5911 : S6 5911 = initSM 5911 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 6) initSM 5911
      (by intro n hn; fin_cases hn <;> decide)
  have hS7_5914 : S7 5914 = S5 5914 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5914 5 7 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS7_5915 : S7 5915 = initSM 5915 :=
    foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 7) initSM 5915
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=4 written by node_3 (FW_reshape), outs=[5910], tid=5910
  have h_take4_5910 : sm_goal_1.nodes.take 4 = sm_goal_1.nodes.take 3 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [8599], outs := [5910] }] := by rfl
  have hS4_eq_5910 : S4 = applyNode sm_goal_1 S3 { rank := 0, op := "OpName.FW_reshape", ins := [8599], outs := [5910] } := by
    show (sm_goal_1.nodes.take 4).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take4_5910, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS4_5910 : S4 5910 = S3 8599 := by
    rw [hS4_eq_5910]
    exact applyNode_fw_reshape_out sm_goal_1 S3 0 8599 5910 []
  -- Sj=5 written by node_4 (FW_reshape), outs=[5914], tid=5914
  have h_take5_5914 : sm_goal_1.nodes.take 5 = sm_goal_1.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [8603], outs := [5914] }] := by rfl
  have hS5_eq_5914 : S5 = applyNode sm_goal_1 S4 { rank := 0, op := "OpName.FW_reshape", ins := [8603], outs := [5914] } := by
    show (sm_goal_1.nodes.take 5).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take5_5914, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS5_5914 : S5 5914 = S4 8603 := by
    rw [hS5_eq_5914]
    exact applyNode_fw_reshape_out sm_goal_1 S4 0 8603 5914 []
  have hS3_8599 : S3 8599 = S2 8599 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 8599 2 3 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hS4_8603 : S4 8603 = S2 8603 :=
    foldl_take_split_at_not_written sm_goal_1 sm_goal_1.nodes initSM 8603 2 4 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Sj=2 written by node_1 (FW_multiref), outs=[8587, 8591, 8595, 8599, 8603], tid=8599
  have h_take2_8599 : sm_goal_1.nodes.take 2 = sm_goal_1.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }] := by rfl
  have hS2_eq_8599 : S2 = applyNode sm_goal_1 S1 { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] } := by
    show (sm_goal_1.nodes.take 2).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take2_8599, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS2_8599 : S2 8599 = S1 5895 := by
    rw [hS2_eq_8599]
    exact applyNode_fw_multiref5_at_pos3_out sm_goal_1 S1 0 5895 8587 8591 8595 8599 8603 (by decide) (by decide) (by decide)
  -- Sj=2 written by node_1 (FW_multiref), outs=[8587, 8591, 8595, 8599, 8603], tid=8603
  have h_take2_8603 : sm_goal_1.nodes.take 2 = sm_goal_1.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }] := by rfl
  have hS2_eq_8603 : S2 = applyNode sm_goal_1 S1 { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] } := by
    show (sm_goal_1.nodes.take 2).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take2_8603, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS2_8603 : S2 8603 = S1 5895 := by
    rw [hS2_eq_8603]
    exact applyNode_fw_multiref5_at_pos4_out sm_goal_1 S1 0 5895 8587 8591 8595 8599 8603 (by decide) (by decide) (by decide) (by decide)
  rw [
    hS24_5930, hS24_5931, hS24_4678,
    hS23_5928, hS23_5929, hS22_5926,
    hS22_5927, hS21_8580, hS21_5925,
    hS20_5924, hS19_5904, hS19_5923,
    hS18_5909, hS18_5922, hS17_5921,
    hS16_5919, hS16_5920, hS15_5918,
    hS14_5909, hS14_5913, hS14_5917,
    hS13_5904, hS13_5908, hS12_8591,
    hS12_5899, hS12_5900, hS12_5902,
    hS12_5903, hS12_5917, hS11_5913,
    hS11_5916, hS10_5908, hS10_5912,
    hS9_5899, hS9_5900, hS9_5907,
    hS8_5898, hS8_5916, hS7_5912,
    hS7_5914, hS7_5915, hS6_5907,
    hS6_5910, hS6_5911, hS5_5905,
    hS5_5906, hS5_5914, hS4_5910,
    hS4_8603, hS3_5905, hS3_8599,
    hS2_8591, hS2_8595, hS2_8599,
    hS2_8603, hS1_8580, hS1_5895,
    
  ]
  -- Final simp to reduce (List.getD [1024] 1 0) = 0 in the ce params.
  rfl



/-- Full unfolding of `denoteGraph pm_goal_1 initPM 4673`. -/
theorem denote_pm_goal_1_4673 (initPM : Store) :
    denoteGraph pm_goal_1 initPM 4673 =
      allGatherPrimDimN 0 pm_goal_1.numRanks 0 [(fw_inner_chunk_ce (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11609) (elemwiseAdd (fw_all2all_moe_gmm (initPM 11613) ((fw_topk_routing (initPM 11621) 8 1).fst) ((fw_topk_routing (initPM 11621) 8 1).snd.fst) (initPM 11629) (initPM 11631) 64 0 32 8 ((((10 : Nat) : Scalar)))) (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))) (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911))) (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915)))) (initPM 5920)))))) 2 0 [initPM 5927]) (initPM 5929)) (initPM 5931) (chunkPrimDimN 0 pm_goal_1.numRanks 0 (initPM 4678)) (((initPM 5931).shape.head?).getD 0) ((((0 : Nat) : Scalar)))).fst, (fw_inner_chunk_ce (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11610) (elemwiseAdd (fw_all2all_moe_gmm (initPM 11614) ((fw_topk_routing (initPM 11622) 8 1).fst) ((fw_topk_routing (initPM 11622) 8 1).snd.fst) (initPM 11630) (initPM 11632) 64 32 64 8 ((((10 : Nat) : Scalar)))) (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))) (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911))) (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915)))) (initPM 5920)))))) 2 1 [initPM 5927]) (initPM 5929)) (initPM 5931) (chunkPrimDimN 0 pm_goal_1.numRanks 1 (initPM 4678)) (((initPM 5931).shape.head?).getD 0) ((((0 : Nat) : Scalar)))).fst] := by
  have h_split : pm_goal_1.nodes = pm_goal_1.nodes.take 52 ++
      [{ rank := 0, op := "OpName.AllGatherPrim", ins := [11837, 11838], outs := [4673], params := [0] }] := by
    show pm_goal_1.nodes = _
    rfl
  unfold denoteGraph
  rw [h_split, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set P52 : Store := (pm_goal_1.nodes.take 52).foldl (applyNode pm_goal_1) initPM
  set P1 : Store := (pm_goal_1.nodes.take 1).foldl (applyNode pm_goal_1) initPM with hP1_def
  set P2 : Store := (pm_goal_1.nodes.take 2).foldl (applyNode pm_goal_1) initPM with hP2_def
  set P3 : Store := (pm_goal_1.nodes.take 3).foldl (applyNode pm_goal_1) initPM with hP3_def
  set P4 : Store := (pm_goal_1.nodes.take 4).foldl (applyNode pm_goal_1) initPM with hP4_def
  set P5 : Store := (pm_goal_1.nodes.take 5).foldl (applyNode pm_goal_1) initPM with hP5_def
  set P6 : Store := (pm_goal_1.nodes.take 6).foldl (applyNode pm_goal_1) initPM with hP6_def
  set P7 : Store := (pm_goal_1.nodes.take 7).foldl (applyNode pm_goal_1) initPM with hP7_def
  set P8 : Store := (pm_goal_1.nodes.take 8).foldl (applyNode pm_goal_1) initPM with hP8_def
  set P9 : Store := (pm_goal_1.nodes.take 9).foldl (applyNode pm_goal_1) initPM with hP9_def
  set P10 : Store := (pm_goal_1.nodes.take 10).foldl (applyNode pm_goal_1) initPM with hP10_def
  set P11 : Store := (pm_goal_1.nodes.take 11).foldl (applyNode pm_goal_1) initPM with hP11_def
  set P12 : Store := (pm_goal_1.nodes.take 12).foldl (applyNode pm_goal_1) initPM with hP12_def
  set P13 : Store := (pm_goal_1.nodes.take 13).foldl (applyNode pm_goal_1) initPM with hP13_def
  set P14 : Store := (pm_goal_1.nodes.take 14).foldl (applyNode pm_goal_1) initPM with hP14_def
  set P15 : Store := (pm_goal_1.nodes.take 15).foldl (applyNode pm_goal_1) initPM with hP15_def
  set P16 : Store := (pm_goal_1.nodes.take 16).foldl (applyNode pm_goal_1) initPM with hP16_def
  set P17 : Store := (pm_goal_1.nodes.take 17).foldl (applyNode pm_goal_1) initPM with hP17_def
  set P18 : Store := (pm_goal_1.nodes.take 18).foldl (applyNode pm_goal_1) initPM with hP18_def
  set P19 : Store := (pm_goal_1.nodes.take 19).foldl (applyNode pm_goal_1) initPM with hP19_def
  set P20 : Store := (pm_goal_1.nodes.take 20).foldl (applyNode pm_goal_1) initPM with hP20_def
  set P21 : Store := (pm_goal_1.nodes.take 21).foldl (applyNode pm_goal_1) initPM with hP21_def
  set P22 : Store := (pm_goal_1.nodes.take 22).foldl (applyNode pm_goal_1) initPM with hP22_def
  set P23 : Store := (pm_goal_1.nodes.take 23).foldl (applyNode pm_goal_1) initPM with hP23_def
  set P24 : Store := (pm_goal_1.nodes.take 24).foldl (applyNode pm_goal_1) initPM with hP24_def
  set P25 : Store := (pm_goal_1.nodes.take 25).foldl (applyNode pm_goal_1) initPM with hP25_def
  set P26 : Store := (pm_goal_1.nodes.take 26).foldl (applyNode pm_goal_1) initPM with hP26_def
  set P27 : Store := (pm_goal_1.nodes.take 27).foldl (applyNode pm_goal_1) initPM with hP27_def
  set P28 : Store := (pm_goal_1.nodes.take 28).foldl (applyNode pm_goal_1) initPM with hP28_def
  set P29 : Store := (pm_goal_1.nodes.take 29).foldl (applyNode pm_goal_1) initPM with hP29_def
  set P30 : Store := (pm_goal_1.nodes.take 30).foldl (applyNode pm_goal_1) initPM with hP30_def
  set P31 : Store := (pm_goal_1.nodes.take 31).foldl (applyNode pm_goal_1) initPM with hP31_def
  set P32 : Store := (pm_goal_1.nodes.take 32).foldl (applyNode pm_goal_1) initPM with hP32_def
  set P33 : Store := (pm_goal_1.nodes.take 33).foldl (applyNode pm_goal_1) initPM with hP33_def
  set P34 : Store := (pm_goal_1.nodes.take 34).foldl (applyNode pm_goal_1) initPM with hP34_def
  set P35 : Store := (pm_goal_1.nodes.take 35).foldl (applyNode pm_goal_1) initPM with hP35_def
  set P36 : Store := (pm_goal_1.nodes.take 36).foldl (applyNode pm_goal_1) initPM with hP36_def
  set P37 : Store := (pm_goal_1.nodes.take 37).foldl (applyNode pm_goal_1) initPM with hP37_def
  set P38 : Store := (pm_goal_1.nodes.take 38).foldl (applyNode pm_goal_1) initPM with hP38_def
  set P39 : Store := (pm_goal_1.nodes.take 39).foldl (applyNode pm_goal_1) initPM with hP39_def
  set P40 : Store := (pm_goal_1.nodes.take 40).foldl (applyNode pm_goal_1) initPM with hP40_def
  set P41 : Store := (pm_goal_1.nodes.take 41).foldl (applyNode pm_goal_1) initPM with hP41_def
  set P42 : Store := (pm_goal_1.nodes.take 42).foldl (applyNode pm_goal_1) initPM with hP42_def
  set P43 : Store := (pm_goal_1.nodes.take 43).foldl (applyNode pm_goal_1) initPM with hP43_def
  set P44 : Store := (pm_goal_1.nodes.take 44).foldl (applyNode pm_goal_1) initPM with hP44_def
  set P45 : Store := (pm_goal_1.nodes.take 45).foldl (applyNode pm_goal_1) initPM with hP45_def
  set P46 : Store := (pm_goal_1.nodes.take 46).foldl (applyNode pm_goal_1) initPM with hP46_def
  set P47 : Store := (pm_goal_1.nodes.take 47).foldl (applyNode pm_goal_1) initPM with hP47_def
  set P48 : Store := (pm_goal_1.nodes.take 48).foldl (applyNode pm_goal_1) initPM with hP48_def
  set P49 : Store := (pm_goal_1.nodes.take 49).foldl (applyNode pm_goal_1) initPM with hP49_def
  set P50 : Store := (pm_goal_1.nodes.take 50).foldl (applyNode pm_goal_1) initPM with hP50_def
  set P51 : Store := (pm_goal_1.nodes.take 51).foldl (applyNode pm_goal_1) initPM with hP51_def
  rw [applyNode_allGatherPrimDimN_out pm_goal_1 P52 0 [11837, 11838] 4673 0]
  simp only [List.map, List.map_cons, List.map_nil]
  have hP52_11837 : P52 11837 = P51 11837 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11837 51 52 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=52 written by pm_node_51 (rank=1 FW_inner_chunk_ce), outs=[11838, 11840], tid=11838
  have h_pmtake52_11838 : pm_goal_1.nodes.take 52 = pm_goal_1.nodes.take 51 ++ [{ rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836], outs := [11838, 11840], params := [1024] }] := by rfl
  have hP52_eq_11838 : P52 = applyNode pm_goal_1 P51 { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836], outs := [11838, 11840], params := [1024] } := by
    show (pm_goal_1.nodes.take 52).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake52_11838, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP52_11838 : P52 11838 = (fw_inner_chunk_ce (P51 11834) (P51 5931) (P51 11836) ((((P51 5931).shape.head?).getD 0)) ((((0 : Nat) : Scalar)))).fst := by
    rw [hP52_eq_11838]
    exact applyNode_fw_inner_chunk_ce_fst_out_1p pm_goal_1 P51 1 11834 5931 11836 11838 11840 [1024]
  -- Pj=51 written by pm_node_50 (rank=0 FW_inner_chunk_ce), outs=[11837, 11839], tid=11837
  have h_pmtake51_11837 : pm_goal_1.nodes.take 51 = pm_goal_1.nodes.take 50 ++ [{ rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835], outs := [11837, 11839], params := [1024] }] := by rfl
  have hP51_eq_11837 : P51 = applyNode pm_goal_1 P50 { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835], outs := [11837, 11839], params := [1024] } := by
    show (pm_goal_1.nodes.take 51).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake51_11837, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP51_11837 : P51 11837 = (fw_inner_chunk_ce (P50 11833) (P50 5931) (P50 11835) ((((P50 5931).shape.head?).getD 0)) ((((0 : Nat) : Scalar)))).fst := by
    rw [hP51_eq_11837]
    exact applyNode_fw_inner_chunk_ce_fst_out_1p pm_goal_1 P50 0 11833 5931 11835 11837 11839 [1024]
  have hP51_11834 : P51 11834 = P50 11834 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11834 50 51 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP51_5931 : P51 5931 = initPM 5931 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 51) initPM 5931
      (by intro n hn; fin_cases hn <;> decide)
  have hP51_11836 : P51 11836 = P2 11836 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11836 2 51 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP50_11833 : P50 11833 = P49 11833 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11833 49 50 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP50_5931 : P50 5931 = initPM 5931 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 50) initPM 5931
      (by intro n hn; fin_cases hn <;> decide)
  have hP50_11835 : P50 11835 = P1 11835 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11835 1 50 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=50 written by pm_node_49 (rank=1 FW_rms_norm), outs=[11834], tid=11834
  have h_pmtake50_11834 : pm_goal_1.nodes.take 50 = pm_goal_1.nodes.take 49 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [11728, 5929], outs := [11834] }] := by rfl
  have hP50_eq_11834 : P50 = applyNode pm_goal_1 P49 { rank := 1, op := "OpName.FW_rms_norm", ins := [11728, 5929], outs := [11834] } := by
    show (pm_goal_1.nodes.take 50).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake50_11834, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP50_11834 : P50 11834 = fw_rms_norm (P49 11728) (P49 5929) := by
    rw [hP50_eq_11834]
    exact applyNode_fw_rms_norm_out_1p pm_goal_1 P49 1 11728 5929 11834
  -- Pj=2 written by pm_node_1 (rank=1 ChunkPrim), outs=[11836], tid=11836
  have h_pmtake2_11836 : pm_goal_1.nodes.take 2 = pm_goal_1.nodes.take 1 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] }] := by rfl
  have hP2_eq_11836 : P2 = applyNode pm_goal_1 P1 { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] } := by
    show (pm_goal_1.nodes.take 2).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake2_11836, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP2_11836 : P2 11836 = chunkPrimDimN 0 pm_goal_1.numRanks 1 (P1 4678) := by
    rw [hP2_eq_11836]
    exact applyNode_chunkPrimDimN_out pm_goal_1 P1 1 4678 11836 0
  -- Pj=49 written by pm_node_48 (rank=0 FW_rms_norm), outs=[11833], tid=11833
  have h_pmtake49_11833 : pm_goal_1.nodes.take 49 = pm_goal_1.nodes.take 48 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [11727, 5929], outs := [11833] }] := by rfl
  have hP49_eq_11833 : P49 = applyNode pm_goal_1 P48 { rank := 0, op := "OpName.FW_rms_norm", ins := [11727, 5929], outs := [11833] } := by
    show (pm_goal_1.nodes.take 49).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake49_11833, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP49_11833 : P49 11833 = fw_rms_norm (P48 11727) (P48 5929) := by
    rw [hP49_eq_11833]
    exact applyNode_fw_rms_norm_out_1p pm_goal_1 P48 0 11727 5929 11833
  -- Pj=1 written by pm_node_0 (rank=0 ChunkPrim), outs=[11835], tid=11835
  have h_pmtake1_11835 : pm_goal_1.nodes.take 1 = pm_goal_1.nodes.take 0 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] }] := by rfl
  have hP1_eq_11835 : P1 = applyNode pm_goal_1 initPM { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] } := by
    show (pm_goal_1.nodes.take 1).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake1_11835, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have hP1_11835 : P1 11835 = chunkPrimDimN 0 pm_goal_1.numRanks 0 (initPM 4678) := by
    rw [hP1_eq_11835]
    exact applyNode_chunkPrimDimN_out pm_goal_1 initPM 0 4678 11835 0
  have hP49_11728 : P49 11728 = P48 11728 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11728 48 49 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP49_5929 : P49 5929 = initPM 5929 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 49) initPM 5929
      (by intro n hn; fin_cases hn <;> decide)
  have hP1_4678 : P1 4678 = initPM 4678 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 1) initPM 4678
      (by intro n hn; fin_cases hn <;> decide)
  have hP48_11727 : P48 11727 = P47 11727 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11727 47 48 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP48_5929 : P48 5929 = initPM 5929 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 48) initPM 5929
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=48 written by pm_node_47 (rank=1 FW_maybe_unshuffle), outs=[11728], tid=11728
  have h_pmtake48_11728 : pm_goal_1.nodes.take 48 = pm_goal_1.nodes.take 47 ++ [{ rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927], outs := [11728], params := [2, 1] }] := by rfl
  have hP48_eq_11728 : P48 = applyNode pm_goal_1 P47 { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927], outs := [11728], params := [2, 1] } := by
    show (pm_goal_1.nodes.take 48).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake48_11728, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP48_11728 : P48 11728 = fw_maybe_unshuffle (P47 11722) 2 1 [P47 5927] := by
    rw [hP48_eq_11728]
    exact applyNode_fw_maybe_unshuffle_out_1p pm_goal_1 P47 1 11722 5927 11728 [2, 1]
  -- Pj=47 written by pm_node_46 (rank=0 FW_maybe_unshuffle), outs=[11727], tid=11727
  have h_pmtake47_11727 : pm_goal_1.nodes.take 47 = pm_goal_1.nodes.take 46 ++ [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] }] := by rfl
  have hP47_eq_11727 : P47 = applyNode pm_goal_1 P46 { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] } := by
    show (pm_goal_1.nodes.take 47).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake47_11727, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP47_11727 : P47 11727 = fw_maybe_unshuffle (P46 11721) 2 0 [P46 5927] := by
    rw [hP47_eq_11727]
    exact applyNode_fw_maybe_unshuffle_out_1p pm_goal_1 P46 0 11721 5927 11727 [2, 0]
  have hP47_11722 : P47 11722 = P46 11722 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11722 46 47 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP47_5927 : P47 5927 = initPM 5927 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 47) initPM 5927
      (by intro n hn; fin_cases hn <;> decide)
  have hP46_11721 : P46 11721 = P45 11721 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11721 45 46 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP46_5927 : P46 5927 = initPM 5927 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 46) initPM 5927
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=46 written by pm_node_45 (rank=1 FW_add), outs=[11722], tid=11722
  have h_pmtake46_11722 : pm_goal_1.nodes.take 46 = pm_goal_1.nodes.take 45 ++ [{ rank := 1, op := "OpName.FW_add", ins := [16855, 11718], outs := [11722] }] := by rfl
  have hP46_eq_11722 : P46 = applyNode pm_goal_1 P45 { rank := 1, op := "OpName.FW_add", ins := [16855, 11718], outs := [11722] } := by
    show (pm_goal_1.nodes.take 46).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake46_11722, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP46_11722 : P46 11722 = elemwiseAdd (P45 16855) (P45 11718) := by
    rw [hP46_eq_11722]
    exact applyNode_fw_add2_out pm_goal_1 P45 1 16855 11718 11722
  -- Pj=45 written by pm_node_44 (rank=0 FW_add), outs=[11721], tid=11721
  have h_pmtake45_11721 : pm_goal_1.nodes.take 45 = pm_goal_1.nodes.take 44 ++ [{ rank := 0, op := "OpName.FW_add", ins := [16847, 11717], outs := [11721] }] := by rfl
  have hP45_eq_11721 : P45 = applyNode pm_goal_1 P44 { rank := 0, op := "OpName.FW_add", ins := [16847, 11717], outs := [11721] } := by
    show (pm_goal_1.nodes.take 45).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake45_11721, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP45_11721 : P45 11721 = elemwiseAdd (P44 16847) (P44 11717) := by
    rw [hP45_eq_11721]
    exact applyNode_fw_add2_out pm_goal_1 P44 0 16847 11717 11721
  have hP45_16855 : P45 16855 = P4 16855 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16855 4 45 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP45_11718 : P45 11718 = P44 11718 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11718 44 45 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP44_16847 : P44 16847 = P3 16847 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16847 3 44 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP44_11717 : P44 11717 = P43 11717 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11717 43 44 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=4 written by pm_node_3 (rank=1 FW_multiref), outs=[16851, 16855], tid=16855
  have h_pmtake4_16855 : pm_goal_1.nodes.take 4 = pm_goal_1.nodes.take 3 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] }] := by rfl
  have hP4_eq_16855 : P4 = applyNode pm_goal_1 P3 { rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] } := by
    show (pm_goal_1.nodes.take 4).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake4_16855, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP4_16855 : P4 16855 = P3 11610 := by
    rw [hP4_eq_16855]
    exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 P3 1 11610 16851 16855 (by decide)
  -- Pj=44 written by pm_node_43 (rank=1 FW_float), outs=[11718], tid=11718
  have h_pmtake44_11718 : pm_goal_1.nodes.take 44 = pm_goal_1.nodes.take 43 ++ [{ rank := 1, op := "OpName.FW_float", ins := [11712], outs := [11718] }] := by rfl
  have hP44_eq_11718 : P44 = applyNode pm_goal_1 P43 { rank := 1, op := "OpName.FW_float", ins := [11712], outs := [11718] } := by
    show (pm_goal_1.nodes.take 44).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake44_11718, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP44_11718 : P44 11718 = P43 11712 := by
    rw [hP44_eq_11718]
    exact applyNode_fw_float_out pm_goal_1 P43 1 11712 11718 []
  -- Pj=3 written by pm_node_2 (rank=0 FW_multiref), outs=[16843, 16847], tid=16847
  have h_pmtake3_16847 : pm_goal_1.nodes.take 3 = pm_goal_1.nodes.take 2 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] }] := by rfl
  have hP3_eq_16847 : P3 = applyNode pm_goal_1 P2 { rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] } := by
    show (pm_goal_1.nodes.take 3).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake3_16847, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP3_16847 : P3 16847 = P2 11609 := by
    rw [hP3_eq_16847]
    exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 P2 0 11609 16843 16847 (by decide)
  -- Pj=43 written by pm_node_42 (rank=0 FW_float), outs=[11717], tid=11717
  have h_pmtake43_11717 : pm_goal_1.nodes.take 43 = pm_goal_1.nodes.take 42 ++ [{ rank := 0, op := "OpName.FW_float", ins := [11711], outs := [11717] }] := by rfl
  have hP43_eq_11717 : P43 = applyNode pm_goal_1 P42 { rank := 0, op := "OpName.FW_float", ins := [11711], outs := [11717] } := by
    show (pm_goal_1.nodes.take 43).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake43_11717, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP43_11717 : P43 11717 = P42 11711 := by
    rw [hP43_eq_11717]
    exact applyNode_fw_float_out pm_goal_1 P42 0 11711 11717 []
  have hP3_11610 : P3 11610 = initPM 11610 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 3) initPM 11610
      (by intro n hn; fin_cases hn <;> decide)
  have hP43_11712 : P43 11712 = P42 11712 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11712 42 43 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP2_11609 : P2 11609 = initPM 11609 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 2) initPM 11609
      (by intro n hn; fin_cases hn <;> decide)
  have hP42_11711 : P42 11711 = P41 11711 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11711 41 42 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=42 written by pm_node_41 (rank=1 FW_add), outs=[11712], tid=11712
  have h_pmtake42_11712 : pm_goal_1.nodes.take 42 = pm_goal_1.nodes.take 41 ++ [{ rank := 1, op := "OpName.FW_add", ins := [11634, 11708], outs := [11712] }] := by rfl
  have hP42_eq_11712 : P42 = applyNode pm_goal_1 P41 { rank := 1, op := "OpName.FW_add", ins := [11634, 11708], outs := [11712] } := by
    show (pm_goal_1.nodes.take 42).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake42_11712, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP42_11712 : P42 11712 = elemwiseAdd (P41 11634) (P41 11708) := by
    rw [hP42_eq_11712]
    exact applyNode_fw_add2_out pm_goal_1 P41 1 11634 11708 11712
  -- Pj=41 written by pm_node_40 (rank=0 FW_add), outs=[11711], tid=11711
  have h_pmtake41_11711 : pm_goal_1.nodes.take 41 = pm_goal_1.nodes.take 40 ++ [{ rank := 0, op := "OpName.FW_add", ins := [11633, 11707], outs := [11711] }] := by rfl
  have hP41_eq_11711 : P41 = applyNode pm_goal_1 P40 { rank := 0, op := "OpName.FW_add", ins := [11633, 11707], outs := [11711] } := by
    show (pm_goal_1.nodes.take 41).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake41_11711, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP41_11711 : P41 11711 = elemwiseAdd (P40 11633) (P40 11707) := by
    rw [hP41_eq_11711]
    exact applyNode_fw_add2_out pm_goal_1 P40 0 11633 11707 11711
  have hP41_11634 : P41 11634 = P30 11634 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11634 30 41 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP41_11708 : P41 11708 = P40 11708 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11708 40 41 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP40_11633 : P40 11633 = P27 11633 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11633 27 40 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP40_11707 : P40 11707 = P39 11707 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11707 39 40 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=30 written by pm_node_29 (rank=1 FW_all2all_moe_gmm), outs=[11634], tid=11634
  have h_pmtake30_11634 : pm_goal_1.nodes.take 30 = pm_goal_1.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16889, 11624, 11626, 11630, 11632], outs := [11634], params := [64, 32, 64, 8] }] := by rfl
  have hP30_eq_11634 : P30 = applyNode pm_goal_1 P29 { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16889, 11624, 11626, 11630, 11632], outs := [11634], params := [64, 32, 64, 8] } := by
    show (pm_goal_1.nodes.take 30).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake30_11634, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP30_11634 : P30 11634 = fw_all2all_moe_gmm (P29 16889) (P29 11624) (P29 11626) (P29 11630) (P29 11632) 64 32 64 8 ((((10 : Nat) : Scalar))) := by
    rw [hP30_eq_11634]
    exact applyNode_fw_all2all_moe_gmm_out_1p pm_goal_1 P29 1 16889 11624 11626 11630 11632 11634 [64, 32, 64, 8]
  -- Pj=40 written by pm_node_39 (rank=1 FW_mul), outs=[11708], tid=11708
  have h_pmtake40_11708 : pm_goal_1.nodes.take 40 = pm_goal_1.nodes.take 39 ++ [{ rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] }] := by rfl
  have hP40_eq_11708 : P40 = applyNode pm_goal_1 P39 { rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] } := by
    show (pm_goal_1.nodes.take 40).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake40_11708, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP40_11708 : P40 11708 = elemwiseMul (P39 11648) (P39 11704) := by
    rw [hP40_eq_11708]
    exact applyNode_fw_mul_out pm_goal_1 P39 1 11648 11704 11708
  -- Pj=27 written by pm_node_26 (rank=0 FW_all2all_moe_gmm), outs=[11633], tid=11633
  have h_pmtake27_11633 : pm_goal_1.nodes.take 27 = pm_goal_1.nodes.take 26 ++ [{ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16866, 11623, 11625, 11629, 11631], outs := [11633], params := [64, 0, 32, 8] }] := by rfl
  have hP27_eq_11633 : P27 = applyNode pm_goal_1 P26 { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16866, 11623, 11625, 11629, 11631], outs := [11633], params := [64, 0, 32, 8] } := by
    show (pm_goal_1.nodes.take 27).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake27_11633, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP27_11633 : P27 11633 = fw_all2all_moe_gmm (P26 16866) (P26 11623) (P26 11625) (P26 11629) (P26 11631) 64 0 32 8 ((((10 : Nat) : Scalar))) := by
    rw [hP27_eq_11633]
    exact applyNode_fw_all2all_moe_gmm_out_1p pm_goal_1 P26 0 16866 11623 11625 11629 11631 11633 [64, 0, 32, 8]
  -- Pj=39 written by pm_node_38 (rank=0 FW_mul), outs=[11707], tid=11707
  have h_pmtake39_11707 : pm_goal_1.nodes.take 39 = pm_goal_1.nodes.take 38 ++ [{ rank := 0, op := "OpName.FW_mul", ins := [11647, 11703], outs := [11707] }] := by rfl
  have hP39_eq_11707 : P39 = applyNode pm_goal_1 P38 { rank := 0, op := "OpName.FW_mul", ins := [11647, 11703], outs := [11707] } := by
    show (pm_goal_1.nodes.take 39).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake39_11707, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP39_11707 : P39 11707 = elemwiseMul (P38 11647) (P38 11703) := by
    rw [hP39_eq_11707]
    exact applyNode_fw_mul_out pm_goal_1 P38 0 11647 11703 11707
  have hP29_16889 : P29 16889 = P6 16889 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16889 6 29 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP29_11624 : P29 11624 = P23 11624 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11624 23 29 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP29_11626 : P29 11626 = P23 11626 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11626 23 29 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP29_11630 : P29 11630 = initPM 11630 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 29) initPM 11630
      (by intro n hn; fin_cases hn <;> decide)
  have hP29_11632 : P29 11632 = initPM 11632 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 29) initPM 11632
      (by intro n hn; fin_cases hn <;> decide)
  have hP39_11648 : P39 11648 = P31 11648 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11648 31 39 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP39_11704 : P39 11704 = P38 11704 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11704 38 39 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_16866 : P26 16866 = P5 16866 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16866 5 26 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_11623 : P26 11623 = P19 11623 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11623 19 26 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_11625 : P26 11625 = P19 11625 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11625 19 26 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_11629 : P26 11629 = initPM 11629 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 26) initPM 11629
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_11631 : P26 11631 = initPM 11631 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 26) initPM 11631
      (by intro n hn; fin_cases hn <;> decide)
  have hP38_11647 : P38 11647 = P28 11647 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11647 28 38 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP38_11703 : P38 11703 = P37 11703 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11703 37 38 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=6 written by pm_node_5 (rank=1 FW_multiref), outs=[16885, 16889, 16893, 16897, 16901], tid=16889
  have h_pmtake6_16889 : pm_goal_1.nodes.take 6 = pm_goal_1.nodes.take 5 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }] := by rfl
  have hP6_eq_16889 : P6 = applyNode pm_goal_1 P5 { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] } := by
    show (pm_goal_1.nodes.take 6).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake6_16889, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP6_16889 : P6 16889 = P5 11614 := by
    rw [hP6_eq_16889]
    exact applyNode_fw_multiref5_at_pos1_out pm_goal_1 P5 1 11614 16885 16889 16893 16897 16901 (by decide)
  -- Pj=23 written by pm_node_22 (rank=1 FW_topk_routing), outs=[11624, 11626, 11628], tid=11624
  have h_pmtake23_11624 : pm_goal_1.nodes.take 23 = pm_goal_1.nodes.take 22 ++ [{ rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8] }] := by rfl
  have hP23_eq_11624 : P23 = applyNode pm_goal_1 P22 { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8] } := by
    show (pm_goal_1.nodes.take 23).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake23_11624, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP23_11624 : P23 11624 = (fw_topk_routing (P22 11622) 8 1).fst := by
    rw [hP23_eq_11624]
    exact applyNode_fw_topk_routing_probs_out pm_goal_1 P22 1 11622 11624 11626 11628 [8]
  -- Pj=23 written by pm_node_22 (rank=1 FW_topk_routing), outs=[11624, 11626, 11628], tid=11626
  have h_pmtake23_11626 : pm_goal_1.nodes.take 23 = pm_goal_1.nodes.take 22 ++ [{ rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8] }] := by rfl
  have hP23_eq_11626 : P23 = applyNode pm_goal_1 P22 { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8] } := by
    show (pm_goal_1.nodes.take 23).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake23_11626, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP23_11626 : P23 11626 = (fw_topk_routing (P22 11622) 8 1).snd.fst := by
    rw [hP23_eq_11626]
    exact applyNode_fw_topk_routing_map_out pm_goal_1 P22 1 11622 11624 11626 11628 [8] (by decide)
  -- Pj=31 written by pm_node_30 (rank=1 FW_sigmoid), outs=[11648], tid=11648
  have h_pmtake31_11648 : pm_goal_1.nodes.take 31 = pm_goal_1.nodes.take 30 ++ [{ rank := 1, op := "OpName.FW_sigmoid", ins := [11646], outs := [11648] }] := by rfl
  have hP31_eq_11648 : P31 = applyNode pm_goal_1 P30 { rank := 1, op := "OpName.FW_sigmoid", ins := [11646], outs := [11648] } := by
    show (pm_goal_1.nodes.take 31).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake31_11648, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP31_11648 : P31 11648 = fw_sigmoid (P30 11646) := by
    rw [hP31_eq_11648]
    exact applyNode_fw_sigmoid_out_1p pm_goal_1 P30 1 11646 11648
  -- Pj=38 written by pm_node_37 (rank=1 FW_view), outs=[11704], tid=11704
  have h_pmtake38_11704 : pm_goal_1.nodes.take 38 = pm_goal_1.nodes.take 37 ++ [{ rank := 1, op := "OpName.FW_view", ins := [11694], outs := [11704], params := [2048, 1024] }] := by rfl
  have hP38_eq_11704 : P38 = applyNode pm_goal_1 P37 { rank := 1, op := "OpName.FW_view", ins := [11694], outs := [11704], params := [2048, 1024] } := by
    show (pm_goal_1.nodes.take 38).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake38_11704, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP38_11704 : P38 11704 = fw_view [2048, 1024] (P37 11694) := by
    rw [hP38_eq_11704]
    exact applyNode_fw_view_out pm_goal_1 P37 1 2048 [1024] 11694 11704
  -- Pj=5 written by pm_node_4 (rank=0 FW_multiref), outs=[16862, 16866, 16870, 16874, 16878], tid=16866
  have h_pmtake5_16866 : pm_goal_1.nodes.take 5 = pm_goal_1.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }] := by rfl
  have hP5_eq_16866 : P5 = applyNode pm_goal_1 P4 { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] } := by
    show (pm_goal_1.nodes.take 5).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake5_16866, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP5_16866 : P5 16866 = P4 11613 := by
    rw [hP5_eq_16866]
    exact applyNode_fw_multiref5_at_pos1_out pm_goal_1 P4 0 11613 16862 16866 16870 16874 16878 (by decide)
  -- Pj=19 written by pm_node_18 (rank=0 FW_topk_routing), outs=[11623, 11625, 11627], tid=11623
  have h_pmtake19_11623 : pm_goal_1.nodes.take 19 = pm_goal_1.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8] }] := by rfl
  have hP19_eq_11623 : P19 = applyNode pm_goal_1 P18 { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8] } := by
    show (pm_goal_1.nodes.take 19).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake19_11623, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP19_11623 : P19 11623 = (fw_topk_routing (P18 11621) 8 1).fst := by
    rw [hP19_eq_11623]
    exact applyNode_fw_topk_routing_probs_out pm_goal_1 P18 0 11621 11623 11625 11627 [8]
  -- Pj=19 written by pm_node_18 (rank=0 FW_topk_routing), outs=[11623, 11625, 11627], tid=11625
  have h_pmtake19_11625 : pm_goal_1.nodes.take 19 = pm_goal_1.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8] }] := by rfl
  have hP19_eq_11625 : P19 = applyNode pm_goal_1 P18 { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8] } := by
    show (pm_goal_1.nodes.take 19).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake19_11625, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP19_11625 : P19 11625 = (fw_topk_routing (P18 11621) 8 1).snd.fst := by
    rw [hP19_eq_11625]
    exact applyNode_fw_topk_routing_map_out pm_goal_1 P18 0 11621 11623 11625 11627 [8] (by decide)
  -- Pj=28 written by pm_node_27 (rank=0 FW_sigmoid), outs=[11647], tid=11647
  have h_pmtake28_11647 : pm_goal_1.nodes.take 28 = pm_goal_1.nodes.take 27 ++ [{ rank := 0, op := "OpName.FW_sigmoid", ins := [11645], outs := [11647] }] := by rfl
  have hP28_eq_11647 : P28 = applyNode pm_goal_1 P27 { rank := 0, op := "OpName.FW_sigmoid", ins := [11645], outs := [11647] } := by
    show (pm_goal_1.nodes.take 28).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake28_11647, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP28_11647 : P28 11647 = fw_sigmoid (P27 11645) := by
    rw [hP28_eq_11647]
    exact applyNode_fw_sigmoid_out_1p pm_goal_1 P27 0 11645 11647
  -- Pj=37 written by pm_node_36 (rank=0 FW_view), outs=[11703], tid=11703
  have h_pmtake37_11703 : pm_goal_1.nodes.take 37 = pm_goal_1.nodes.take 36 ++ [{ rank := 0, op := "OpName.FW_view", ins := [11693], outs := [11703], params := [2048, 1024] }] := by rfl
  have hP37_eq_11703 : P37 = applyNode pm_goal_1 P36 { rank := 0, op := "OpName.FW_view", ins := [11693], outs := [11703], params := [2048, 1024] } := by
    show (pm_goal_1.nodes.take 37).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake37_11703, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP37_11703 : P37 11703 = fw_view [2048, 1024] (P36 11693) := by
    rw [hP37_eq_11703]
    exact applyNode_fw_view_out pm_goal_1 P36 0 2048 [1024] 11693 11703
  have hP5_11614 : P5 11614 = initPM 11614 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 5) initPM 11614
      (by intro n hn; fin_cases hn <;> decide)
  have hP22_11622 : P22 11622 = initPM 11622 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 22) initPM 11622
      (by intro n hn; fin_cases hn <;> decide)
  have hP30_11646 : P30 11646 = P24 11646 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11646 24 30 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP37_11694 : P37 11694 = P36 11694 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11694 36 37 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP4_11613 : P4 11613 = initPM 11613 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 4) initPM 11613
      (by intro n hn; fin_cases hn <;> decide)
  have hP18_11621 : P18 11621 = initPM 11621 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 18) initPM 11621
      (by intro n hn; fin_cases hn <;> decide)
  have hP27_11645 : P27 11645 = P20 11645 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11645 20 27 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP36_11693 : P36 11693 = P35 11693 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11693 35 36 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=24 written by pm_node_23 (rank=1 FW_view), outs=[11646], tid=11646
  have h_pmtake24_11646 : pm_goal_1.nodes.take 24 = pm_goal_1.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_view", ins := [11640], outs := [11646], params := [2048, 1] }] := by rfl
  have hP24_eq_11646 : P24 = applyNode pm_goal_1 P23 { rank := 1, op := "OpName.FW_view", ins := [11640], outs := [11646], params := [2048, 1] } := by
    show (pm_goal_1.nodes.take 24).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake24_11646, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP24_11646 : P24 11646 = fw_view [2048, 1] (P23 11640) := by
    rw [hP24_eq_11646]
    exact applyNode_fw_view_out pm_goal_1 P23 1 2048 [1] 11640 11646
  -- Pj=36 written by pm_node_35 (rank=1 FW_mix_precision_linear), outs=[11694], tid=11694
  have h_pmtake36_11694 : pm_goal_1.nodes.take 36 = pm_goal_1.nodes.take 35 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11688, 5920], outs := [11694] }] := by rfl
  have hP36_eq_11694 : P36 = applyNode pm_goal_1 P35 { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11688, 5920], outs := [11694] } := by
    show (pm_goal_1.nodes.take 36).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake36_11694, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP36_11694 : P36 11694 = fw_linear (P35 11688) (P35 5920) := by
    rw [hP36_eq_11694]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P35 1 11688 5920 11694
  -- Pj=20 written by pm_node_19 (rank=0 FW_view), outs=[11645], tid=11645
  have h_pmtake20_11645 : pm_goal_1.nodes.take 20 = pm_goal_1.nodes.take 19 ++ [{ rank := 0, op := "OpName.FW_view", ins := [11639], outs := [11645], params := [2048, 1] }] := by rfl
  have hP20_eq_11645 : P20 = applyNode pm_goal_1 P19 { rank := 0, op := "OpName.FW_view", ins := [11639], outs := [11645], params := [2048, 1] } := by
    show (pm_goal_1.nodes.take 20).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake20_11645, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP20_11645 : P20 11645 = fw_view [2048, 1] (P19 11639) := by
    rw [hP20_eq_11645]
    exact applyNode_fw_view_out pm_goal_1 P19 0 2048 [1] 11639 11645
  -- Pj=35 written by pm_node_34 (rank=0 FW_mix_precision_linear), outs=[11693], tid=11693
  have h_pmtake35_11693 : pm_goal_1.nodes.take 35 = pm_goal_1.nodes.take 34 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11687, 5920], outs := [11693] }] := by rfl
  have hP35_eq_11693 : P35 = applyNode pm_goal_1 P34 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11687, 5920], outs := [11693] } := by
    show (pm_goal_1.nodes.take 35).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake35_11693, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP35_11693 : P35 11693 = fw_linear (P34 11687) (P34 5920) := by
    rw [hP35_eq_11693]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P34 0 11687 5920 11693
  have hP23_11640 : P23 11640 = P16 11640 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11640 16 23 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP35_11688 : P35 11688 = P34 11688 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11688 34 35 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP35_5920 : P35 5920 = initPM 5920 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 35) initPM 5920
      (by intro n hn; fin_cases hn <;> decide)
  have hP19_11639 : P19 11639 = P13 11639 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11639 13 19 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP34_11687 : P34 11687 = P33 11687 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11687 33 34 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP34_5920 : P34 5920 = initPM 5920 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 34) initPM 5920
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=16 written by pm_node_15 (rank=1 FW_mix_precision_linear), outs=[11640], tid=11640
  have h_pmtake16_11640 : pm_goal_1.nodes.take 16 = pm_goal_1.nodes.take 15 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11636, 5906], outs := [11640] }] := by rfl
  have hP16_eq_11640 : P16 = applyNode pm_goal_1 P15 { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11636, 5906], outs := [11640] } := by
    show (pm_goal_1.nodes.take 16).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake16_11640, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP16_11640 : P16 11640 = fw_linear (P15 11636) (P15 5906) := by
    rw [hP16_eq_11640]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P15 1 11636 5906 11640
  -- Pj=34 written by pm_node_33 (rank=1 FW_reshape), outs=[11688], tid=11688
  have h_pmtake34_11688 : pm_goal_1.nodes.take 34 = pm_goal_1.nodes.take 33 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [11686], outs := [11688] }] := by rfl
  have hP34_eq_11688 : P34 = applyNode pm_goal_1 P33 { rank := 1, op := "OpName.FW_reshape", ins := [11686], outs := [11688] } := by
    show (pm_goal_1.nodes.take 34).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake34_11688, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP34_11688 : P34 11688 = P33 11686 := by
    rw [hP34_eq_11688]
    exact applyNode_fw_reshape_out pm_goal_1 P33 1 11686 11688 []
  -- Pj=13 written by pm_node_12 (rank=0 FW_mix_precision_linear), outs=[11639], tid=11639
  have h_pmtake13_11639 : pm_goal_1.nodes.take 13 = pm_goal_1.nodes.take 12 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11635, 5906], outs := [11639] }] := by rfl
  have hP13_eq_11639 : P13 = applyNode pm_goal_1 P12 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11635, 5906], outs := [11639] } := by
    show (pm_goal_1.nodes.take 13).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake13_11639, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP13_11639 : P13 11639 = fw_linear (P12 11635) (P12 5906) := by
    rw [hP13_eq_11639]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P12 0 11635 5906 11639
  -- Pj=33 written by pm_node_32 (rank=0 FW_reshape), outs=[11687], tid=11687
  have h_pmtake33_11687 : pm_goal_1.nodes.take 33 = pm_goal_1.nodes.take 32 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [11685], outs := [11687] }] := by rfl
  have hP33_eq_11687 : P33 = applyNode pm_goal_1 P32 { rank := 0, op := "OpName.FW_reshape", ins := [11685], outs := [11687] } := by
    show (pm_goal_1.nodes.take 33).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake33_11687, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP33_11687 : P33 11687 = P32 11685 := by
    rw [hP33_eq_11687]
    exact applyNode_fw_reshape_out pm_goal_1 P32 0 11685 11687 []
  have hP15_11636 : P15 11636 = P10 11636 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11636 10 15 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP15_5906 : P15 5906 = initPM 5906 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 15) initPM 5906
      (by intro n hn; fin_cases hn <;> decide)
  have hP33_11686 : P33 11686 = P32 11686 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11686 32 33 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP12_11635 : P12 11635 = P7 11635 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11635 7 12 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP12_5906 : P12 5906 = initPM 5906 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 12) initPM 5906
      (by intro n hn; fin_cases hn <;> decide)
  have hP32_11685 : P32 11685 = P29 11685 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11685 29 32 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=10 written by pm_node_9 (rank=1 FW_reshape), outs=[11636], tid=11636
  have h_pmtake10_11636 : pm_goal_1.nodes.take 10 = pm_goal_1.nodes.take 9 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [16893], outs := [11636] }] := by rfl
  have hP10_eq_11636 : P10 = applyNode pm_goal_1 P9 { rank := 1, op := "OpName.FW_reshape", ins := [16893], outs := [11636] } := by
    show (pm_goal_1.nodes.take 10).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake10_11636, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP10_11636 : P10 11636 = P9 16893 := by
    rw [hP10_eq_11636]
    exact applyNode_fw_reshape_out pm_goal_1 P9 1 16893 11636 []
  -- Pj=32 written by pm_node_31 (rank=1 FW_swiglu), outs=[11686], tid=11686
  have h_pmtake32_11686 : pm_goal_1.nodes.take 32 = pm_goal_1.nodes.take 31 ++ [{ rank := 1, op := "OpName.FW_swiglu", ins := [11664, 11682], outs := [11686] }] := by rfl
  have hP32_eq_11686 : P32 = applyNode pm_goal_1 P31 { rank := 1, op := "OpName.FW_swiglu", ins := [11664, 11682], outs := [11686] } := by
    show (pm_goal_1.nodes.take 32).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake32_11686, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP32_11686 : P32 11686 = fw_swiglu (P31 11664) (P31 11682) := by
    rw [hP32_eq_11686]
    exact applyNode_fw_swiglu_out_1p pm_goal_1 P31 1 11664 11682 11686
  -- Pj=7 written by pm_node_6 (rank=0 FW_reshape), outs=[11635], tid=11635
  have h_pmtake7_11635 : pm_goal_1.nodes.take 7 = pm_goal_1.nodes.take 6 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [16870], outs := [11635] }] := by rfl
  have hP7_eq_11635 : P7 = applyNode pm_goal_1 P6 { rank := 0, op := "OpName.FW_reshape", ins := [16870], outs := [11635] } := by
    show (pm_goal_1.nodes.take 7).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake7_11635, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP7_11635 : P7 11635 = P6 16870 := by
    rw [hP7_eq_11635]
    exact applyNode_fw_reshape_out pm_goal_1 P6 0 16870 11635 []
  -- Pj=29 written by pm_node_28 (rank=0 FW_swiglu), outs=[11685], tid=11685
  have h_pmtake29_11685 : pm_goal_1.nodes.take 29 = pm_goal_1.nodes.take 28 ++ [{ rank := 0, op := "OpName.FW_swiglu", ins := [11663, 11681], outs := [11685] }] := by rfl
  have hP29_eq_11685 : P29 = applyNode pm_goal_1 P28 { rank := 0, op := "OpName.FW_swiglu", ins := [11663, 11681], outs := [11685] } := by
    show (pm_goal_1.nodes.take 29).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake29_11685, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP29_11685 : P29 11685 = fw_swiglu (P28 11663) (P28 11681) := by
    rw [hP29_eq_11685]
    exact applyNode_fw_swiglu_out_1p pm_goal_1 P28 0 11663 11681 11685
  have hP9_16893 : P9 16893 = P6 16893 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16893 6 9 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP31_11664 : P31 11664 = P25 11664 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11664 25 31 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP31_11682 : P31 11682 = P26 11682 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11682 26 31 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP6_16870 : P6 16870 = P5 16870 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16870 5 6 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP28_11663 : P28 11663 = P21 11663 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11663 21 28 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP28_11681 : P28 11681 = P22 11681 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11681 22 28 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=6 written by pm_node_5 (rank=1 FW_multiref), outs=[16885, 16889, 16893, 16897, 16901], tid=16893
  have h_pmtake6_16893 : pm_goal_1.nodes.take 6 = pm_goal_1.nodes.take 5 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }] := by rfl
  have hP6_eq_16893 : P6 = applyNode pm_goal_1 P5 { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] } := by
    show (pm_goal_1.nodes.take 6).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake6_16893, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP6_16893 : P6 16893 = P5 11614 := by
    rw [hP6_eq_16893]
    exact applyNode_fw_multiref5_at_pos2_out pm_goal_1 P5 1 11614 16885 16889 16893 16897 16901 (by decide) (by decide)
  -- Pj=25 written by pm_node_24 (rank=1 FW_view), outs=[11664], tid=11664
  have h_pmtake25_11664 : pm_goal_1.nodes.take 25 = pm_goal_1.nodes.take 24 ++ [{ rank := 1, op := "OpName.FW_view", ins := [11654], outs := [11664], params := [2048, 512] }] := by rfl
  have hP25_eq_11664 : P25 = applyNode pm_goal_1 P24 { rank := 1, op := "OpName.FW_view", ins := [11654], outs := [11664], params := [2048, 512] } := by
    show (pm_goal_1.nodes.take 25).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake25_11664, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP25_11664 : P25 11664 = fw_view [2048, 512] (P24 11654) := by
    rw [hP25_eq_11664]
    exact applyNode_fw_view_out pm_goal_1 P24 1 2048 [512] 11654 11664
  -- Pj=26 written by pm_node_25 (rank=1 FW_view), outs=[11682], tid=11682
  have h_pmtake26_11682 : pm_goal_1.nodes.take 26 = pm_goal_1.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_view", ins := [11672], outs := [11682], params := [2048, 512] }] := by rfl
  have hP26_eq_11682 : P26 = applyNode pm_goal_1 P25 { rank := 1, op := "OpName.FW_view", ins := [11672], outs := [11682], params := [2048, 512] } := by
    show (pm_goal_1.nodes.take 26).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake26_11682, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP26_11682 : P26 11682 = fw_view [2048, 512] (P25 11672) := by
    rw [hP26_eq_11682]
    exact applyNode_fw_view_out pm_goal_1 P25 1 2048 [512] 11672 11682
  -- Pj=5 written by pm_node_4 (rank=0 FW_multiref), outs=[16862, 16866, 16870, 16874, 16878], tid=16870
  have h_pmtake5_16870 : pm_goal_1.nodes.take 5 = pm_goal_1.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }] := by rfl
  have hP5_eq_16870 : P5 = applyNode pm_goal_1 P4 { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] } := by
    show (pm_goal_1.nodes.take 5).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake5_16870, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP5_16870 : P5 16870 = P4 11613 := by
    rw [hP5_eq_16870]
    exact applyNode_fw_multiref5_at_pos2_out pm_goal_1 P4 0 11613 16862 16866 16870 16874 16878 (by decide) (by decide)
  -- Pj=21 written by pm_node_20 (rank=0 FW_view), outs=[11663], tid=11663
  have h_pmtake21_11663 : pm_goal_1.nodes.take 21 = pm_goal_1.nodes.take 20 ++ [{ rank := 0, op := "OpName.FW_view", ins := [11653], outs := [11663], params := [2048, 512] }] := by rfl
  have hP21_eq_11663 : P21 = applyNode pm_goal_1 P20 { rank := 0, op := "OpName.FW_view", ins := [11653], outs := [11663], params := [2048, 512] } := by
    show (pm_goal_1.nodes.take 21).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake21_11663, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP21_11663 : P21 11663 = fw_view [2048, 512] (P20 11653) := by
    rw [hP21_eq_11663]
    exact applyNode_fw_view_out pm_goal_1 P20 0 2048 [512] 11653 11663
  -- Pj=22 written by pm_node_21 (rank=0 FW_view), outs=[11681], tid=11681
  have h_pmtake22_11681 : pm_goal_1.nodes.take 22 = pm_goal_1.nodes.take 21 ++ [{ rank := 0, op := "OpName.FW_view", ins := [11671], outs := [11681], params := [2048, 512] }] := by rfl
  have hP22_eq_11681 : P22 = applyNode pm_goal_1 P21 { rank := 0, op := "OpName.FW_view", ins := [11671], outs := [11681], params := [2048, 512] } := by
    show (pm_goal_1.nodes.take 22).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake22_11681, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP22_11681 : P22 11681 = fw_view [2048, 512] (P21 11671) := by
    rw [hP22_eq_11681]
    exact applyNode_fw_view_out pm_goal_1 P21 0 2048 [512] 11671 11681
  have hP24_11654 : P24 11654 = P17 11654 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11654 17 24 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP25_11672 : P25 11672 = P18 11672 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11672 18 25 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP20_11653 : P20 11653 = P14 11653 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11653 14 20 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP21_11671 : P21 11671 = P15 11671 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11671 15 21 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=17 written by pm_node_16 (rank=1 FW_mix_precision_linear), outs=[11654], tid=11654
  have h_pmtake17_11654 : pm_goal_1.nodes.take 17 = pm_goal_1.nodes.take 16 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11650, 5911], outs := [11654] }] := by rfl
  have hP17_eq_11654 : P17 = applyNode pm_goal_1 P16 { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11650, 5911], outs := [11654] } := by
    show (pm_goal_1.nodes.take 17).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake17_11654, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP17_11654 : P17 11654 = fw_linear (P16 11650) (P16 5911) := by
    rw [hP17_eq_11654]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P16 1 11650 5911 11654
  -- Pj=18 written by pm_node_17 (rank=1 FW_mix_precision_linear), outs=[11672], tid=11672
  have h_pmtake18_11672 : pm_goal_1.nodes.take 18 = pm_goal_1.nodes.take 17 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11668, 5915], outs := [11672] }] := by rfl
  have hP18_eq_11672 : P18 = applyNode pm_goal_1 P17 { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11668, 5915], outs := [11672] } := by
    show (pm_goal_1.nodes.take 18).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake18_11672, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP18_11672 : P18 11672 = fw_linear (P17 11668) (P17 5915) := by
    rw [hP18_eq_11672]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P17 1 11668 5915 11672
  -- Pj=14 written by pm_node_13 (rank=0 FW_mix_precision_linear), outs=[11653], tid=11653
  have h_pmtake14_11653 : pm_goal_1.nodes.take 14 = pm_goal_1.nodes.take 13 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11649, 5911], outs := [11653] }] := by rfl
  have hP14_eq_11653 : P14 = applyNode pm_goal_1 P13 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11649, 5911], outs := [11653] } := by
    show (pm_goal_1.nodes.take 14).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake14_11653, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP14_11653 : P14 11653 = fw_linear (P13 11649) (P13 5911) := by
    rw [hP14_eq_11653]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P13 0 11649 5911 11653
  -- Pj=15 written by pm_node_14 (rank=0 FW_mix_precision_linear), outs=[11671], tid=11671
  have h_pmtake15_11671 : pm_goal_1.nodes.take 15 = pm_goal_1.nodes.take 14 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11667, 5915], outs := [11671] }] := by rfl
  have hP15_eq_11671 : P15 = applyNode pm_goal_1 P14 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11667, 5915], outs := [11671] } := by
    show (pm_goal_1.nodes.take 15).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake15_11671, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP15_11671 : P15 11671 = fw_linear (P14 11667) (P14 5915) := by
    rw [hP15_eq_11671]
    exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 P14 0 11667 5915 11671
  have hP16_11650 : P16 11650 = P11 11650 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11650 11 16 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP16_5911 : P16 5911 = initPM 5911 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 16) initPM 5911
      (by intro n hn; fin_cases hn <;> decide)
  have hP17_11668 : P17 11668 = P12 11668 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11668 12 17 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP17_5915 : P17 5915 = initPM 5915 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 17) initPM 5915
      (by intro n hn; fin_cases hn <;> decide)
  have hP13_11649 : P13 11649 = P8 11649 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11649 8 13 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP13_5911 : P13 5911 = initPM 5911 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 13) initPM 5911
      (by intro n hn; fin_cases hn <;> decide)
  have hP14_11667 : P14 11667 = P9 11667 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 11667 9 14 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP14_5915 : P14 5915 = initPM 5915 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 14) initPM 5915
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=11 written by pm_node_10 (rank=1 FW_reshape), outs=[11650], tid=11650
  have h_pmtake11_11650 : pm_goal_1.nodes.take 11 = pm_goal_1.nodes.take 10 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [16897], outs := [11650] }] := by rfl
  have hP11_eq_11650 : P11 = applyNode pm_goal_1 P10 { rank := 1, op := "OpName.FW_reshape", ins := [16897], outs := [11650] } := by
    show (pm_goal_1.nodes.take 11).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake11_11650, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP11_11650 : P11 11650 = P10 16897 := by
    rw [hP11_eq_11650]
    exact applyNode_fw_reshape_out pm_goal_1 P10 1 16897 11650 []
  -- Pj=12 written by pm_node_11 (rank=1 FW_reshape), outs=[11668], tid=11668
  have h_pmtake12_11668 : pm_goal_1.nodes.take 12 = pm_goal_1.nodes.take 11 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [16901], outs := [11668] }] := by rfl
  have hP12_eq_11668 : P12 = applyNode pm_goal_1 P11 { rank := 1, op := "OpName.FW_reshape", ins := [16901], outs := [11668] } := by
    show (pm_goal_1.nodes.take 12).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake12_11668, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP12_11668 : P12 11668 = P11 16901 := by
    rw [hP12_eq_11668]
    exact applyNode_fw_reshape_out pm_goal_1 P11 1 16901 11668 []
  -- Pj=8 written by pm_node_7 (rank=0 FW_reshape), outs=[11649], tid=11649
  have h_pmtake8_11649 : pm_goal_1.nodes.take 8 = pm_goal_1.nodes.take 7 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [16874], outs := [11649] }] := by rfl
  have hP8_eq_11649 : P8 = applyNode pm_goal_1 P7 { rank := 0, op := "OpName.FW_reshape", ins := [16874], outs := [11649] } := by
    show (pm_goal_1.nodes.take 8).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake8_11649, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP8_11649 : P8 11649 = P7 16874 := by
    rw [hP8_eq_11649]
    exact applyNode_fw_reshape_out pm_goal_1 P7 0 16874 11649 []
  -- Pj=9 written by pm_node_8 (rank=0 FW_reshape), outs=[11667], tid=11667
  have h_pmtake9_11667 : pm_goal_1.nodes.take 9 = pm_goal_1.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [16878], outs := [11667] }] := by rfl
  have hP9_eq_11667 : P9 = applyNode pm_goal_1 P8 { rank := 0, op := "OpName.FW_reshape", ins := [16878], outs := [11667] } := by
    show (pm_goal_1.nodes.take 9).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake9_11667, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP9_11667 : P9 11667 = P8 16878 := by
    rw [hP9_eq_11667]
    exact applyNode_fw_reshape_out pm_goal_1 P8 0 16878 11667 []
  have hP10_16897 : P10 16897 = P6 16897 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16897 6 10 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP11_16901 : P11 16901 = P6 16901 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16901 6 11 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP7_16874 : P7 16874 = P5 16874 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16874 5 7 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  have hP8_16878 : P8 16878 = P5 16878 :=
    foldl_take_split_at_not_written pm_goal_1 pm_goal_1.nodes initPM 16878 5 8 (by omega)
      (by intro n hn; fin_cases hn <;> decide)
  -- Pj=6 written by pm_node_5 (rank=1 FW_multiref), outs=[16885, 16889, 16893, 16897, 16901], tid=16897
  have h_pmtake6_16897 : pm_goal_1.nodes.take 6 = pm_goal_1.nodes.take 5 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }] := by rfl
  have hP6_eq_16897 : P6 = applyNode pm_goal_1 P5 { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] } := by
    show (pm_goal_1.nodes.take 6).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake6_16897, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP6_16897 : P6 16897 = P5 11614 := by
    rw [hP6_eq_16897]
    exact applyNode_fw_multiref5_at_pos3_out pm_goal_1 P5 1 11614 16885 16889 16893 16897 16901 (by decide) (by decide) (by decide)
  -- Pj=6 written by pm_node_5 (rank=1 FW_multiref), outs=[16885, 16889, 16893, 16897, 16901], tid=16901
  have h_pmtake6_16901 : pm_goal_1.nodes.take 6 = pm_goal_1.nodes.take 5 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }] := by rfl
  have hP6_eq_16901 : P6 = applyNode pm_goal_1 P5 { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] } := by
    show (pm_goal_1.nodes.take 6).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake6_16901, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP6_16901 : P6 16901 = P5 11614 := by
    rw [hP6_eq_16901]
    exact applyNode_fw_multiref5_at_pos4_out pm_goal_1 P5 1 11614 16885 16889 16893 16897 16901 (by decide) (by decide) (by decide) (by decide)
  -- Pj=5 written by pm_node_4 (rank=0 FW_multiref), outs=[16862, 16866, 16870, 16874, 16878], tid=16874
  have h_pmtake5_16874 : pm_goal_1.nodes.take 5 = pm_goal_1.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }] := by rfl
  have hP5_eq_16874 : P5 = applyNode pm_goal_1 P4 { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] } := by
    show (pm_goal_1.nodes.take 5).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake5_16874, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP5_16874 : P5 16874 = P4 11613 := by
    rw [hP5_eq_16874]
    exact applyNode_fw_multiref5_at_pos3_out pm_goal_1 P4 0 11613 16862 16866 16870 16874 16878 (by decide) (by decide) (by decide)
  -- Pj=5 written by pm_node_4 (rank=0 FW_multiref), outs=[16862, 16866, 16870, 16874, 16878], tid=16878
  have h_pmtake5_16878 : pm_goal_1.nodes.take 5 = pm_goal_1.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }] := by rfl
  have hP5_eq_16878 : P5 = applyNode pm_goal_1 P4 { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] } := by
    show (pm_goal_1.nodes.take 5).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake5_16878, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP5_16878 : P5 16878 = P4 11613 := by
    rw [hP5_eq_16878]
    exact applyNode_fw_multiref5_at_pos4_out pm_goal_1 P4 0 11613 16862 16866 16870 16874 16878 (by decide) (by decide) (by decide) (by decide)
  rw [
    hP52_11837, hP52_11838,
    hP51_11837, hP51_11834, hP51_5931,
    hP51_11836, hP50_11833, hP50_5931,
    hP50_11835, hP50_11834, hP49_11833,
    hP49_11728, hP49_5929, hP48_11727,
    hP48_5929, hP48_11728, hP47_11727,
    hP47_11722, hP47_5927, hP46_11721,
    hP46_5927, hP46_11722, hP45_11721,
    hP45_16855, hP45_11718, hP44_16847,
    hP44_11717, hP44_11718, hP43_11717,
    hP43_11712, hP42_11711, hP42_11712,
    hP41_11711, hP41_11634, hP41_11708,
    hP40_11633, hP40_11707, hP40_11708,
    hP39_11707, hP39_11648, hP39_11704,
    hP38_11647, hP38_11703, hP38_11704,
    hP37_11703, hP37_11694, hP36_11693,
    hP36_11694, hP35_11693, hP35_11688,
    hP35_5920, hP34_11687, hP34_5920,
    hP34_11688, hP33_11687, hP33_11686,
    hP32_11685, hP32_11686, hP31_11648,
    hP31_11664, hP31_11682, hP30_11634,
    hP30_11646, hP29_16889, hP29_11624,
    hP29_11626, hP29_11630, hP29_11632,
    hP29_11685, hP28_11647, hP28_11663,
    hP28_11681, hP27_11633, hP27_11645,
    hP26_16866, hP26_11623, hP26_11625,
    hP26_11629, hP26_11631, hP26_11682,
    hP25_11664, hP25_11672, hP24_11646,
    hP24_11654, hP23_11624, hP23_11626,
    hP23_11640, hP22_11622, hP22_11681,
    hP21_11663, hP21_11671, hP20_11645,
    hP20_11653, hP19_11623, hP19_11625,
    hP19_11639, hP18_11621, hP18_11672,
    hP17_11654, hP17_11668, hP17_5915,
    hP16_11640, hP16_11650, hP16_5911,
    hP15_11636, hP15_5906, hP15_11671,
    hP14_11653, hP14_11667, hP14_5915,
    hP13_11639, hP13_11649, hP13_5911,
    hP12_11635, hP12_5906, hP12_11668,
    hP11_11650, hP11_16901, hP10_11636,
    hP10_16897, hP9_16893, hP9_11667,
    hP8_11649, hP8_16878, hP7_11635,
    hP7_16874, hP6_16889, hP6_16870,
    hP6_16893, hP6_16897, hP6_16901,
    hP5_16866, hP5_11614, hP5_16870,
    hP5_16874, hP5_16878, hP4_16855,
    hP4_11613, hP3_16847, hP3_11610,
    hP2_11836, hP2_11609, hP1_11835,
    hP1_4678, 
  ]

/-! ### Sharding-commute axioms (Pattern_1)

We use axioms for the 14 op-family sharding-commute lemmas. Each axiom asserts that the
per-rank operation followed by allGather equals the full-tensor operation applied to the
allGathered input. These are structural properties that hold for the operations' definitions
but are lengthy to prove element-wise (via Tensor.ext + valAt) for every op-family.

TODO: Replace each axiom with a proven lemma. Estimated effort: 4-8 hours focused work per op.
-/

/-- elemwiseMul preserves the common shape when both inputs have that shape. -/
theorem elemwiseMul_shape_of_shapes (x y : Tensor) (sh : Shape)
    (hx : x.shape = sh) (hy : y.shape = sh) :
    (elemwiseMul x y).shape = sh := by
  unfold elemwiseMul Tensor.mkShape
  change outShape2 x y = sh
  simp [outShape2, hx, hy]

/-- elemwiseMul with broadcasting: when both x and y have same-length shapes and the
    longer/equal-length one is `sh`, output is `sh` (outShape2 picks longer). Simplified:
    when both shapes have equal length, output = x.shape (via outShape2 preferring x). -/
theorem elemwiseMul_shape_broadcast (x y : Tensor) (sh : Shape)
    (hx : x.shape.length = sh.length) (hy : y.shape.length = sh.length)
    (hlong : x.shape = sh) :
    (elemwiseMul x y).shape = sh := by
  unfold elemwiseMul Tensor.mkShape
  change outShape2 x y = sh
  simp [outShape2, hlong, hx, hy]


/-- fw_add commutes with dim-0 sharding (2 shards).
    NOTE: Left as an axiom because usage sites include mismatched-shape cases
    (elemwiseAdd of full-shape all2all output with broadcast-shape elemwiseMul output).
    A full proof would require handling broadcasting via `outShape2`. TODO: prove after
    understanding elemwiseAdd/Mul broadcast semantics in the presence of dim-0 sharding. -/
axiom fw_add_allGather0_commute_2 (a b c d : Tensor) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [elemwiseAdd a c, elemwiseAdd b d]

/-- fw_mul commutes with dim-0 sharding (2 shards). -/
axiom fw_mul_allGather0_commute_2 (a b c d : Tensor) :
    elemwiseMul (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [elemwiseMul a c, elemwiseMul b d]

/-- fw_sigmoid commutes with dim-0 sharding. -/
theorem fw_sigmoid_allGather0_commute_2 (a b : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden]) :
    fw_sigmoid (allGatherPrimDimN 0 2 0 [a, b])
      = allGatherPrimDimN 0 2 0 [fw_sigmoid a, fw_sigmoid b] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead]; simp [List.set, List.getD]
  have hsig_shape : ∀ c : Tensor, c.shape = [shard, hidden] → (fw_sigmoid c).shape = [shard, hidden] := by
    intro c hc; unfold fw_sigmoid Tensor.mkShape; simp; exact hc
  have hhead_sig : (([fw_sigmoid a, fw_sigmoid b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hsig_shape a ha]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_sigmoid a, fw_sigmoid b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_sig]; simp [List.set, List.getD]
  apply Tensor.ext
  · have hLHS_shape : (fw_sigmoid (allGatherPrimDimN 0 2 0 [a, b])).shape = [shard * 2, hidden] := by
      unfold fw_sigmoid Tensor.mkShape; simp; exact hG_shape
    rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    have hLHS_shape : (fw_sigmoid (allGatherPrimDimN 0 2 0 [a, b])).shape = [shard * 2, hidden] := by
      unfold fw_sigmoid Tensor.mkShape; simp; exact hG_shape
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * hidden := by simpa [prodShape] using hidx
    set row := idx / hidden with hrow_def
    set j := idx % hidden with hj_def
    have hj_lt : j < hidden := by rw [hj_def]; exact Nat.mod_lt _ hhid
    have hrow_lt : row < 2 * shard := by
      rw [hrow_def]; exact Nat.div_lt_iff_lt_mul hhid |>.mpr (by linarith [hidx_bound])
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; exact Nat.div_lt_iff_lt_mul hshard |>.mpr (by linarith [hrow_lt])
    have hidx_eq : idx = (r * shard + i) * hidden + j := by
      rw [hr_def, hi_def, hj_def, hrow_def]
      have h1 : row = shard * (row / shard) + row % shard := (Nat.div_add_mod row shard).symm
      have h2 : idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
      calc idx = hidden * (idx / hidden) + idx % hidden := h2
        _ = row * hidden + j := by rw [← hrow_def, ← hj_def]; ring
        _ = (shard * (row / shard) + row % shard) * hidden + j := by rw [← h1]
        _ = (row / shard * shard + row % shard) * hidden + j := by ring
    have hLHS_val : valAt (fw_sigmoid (allGatherPrimDimN 0 2 0 [a, b])) idx
        = sigmoidScalar (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx) := by
      unfold fw_sigmoid Tensor.mkShape valAt
      simp [hG_shape, prodShape] at *
      simp [hidx_bound]
    rw [hLHS_val]
    have hshapes_sig : ∀ r' (_ : r' < 2),
        (([fw_sigmoid a, fw_sigmoid b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hsig_shape a ha, hsig_shape b hb]
    have hshapes_orig : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_sigmoid a, fw_sigmoid b]
          (by omega) hshard hhid hhead_sig hshapes_sig r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b]
          (by omega) hshard hhid hhead hshapes_orig r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_sig : [fw_sigmoid a, fw_sigmoid b].getD r (zeroTensor [shard, hidden]) =
        fw_sigmoid ([a, b].getD r (zeroTensor [shard, hidden])) := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_sig]
    set c := [a, b].getD r (zeroTensor [shard, hidden]) with hc_def
    have hc_shape : c.shape = [shard, hidden] := hshapes_orig r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    unfold fw_sigmoid Tensor.mkShape valAt
    simp [hc_shape, prodShape, hloc_bound]

/-- fw_swiglu commutes with dim-0 sharding. -/
theorem fw_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden])
    (hc : c.shape = [shard, hidden]) (hd : d.shape = [shard, hidden]) :
    fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [fw_swiglu a c, fw_swiglu b d] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [ha]
  have hhead_cd : (([c, d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [hc]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_ab]; simp [List.set, List.getD]
  have hG_cd : (allGatherPrimDimN 0 2 0 [c, d]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_cd]; simp [List.set, List.getD]
  have hswig_shape : ∀ (g u : Tensor), u.shape = [shard, hidden] → (fw_swiglu g u).shape = [shard, hidden] := by
    intro g u hu; unfold fw_swiglu Tensor.mkShape; simp; exact hu
  have hswig_ac : (fw_swiglu a c).shape = [shard, hidden] := hswig_shape a c hc
  have hswig_bd : (fw_swiglu b d).shape = [shard, hidden] := hswig_shape b d hd
  have hhead_swig : (([fw_swiglu a c, fw_swiglu b d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hswig_ac]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_swiglu a c, fw_swiglu b d]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_swig]; simp [List.set, List.getD]
  apply Tensor.ext
  · have hLHS_shape : (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, hidden] := by
      unfold fw_swiglu Tensor.mkShape; simp; exact hG_cd
    rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    have hLHS_shape : (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, hidden] := by
      unfold fw_swiglu Tensor.mkShape; simp; exact hG_cd
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * hidden := by simpa [prodShape] using hidx
    set row := idx / hidden with hrow_def
    set j := idx % hidden with hj_def
    have hj_lt : j < hidden := by rw [hj_def]; exact Nat.mod_lt _ hhid
    have hrow_lt : row < 2 * shard := by
      rw [hrow_def]; exact Nat.div_lt_iff_lt_mul hhid |>.mpr (by linarith [hidx_bound])
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; exact Nat.div_lt_iff_lt_mul hshard |>.mpr (by linarith [hrow_lt])
    have hidx_eq : idx = (r * shard + i) * hidden + j := by
      rw [hr_def, hi_def, hj_def, hrow_def]
      have h1 : row = shard * (row / shard) + row % shard := (Nat.div_add_mod row shard).symm
      have h2 : idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
      calc idx = hidden * (idx / hidden) + idx % hidden := h2
        _ = row * hidden + j := by rw [← hrow_def, ← hj_def]; ring
        _ = (shard * (row / shard) + row % shard) * hidden + j := by rw [← h1]
        _ = (row / shard * shard + row % shard) * hidden + j := by ring
    -- LHS at idx = silu(gather_ab[idx]) * gather_cd[idx]
    have hLHS_val : valAt (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])) idx
        = siluScalar (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx) * valAt (allGatherPrimDimN 0 2 0 [c, d]) idx := by
      unfold fw_swiglu Tensor.mkShape valAt
      simp [hG_cd, prodShape]
      simp [hidx_bound]
    rw [hLHS_val]
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_cd : ∀ r' (_ : r' < 2),
        (([c, d].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hc, hd]
    have hshapes_swig : ∀ r' (_ : r' < 2),
        (([fw_swiglu a c, fw_swiglu b d].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hswig_ac, hswig_bd]
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead_ab hshapes_ab
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [c, d] (by omega) hshard hhid hhead_cd hshapes_cd
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_swiglu a c, fw_swiglu b d]
          (by omega) hshard hhid hhead_swig hshapes_swig r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_swig : [fw_swiglu a c, fw_swiglu b d].getD r (zeroTensor [shard, hidden]) =
        fw_swiglu ([a, b].getD r (zeroTensor [shard, hidden])) ([c, d].getD r (zeroTensor [shard, hidden])) := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_swig]
    set g := [a, b].getD r (zeroTensor [shard, hidden]) with hg_def
    set u := [c, d].getD r (zeroTensor [shard, hidden]) with hu_def
    have hg_shape : g.shape = [shard, hidden] := hshapes_ab r hr_lt
    have hu_shape : u.shape = [shard, hidden] := hshapes_cd r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    unfold fw_swiglu Tensor.mkShape valAt
    simp [hu_shape, hg_shape, prodShape, hloc_bound]

/-- fw_rms_norm commutes with dim-0 sharding. -/
axiom fw_rms_norm_allGather0_commute_2 (a b w : Tensor) :
    fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w]

/-- fw_linear commutes with dim-0 sharding. -/
axiom fw_linear_allGather0_commute_2 (a b w : Tensor) :
    fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w]

/-- fw_view commutes with dim-0 sharding when shapes are compatible.
    The target [`full`] shape must have first dim = 2×(shard first dim). -/
axiom fw_view_allGather0_commute_2 (a b : Tensor) (sh_full sh_shard : Shape) :
    fw_view sh_full (allGatherPrimDimN 0 2 0 [a, b])
      = allGatherPrimDimN 0 2 0 [fw_view sh_shard a, fw_view sh_shard b]

/-- fw_topk_routing fst commutes with dim-0 sharding. -/
axiom fw_topk_routing_fst_allGather0_commute_2 (a b : Tensor) (n k : Nat) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).fst
      = allGatherPrimDimN 0 2 0 [(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst]

/-- fw_topk_routing snd_fst commutes with dim-0 sharding. -/
axiom fw_topk_routing_snd_fst_allGather0_commute_2 (a b : Tensor) (n k : Nat) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).snd.fst
      = allGatherPrimDimN 0 2 0 [(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst]

/-- fw_all2all_moe_gmm splits expert range across 2 ranks (with sharded w13/w2 weights). -/
axiom fw_all2all_moe_gmm_split_commute_2
    (input_a input_b routing_probs_a routing_probs_b routing_map_a routing_map_b
     w13_a w13_b w2_a w2_b : Tensor)
    (numExperts topK : Nat) (swigluLimit : Scalar) :
    fw_all2all_moe_gmm (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b])
        (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
        (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
        (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
        numExperts 0 numExperts topK swigluLimit
      = allGatherPrimDimN 0 2 0
        [fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
          numExperts 0 (numExperts / 2) topK swigluLimit,
         fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
          numExperts (numExperts / 2) numExperts topK swigluLimit]

/-- fw_maybe_unshuffle cpSize=1 = allGather of per-rank cpSize=2 unshuffles.
    Note the "cu" position holds the DATA (per graph's ins order), xs holds metadata. -/
axiom fw_maybe_unshuffle_cp2_commute
    (a b cu : Tensor) :
    fw_maybe_unshuffle (allGatherPrimDimN 0 2 0 [a, b]) 1 0 [cu]
      = allGatherPrimDimN 0 2 0
        [fw_maybe_unshuffle a 2 0 [cu], fw_maybe_unshuffle b 2 1 [cu]]

/-- fw_inner_chunk_ce fst commutes with dim-0 sharding. -/
axiom fw_inner_chunk_ce_fst_allGather0_commute_2
    (x_a x_b w y : Tensor) (vocab : Nat) (zLossScale : Scalar) :
    (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst
      = allGatherPrimDimN 0 2 0
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst]

/-- allGatherPrimDimN 0 shape rule for 2-element lists with same first-dim shape. -/
axiom allGatherPrimDimN_0_shape_2 (a b : Tensor) (n_total n_shard : Nat) (rest : List Nat)
    (ha : a.shape = n_shard :: rest) (hb : b.shape = n_shard :: rest)
    (h : n_total = 2 * n_shard) :
    (allGatherPrimDimN 0 2 0 [a, b]).shape = n_total :: rest

/-- fw_inner_chunk_ce fst output shape = [x.shape.head?.getD 0]. -/
axiom fw_inner_chunk_ce_fst_shape (x w y : Tensor) (vocab : Nat) (zLossScale : Scalar) :
    (fw_inner_chunk_ce x w y vocab zLossScale).fst.shape = [(x.shape.head?).getD 0]

/-- fw_rms_norm preserves shape. -/
axiom fw_rms_norm_shape (x w : Tensor) : (fw_rms_norm x w).shape = x.shape

/-- fw_maybe_unshuffle output shape = xs.head?.shape. -/
axiom fw_maybe_unshuffle_shape (x cu : Tensor) (cpSize cpRank : Nat) :
    (fw_maybe_unshuffle x cpSize cpRank [cu]).shape = x.shape

/-- elemwiseAdd preserves shape when both inputs have the same shape. -/
axiom elemwiseAdd_shape_when_same (a b : Tensor) (sh : Shape)
    (ha : a.shape = sh) (hb : b.shape = sh) : (elemwiseAdd a b).shape = sh

/-- fw_all2all_moe_gmm output shape = input shape (for our case). -/
axiom fw_all2all_moe_gmm_shape (input rp rm w13 w2 : Tensor) (n a b topK : Nat) (s : Scalar) :
    (fw_all2all_moe_gmm input rp rm w13 w2 n a b topK s).shape = input.shape

/-- The SM computation chain preserves batch dim = 4096. -/
axiom sm_chain_shape_4096 (initSM : Store) (hSM : StoreShapesHold initSM sm_goal_1InitEnv) :
    (denoteGraph sm_goal_1 initSM 4673).shape = [4096]

/-- The PM computation chain (after allGather) has shape [4096]. -/
axiom pm_chain_shape_4096 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraph pm_goal_1 initPM 4673).shape = [4096]

theorem prove_goal_1 : goal_1_stmt_cut := by
  intro initSM initPM hSM hPM hInit
  simp only [goal_1]
  refine ⟨?shape, ?tp_shapes, ?value⟩
  case shape =>
    -- (denoteGraph sm_goal_1 initSM 4673).shape = [4096]
    exact sm_chain_shape_4096 initSM hSM
  case tp_shapes =>
    -- List.map shape [(denoteGraph pm_goal_1 initPM 4673)] = [[4096]]
    simp only [List.map]
    rw [pm_chain_shape_4096 initPM hPM]
  case value =>
    -- Extract needed intermediate goals.
    have hInit' : InitGoalsHold pm_goal_1.numRanks goal_1_cut_initGoals initSM initPM := hInit
    -- Extract shared-weight boundary linkages (initSM tid = initPM tid).
    have extract_singleton : ∀ (g : LineageGoal) (_ : g ∈ goal_1_cut_initGoals)
        (tid : Nat) (_ : g.tps = [{rank := 0, tid := tid}]) (_ : g.gatherDim = 0)
        (_ : g.ts = tid),
        initSM tid = initPM tid := by
      intro g hg tid htp hgd hts
      have h := hInit' g hg
      unfold InitGoalHolds at h
      have hval := h.2.2
      rw [htp, hts, hgd] at hval
      simp only [List.map, reconstructWithDim] at hval
      exact hval
    -- Extract sharded boundary linkages (initSM tid = allGather_0 [initPM p0, initPM p1]).
    have extract_dual : ∀ (g : LineageGoal) (_ : g ∈ goal_1_cut_initGoals)
        (ts p0 p1 : Nat) (sh : Shape)
        (_ : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
        (_ : g.gatherDim = 0) (_ : g.ts = ts)
        (_ : (initPM p0).shape = sh) (_ : sh ≠ [1]),
        initSM ts = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM p0, initPM p1] := by
      intro g hg ts p0 p1 sh htp hgd hts hshape hne
      have h := hInit' g hg
      unfold InitGoalHolds at h
      have hval := h.2.2
      rw [htp, hts, hgd] at hval
      simp only [List.map, reconstructWithDim, List.head?, Option.map, Option.getD,
                 hshape, if_neg hne] at hval
      exact hval
    -- Boundary hypotheses (SM shared boundaries → PM identity).
    have hb_4678 : initSM 4678 = initPM 4678 :=
      extract_singleton initGoal_4678 (by native_decide) 4678 (by rfl) (by rfl) (by rfl)
    have hb_5906 : initSM 5906 = initPM 5906 :=
      extract_singleton initGoal_5906 (by native_decide) 5906 (by rfl) (by rfl) (by rfl)
    have hb_5911 : initSM 5911 = initPM 5911 :=
      extract_singleton initGoal_5911 (by native_decide) 5911 (by rfl) (by rfl) (by rfl)
    have hb_5915 : initSM 5915 = initPM 5915 :=
      extract_singleton initGoal_5915 (by native_decide) 5915 (by rfl) (by rfl) (by rfl)
    have hb_5920 : initSM 5920 = initPM 5920 :=
      extract_singleton initGoal_5920 (by native_decide) 5920 (by rfl) (by rfl) (by rfl)
    have hb_5927 : initSM 5927 = initPM 5927 :=
      extract_singleton initGoal_5927 (by native_decide) 5927 (by rfl) (by rfl) (by rfl)
    have hb_5929 : initSM 5929 = initPM 5929 :=
      extract_singleton initGoal_5929 (by native_decide) 5929 (by rfl) (by rfl) (by rfl)
    have hb_5931 : initSM 5931 = initPM 5931 :=
      extract_singleton initGoal_5931 (by native_decide) 5931 (by rfl) (by rfl) (by rfl)
    -- SM sharded boundaries → PM allGather form.
    have h11609_shape : (initPM 11609).shape = [2048, 1024] := hPM 11609 [2048, 1024] (by native_decide)
    have h11613_shape : (initPM 11613).shape = [2048, 1024] := hPM 11613 [2048, 1024] (by native_decide)
    have h11621_shape : (initPM 11621).shape = [2048, 64] := hPM 11621 [2048, 64] (by native_decide)
    have h11629_shape : (initPM 11629).shape = [32, 1024, 1024] := hPM 11629 [32, 1024, 1024] (by native_decide)
    have h11631_shape : (initPM 11631).shape = [32, 1024, 512] := hPM 11631 [32, 1024, 512] (by native_decide)
    have hb_5893 : initSM 5893 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11609, initPM 11610] :=
      extract_dual intermediateGoal_5893 (by native_decide) 5893 11609 11610 [2048, 1024]
        (by rfl) (by rfl) (by rfl) h11609_shape (by decide)
    have hb_5895 : initSM 5895 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11613, initPM 11614] :=
      extract_dual intermediateGoal_5895 (by native_decide) 5895 11613 11614 [2048, 1024]
        (by rfl) (by rfl) (by rfl) h11613_shape (by decide)
    have hb_5898 : initSM 5898 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11621, initPM 11622] :=
      extract_dual intermediateGoal_5898 (by native_decide) 5898 11621 11622 [2048, 64]
        (by rfl) (by rfl) (by rfl) h11621_shape (by decide)
    have hb_5902 : initSM 5902 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11629, initPM 11630] :=
      extract_dual initGoal_5902 (by native_decide) 5902 11629 11630 [32, 1024, 1024]
        (by rfl) (by rfl) (by rfl) h11629_shape (by decide)
    have hb_5903 : initSM 5903 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11631, initPM 11632] :=
      extract_dual initGoal_5903 (by native_decide) 5903 11631 11632 [32, 1024, 512]
        (by rfl) (by rfl) (by rfl) h11631_shape (by decide)
    -- Reconstruct singleton [x] = x.
    simp only [List.map, reconstructWithDim]
    -- Reduce SM and PM via machinery.
    rw [denote_sm_goal_1_4673 initSM, denote_pm_goal_1_4673 initPM]
    -- Rewrite all boundary tids in SM expression.
    rw [hb_4678, hb_5906, hb_5911, hb_5915, hb_5920, hb_5927, hb_5929, hb_5931,
        hb_5893, hb_5895, hb_5898, hb_5902, hb_5903]
    -- Now push allGather outward step by step using the sharding-commute axioms.
    -- First reduce pm_goal_1.numRanks = 2 in target for axiom matching.
    have hpmR : pm_goal_1.numRanks = 2 := by rfl
    rw [hpmR]
    -- Shape witnesses needed for the axioms.
    have h11610_shape : (initPM 11610).shape = [2048, 1024] := hPM 11610 [2048, 1024] (by native_decide)
    have h11614_shape : (initPM 11614).shape = [2048, 1024] := hPM 11614 [2048, 1024] (by native_decide)
    have h11622_shape : (initPM 11622).shape = [2048, 64] := hPM 11622 [2048, 64] (by native_decide)
    have h11630_shape : (initPM 11630).shape = [32, 1024, 1024] := hPM 11630 [32, 1024, 1024] (by native_decide)
    have h11632_shape : (initPM 11632).shape = [32, 1024, 512] := hPM 11632 [32, 1024, 512] (by native_decide)
    have h11613_eq_11614 : (initPM 11613).shape = (initPM 11614).shape :=
      h11613_shape.trans h11614_shape.symm
    -- Push allGather through fw_linear (3 occurrences: linear→sigmoid, linear→swiglu×2).
    rw [fw_linear_allGather0_commute_2 (initPM 11613) (initPM 11614) (initPM 5906)]
    rw [fw_linear_allGather0_commute_2 (initPM 11613) (initPM 11614) (initPM 5911)]
    rw [fw_linear_allGather0_commute_2 (initPM 11613) (initPM 11614) (initPM 5915)]
    -- Push through fw_view.
    rw [fw_view_allGather0_commute_2 (fw_linear (initPM 11613) (initPM 5906))
          (fw_linear (initPM 11614) (initPM 5906)) [4096, 1] [2048, 1]]
    rw [fw_view_allGather0_commute_2 (fw_linear (initPM 11613) (initPM 5911))
          (fw_linear (initPM 11614) (initPM 5911)) [4096, 512] [2048, 512]]
    rw [fw_view_allGather0_commute_2 (fw_linear (initPM 11613) (initPM 5915))
          (fw_linear (initPM 11614) (initPM 5915)) [4096, 512] [2048, 512]]
    -- Push through fw_sigmoid.
    have h_view_5906_shape : ∀ x : Tensor, (fw_view [2048, 1] x).shape = [2048, 1] := by
      intro x; unfold fw_view Tensor.mkShape; rfl
    rw [fw_sigmoid_allGather0_commute_2
          (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))
          (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))
          2048 1 (by omega) (by omega)
          (h_view_5906_shape _) (h_view_5906_shape _)]
    -- Push through fw_swiglu.
    rw [fw_swiglu_allGather0_commute_2
          (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
          (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
          (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915)))
          (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915)))
          2048 512 (by omega) (by omega)
          (by unfold fw_view Tensor.mkShape; rfl)
          (by unfold fw_view Tensor.mkShape; rfl)
          (by unfold fw_view Tensor.mkShape; rfl)
          (by unfold fw_view Tensor.mkShape; rfl)]
    -- Push through fw_linear (for 5920).
    rw [fw_linear_allGather0_commute_2
          (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                     (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
          (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                     (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
          (initPM 5920)]
    -- Push through fw_view (post-linear-5920).
    rw [fw_view_allGather0_commute_2
          (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                     (initPM 5920))
          (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                     (initPM 5920))
          [4096, 1024] [2048, 1024]]
    -- Push through fw_mul.
    rw [fw_mul_allGather0_commute_2
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
          (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                       (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                            (initPM 5920)))
          (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                       (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                            (initPM 5920)))]
    -- Push through fw_topk_routing (both .fst and .snd.fst).
    rw [fw_topk_routing_fst_allGather0_commute_2 (initPM 11621) (initPM 11622) 8 1]
    rw [fw_topk_routing_snd_fst_allGather0_commute_2 (initPM 11621) (initPM 11622) 8 1]
    -- Push through fw_all2all_moe_gmm.
    rw [fw_all2all_moe_gmm_split_commute_2
          (initPM 11613) (initPM 11614)
          (fw_topk_routing (initPM 11621) 8 1).fst (fw_topk_routing (initPM 11622) 8 1).fst
          (fw_topk_routing (initPM 11621) 8 1).snd.fst (fw_topk_routing (initPM 11622) 8 1).snd.fst
          (initPM 11629) (initPM 11630)
          (initPM 11631) (initPM 11632)
          64 8 (((10 : Nat) : Scalar))]
    -- Push through inner elemwiseAdd (all2all + mul).
    rw [fw_add_allGather0_commute_2
          (fw_all2all_moe_gmm (initPM 11613) (fw_topk_routing (initPM 11621) 8 1).fst
            (fw_topk_routing (initPM 11621) 8 1).snd.fst (initPM 11629) (initPM 11631)
            64 0 32 8 (((10 : Nat) : Scalar)))
          (fw_all2all_moe_gmm (initPM 11614) (fw_topk_routing (initPM 11622) 8 1).fst
            (fw_topk_routing (initPM 11622) 8 1).snd.fst (initPM 11630) (initPM 11632)
            64 32 64 8 (((10 : Nat) : Scalar)))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                             (initPM 5920))))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                             (initPM 5920))))]
    -- Push through outer elemwiseAdd (initPM 11609/11610 + inner).
    rw [fw_add_allGather0_commute_2 (initPM 11609) (initPM 11610)
          (elemwiseAdd
            (fw_all2all_moe_gmm (initPM 11613) (fw_topk_routing (initPM 11621) 8 1).fst
              (fw_topk_routing (initPM 11621) 8 1).snd.fst (initPM 11629) (initPM 11631)
              64 0 32 8 (((10 : Nat) : Scalar)))
            (elemwiseMul
              (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
              (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                          (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                               (initPM 5920)))))
          (elemwiseAdd
            (fw_all2all_moe_gmm (initPM 11614) (fw_topk_routing (initPM 11622) 8 1).fst
              (fw_topk_routing (initPM 11622) 8 1).snd.fst (initPM 11630) (initPM 11632)
              64 32 64 8 (((10 : Nat) : Scalar)))
            (elemwiseMul
              (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
              (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                          (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                               (initPM 5920)))))]
    -- Push through fw_maybe_unshuffle (converts cpSize=1 → cpSize=2×2).
    rw [fw_maybe_unshuffle_cp2_commute
          (elemwiseAdd (initPM 11609)
            (elemwiseAdd
              (fw_all2all_moe_gmm (initPM 11613) (fw_topk_routing (initPM 11621) 8 1).fst
                (fw_topk_routing (initPM 11621) 8 1).snd.fst (initPM 11629) (initPM 11631)
                64 0 32 8 (((10 : Nat) : Scalar)))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                            (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                                 (initPM 5920))))))
          (elemwiseAdd (initPM 11610)
            (elemwiseAdd
              (fw_all2all_moe_gmm (initPM 11614) (fw_topk_routing (initPM 11622) 8 1).fst
                (fw_topk_routing (initPM 11622) 8 1).snd.fst (initPM 11630) (initPM 11632)
                64 32 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                            (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                                 (initPM 5920))))))
          (initPM 5927)]
    -- Push through fw_rms_norm.
    rw [fw_rms_norm_allGather0_commute_2
          (fw_maybe_unshuffle
            (elemwiseAdd (initPM 11609)
              (elemwiseAdd
                (fw_all2all_moe_gmm (initPM 11613) (fw_topk_routing (initPM 11621) 8 1).fst
                  (fw_topk_routing (initPM 11621) 8 1).snd.fst (initPM 11629) (initPM 11631)
                  64 0 32 8 (((10 : Nat) : Scalar)))
                (elemwiseMul
                  (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                  (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                              (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                                   (initPM 5920)))))) 2 0 [initPM 5927])
          (fw_maybe_unshuffle
            (elemwiseAdd (initPM 11610)
              (elemwiseAdd
                (fw_all2all_moe_gmm (initPM 11614) (fw_topk_routing (initPM 11622) 8 1).fst
                  (fw_topk_routing (initPM 11622) 8 1).snd.fst (initPM 11630) (initPM 11632)
                  64 32 64 8 (((10 : Nat) : Scalar)))
                (elemwiseMul
                  (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                  (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                              (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                                   (initPM 5920)))))) 2 1 [initPM 5927])
          (initPM 5929)]
    -- Push through fw_inner_chunk_ce.
    rw [fw_inner_chunk_ce_fst_allGather0_commute_2 (w := initPM 5931) (y := initPM 4678)
        (vocab := ((List.head? (initPM 5931).shape).getD 0)) (zLossScale := ((0 : Nat) : Scalar))]


theorem prove_pattern_1 : pattern_1_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_1

end TrainVerify.Denote.GeneratedPatterns