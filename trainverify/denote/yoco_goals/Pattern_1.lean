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
    exact applyNode_fw_rms_norm_out sm_goal_1 S23 0 5928 5929 5930
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
    exact applyNode_fw_maybe_unshuffle_out sm_goal_1 S22 0 5926 5927 5928 [1, 0]
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
    exact applyNode_fw_all2all_moe_gmm_out sm_goal_1 S12 0 8591 5899 5900 5902 5903 5904 [64, 0, 64, 8]
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
    exact applyNode_fw_sigmoid_out sm_goal_1 S13 0 5908 5909
  -- Sj=17 written by node_16 (FW_mix_precision_linear), outs=[5921], tid=5921
  have h_take17_5921 : sm_goal_1.nodes.take 17 = sm_goal_1.nodes.take 16 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] }] := by rfl
  have hS17_eq_5921 : S17 = applyNode sm_goal_1 S16 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] } := by
    show (sm_goal_1.nodes.take 17).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take17_5921, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS17_5921 : S17 5921 = fw_linear (S16 5919) (S16 5920) := by
    rw [hS17_eq_5921]
    exact applyNode_fw_mix_precision_linear_out sm_goal_1 S16 0 5919 5920 5921
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
    exact applyNode_fw_swiglu_out sm_goal_1 S14 0 5913 5917 5918
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
    exact applyNode_fw_mix_precision_linear_out sm_goal_1 S5 0 5905 5906 5907
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
    exact applyNode_fw_mix_precision_linear_out sm_goal_1 S6 0 5910 5911 5912
  -- Sj=8 written by node_7 (FW_mix_precision_linear), outs=[5916], tid=5916
  have h_take8_5916 : sm_goal_1.nodes.take 8 = sm_goal_1.nodes.take 7 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] }] := by rfl
  have hS8_eq_5916 : S8 = applyNode sm_goal_1 S7 { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] } := by
    show (sm_goal_1.nodes.take 8).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take8_5916, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS8_5916 : S8 5916 = fw_linear (S7 5914) (S7 5915) := by
    rw [hS8_eq_5916]
    exact applyNode_fw_mix_precision_linear_out sm_goal_1 S7 0 5914 5915 5916
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

theorem prove_pattern_1 : pattern_1_stmt := by
  sorry -- WIP

end TrainVerify.Denote.GeneratedPatterns