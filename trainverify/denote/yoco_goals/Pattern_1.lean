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

/-- Wrapped Pattern_1 goal statement with explicit labels hypothesis.

    `goal_1_stmt_cut` unfolds to `∀ initSM initPM, hSM → hPM → hInit → conclusion`.
    Pattern_1's proof previously required a `Pattern_1_labelsAxiom` — an unconstrained
    axiom `∀ y vocab l, valAt y l < vocab` (vacuous: take vocab=0 → False).

    Here we surface that hypothesis as a *statement-level* parameter. The verifier's
    caller (Python autodist / training pipeline) must supply a `hlabels` witness
    (typically via a runtime `assert (labels < vocab).all()`) alongside `initPM`.

    Non-vacuity: the hypothesis quantifies over the SPECIFIC `initPM 4678` tensor
    (not `∀ tensor`) and uses SPECIFIC bounds (Lshard=2048, vocab=154880), so it
    cannot be trivially satisfied by picking pathological values. Existence is
    witnessed by `pattern_1_labels_hypothesis_witness` below (e.g. zeroTensor). -/
def goal_1_stmt_with_labels : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM sm_goal_1InitEnv →
    StoreShapesHold initPM pm_goal_1InitEnv →
    InitGoalsHold pm_goal_1.numRanks goal_1_cut_initGoals initSM initPM →
    (∀ l : Nat, l < 4096 → scalarToNat (valAt (initPM 4678) l) < 154880) →
    let smStore := denoteGraph sm_goal_1 initSM
    let pmStore := denoteGraph pm_goal_1 initPM
    let ts := smStore goal_1.ts
    let tps := goal_1.tps.map (fun p => pmStore p.tid)
    ts.shape = goal_1.tsShape ∧
      (tps.map (fun t => t.shape)) = goal_1.tpShapes ∧
      ts = reconstructWithDim goal_1.gatherDim pm_goal_1.numRanks 0 tps

inductive pattern_1_target : Prop → Prop
  | goal_1 : pattern_1_target goal_1_stmt_with_labels

def pattern_1_stmt : Prop :=
  ∀ {target : Prop}, pattern_1_target target → target

/-- Vacuity witness for `goal_1_stmt_with_labels`'s hypothesis.

    Purpose: prove the labels-bounded hypothesis is NOT logically false. If it
    were (e.g. from a bad axiom like `∀ y vocab, valAt y < vocab` with vocab=0),
    then `stmt := hyp → conclusion` becomes vacuously True and Pattern_1 says
    nothing about actual training runs.

    This witness explicitly constructs a `Store` (namely `fun _ => zeroTensor [4096]`)
    that satisfies the hypothesis: `valAt (zeroTensor [4096]) l = 0` by definition
    of `Tensor.mkShape sh (fun _ => 0)`, and `scalarToNat 0 = ⌊0⌋₊ = 0 < 154880`.

    Because the hypothesis IS satisfiable, `stmt := hyp → conclusion` is a genuine
    implication (not `False → conclusion`), and `prove_pattern_1` gives real content. -/
theorem pattern_1_labels_hypothesis_witness :
    ∃ (initPM : Store), (∀ l : Nat, l < 4096 →
      scalarToNat (valAt (initPM 4678) l) < 154880) := by
  refine ⟨fun _ => zeroTensor [4096], ?_⟩
  intro l _hl
  -- valAt (zeroTensor [4096]) l = 0 for any l:
  -- - if l < prodShape [4096] = 4096, valAt returns .val ⟨l, _⟩ = (fun _ => 0) _ = 0
  -- - otherwise, valAt returns 0 (else branch)
  have hval : valAt (zeroTensor [4096]) l = 0 := by
    unfold valAt zeroTensor
    by_cases h : l < prodShape (Tensor.mkShape [4096] (fun _ => (0 : Scalar))).shape
    · simp [h, Tensor.mkShape]
    · simp [h]
  rw [hval]
  -- scalarToNat 0 = 0
  have : scalarToNat (0 : Scalar) = 0 := by
    unfold scalarToNat; simp
  rw [this]
  omega

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
theorem denote_sm_goal_1_4673 (initSM : Store)
    (h5898 : (initSM 5898).shape.reverse.head? = some 64) :
    denoteGraph sm_goal_1 initSM 4673 =
      (fw_inner_chunk_ce
        (fw_rms_norm
          (fw_maybe_unshuffle (elemwiseAdd (initSM 5893)
              (elemwiseAdd
                (fw_all2all_moe_gmm (initSM 5895)
                  ((fw_topk_routing (initSM 5898) 8 64).fst)
                  ((fw_topk_routing (initSM 5898) 8 64).snd.fst)
                  (initSM 5902) (initSM 5903) 64 0 64 8 ((((10 : Nat) : Scalar))))
                (elemwiseMul
                  (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906))))
                  (fw_view [4096, 1024]
                    (fw_linear
                      (fw_swiglu
                        (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
                        (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
                      (initSM 5920))))))
            (initSM 5927) 1 0)
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
  have hS23_5928 : S23 5928 = fw_maybe_unshuffle (S22 5926) (S22 5927) 1 0 := by
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
  have hS8_5898_sh : (S8 5898).shape.reverse.head? = some 64 := by
    have hS8_5898_eq : S8 5898 = initSM 5898 :=
      foldl_applyNode_at_not_written sm_goal_1 (sm_goal_1.nodes.take 8) initSM 5898
        (by intro n hn; fin_cases hn <;> decide)
    rw [hS8_5898_eq]; exact h5898
  have h_take9_5899 : sm_goal_1.nodes.take 9 = sm_goal_1.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 64] }] := by rfl
  have hS9_eq_5899 : S9 = applyNode sm_goal_1 S8 { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 64] } := by
    show (sm_goal_1.nodes.take 9).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take9_5899, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS9_5899 : S9 5899 = (fw_topk_routing (S8 5898) 8 64).fst := by
    rw [hS9_eq_5899, applyNode_fw_topk_routing_probs_out sm_goal_1 S8 0 5898 5899 5900 5901 [8, 64], hS8_5898_sh]
    rfl
  -- Sj=9 written by node_8 (FW_topk_routing), outs=[5899, 5900, 5901], tid=5900
  have h_take9_5900 : sm_goal_1.nodes.take 9 = sm_goal_1.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 64] }] := by rfl
  have hS9_eq_5900 : S9 = applyNode sm_goal_1 S8 { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 64] } := by
    show (sm_goal_1.nodes.take 9).foldl (applyNode sm_goal_1) initSM = _
    rw [h_take9_5900, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hS9_5900 : S9 5900 = (fw_topk_routing (S8 5898) 8 64).snd.fst := by
    rw [hS9_eq_5900, applyNode_fw_topk_routing_map_out sm_goal_1 S8 0 5898 5899 5900 5901 [8, 64] (by decide), hS8_5898_sh]
    rfl
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
theorem denote_pm_goal_1_4673 (initPM : Store)
    (h11621 : (initPM 11621).shape.reverse.head? = some 64)
    (h11622 : (initPM 11622).shape.reverse.head? = some 64) :
    denoteGraph pm_goal_1 initPM 4673 =
      allGatherPrimDimN 0 pm_goal_1.numRanks 0 [(fw_inner_chunk_ce (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11609) (elemwiseAdd (fw_all2all_moe_gmm_full (initPM 11613) ((fw_topk_routing (initPM 11621) 8 64).fst) ((fw_topk_routing (initPM 11621) 8 64).snd.fst) [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar)))) (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))) (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911))) (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915)))) (initPM 5920)))))) (initPM 5927) 2 0) (initPM 5929)) (initPM 5931) (chunkPrimDimN 0 pm_goal_1.numRanks 0 (initPM 4678)) (((initPM 5931).shape.head?).getD 0) ((((0 : Nat) : Scalar)))).fst, (fw_inner_chunk_ce (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11610) (elemwiseAdd (fw_all2all_moe_gmm_full (initPM 11614) ((fw_topk_routing (initPM 11622) 8 64).fst) ((fw_topk_routing (initPM 11622) 8 64).snd.fst) [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar)))) (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))) (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911))) (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915)))) (initPM 5920)))))) (initPM 5927) 2 1) (initPM 5929)) (initPM 5931) (chunkPrimDimN 0 pm_goal_1.numRanks 1 (initPM 4678)) (((initPM 5931).shape.head?).getD 0) ((((0 : Nat) : Scalar)))).fst] := by
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
  have hP48_11728 : P48 11728 = fw_maybe_unshuffle (P47 11722) (P47 5927) 2 1 := by
    rw [hP48_eq_11728]
    exact applyNode_fw_maybe_unshuffle_out_1p pm_goal_1 P47 1 11722 5927 11728 [2, 1]
  -- Pj=47 written by pm_node_46 (rank=0 FW_maybe_unshuffle), outs=[11727], tid=11727
  have h_pmtake47_11727 : pm_goal_1.nodes.take 47 = pm_goal_1.nodes.take 46 ++ [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] }] := by rfl
  have hP47_eq_11727 : P47 = applyNode pm_goal_1 P46 { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] } := by
    show (pm_goal_1.nodes.take 47).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake47_11727, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP47_11727 : P47 11727 = fw_maybe_unshuffle (P46 11721) (P46 5927) 2 0 := by
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
  -- Pj=30 written by pm_node_29 (rank=1 FW_all2all_moe_gmm_full), outs=[11634], tid=11634
  have h_pmtake30_11634 : pm_goal_1.nodes.take 30 = pm_goal_1.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16889, 11624, 11626, 11629, 11630, 11631, 11632], outs := [11634], params := [64, 8] }] := by rfl
  have hP30_eq_11634 : P30 = applyNode pm_goal_1 P29 { rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16889, 11624, 11626, 11629, 11630, 11631, 11632], outs := [11634], params := [64, 8] } := by
    show (pm_goal_1.nodes.take 30).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake30_11634, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP30_11634 : P30 11634 = fw_all2all_moe_gmm_full (P29 16889) (P29 11624) (P29 11626)
      [P29 11629, P29 11630] [P29 11631, P29 11632] 64 8 ((((10 : Nat) : Scalar))) := by
    rw [hP30_eq_11634]
    exact applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_1 P29 1
      16889 11624 11626 11629 11630 11631 11632 11634 [64, 8]
  -- Pj=40 written by pm_node_39 (rank=1 FW_mul), outs=[11708], tid=11708
  have h_pmtake40_11708 : pm_goal_1.nodes.take 40 = pm_goal_1.nodes.take 39 ++ [{ rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] }] := by rfl
  have hP40_eq_11708 : P40 = applyNode pm_goal_1 P39 { rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] } := by
    show (pm_goal_1.nodes.take 40).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake40_11708, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP40_11708 : P40 11708 = elemwiseMul (P39 11648) (P39 11704) := by
    rw [hP40_eq_11708]
    exact applyNode_fw_mul_out pm_goal_1 P39 1 11648 11704 11708
  -- Pj=27 written by pm_node_26 (rank=0 FW_all2all_moe_gmm_full), outs=[11633], tid=11633
  have h_pmtake27_11633 : pm_goal_1.nodes.take 27 = pm_goal_1.nodes.take 26 ++ [{ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16866, 11623, 11625, 11629, 11630, 11631, 11632], outs := [11633], params := [64, 8] }] := by rfl
  have hP27_eq_11633 : P27 = applyNode pm_goal_1 P26 { rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16866, 11623, 11625, 11629, 11630, 11631, 11632], outs := [11633], params := [64, 8] } := by
    show (pm_goal_1.nodes.take 27).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake27_11633, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP27_11633 : P27 11633 = fw_all2all_moe_gmm_full (P26 16866) (P26 11623) (P26 11625)
      [P26 11629, P26 11630] [P26 11631, P26 11632] 64 8 ((((10 : Nat) : Scalar))) := by
    rw [hP27_eq_11633]
    exact applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_1 P26 0
      16866 11623 11625 11629 11630 11631 11632 11633 [64, 8]
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
  have hP29_11629 : P29 11629 = initPM 11629 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 29) initPM 11629
      (by intro n hn; fin_cases hn <;> decide)
  have hP29_11632 : P29 11632 = initPM 11632 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 29) initPM 11632
      (by intro n hn; fin_cases hn <;> decide)
  have hP29_11631 : P29 11631 = initPM 11631 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 29) initPM 11631
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
  have hP26_11630 : P26 11630 = initPM 11630 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 26) initPM 11630
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_11631 : P26 11631 = initPM 11631 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 26) initPM 11631
      (by intro n hn; fin_cases hn <;> decide)
  have hP26_11632 : P26 11632 = initPM 11632 :=
    foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 26) initPM 11632
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
  have hP22_11622_sh : (P22 11622).shape.reverse.head? = some 64 := by
    have hP22_11622_eq : P22 11622 = initPM 11622 :=
      foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 22) initPM 11622
        (by intro n hn; fin_cases hn <;> decide)
    rw [hP22_11622_eq]; exact h11622
  have h_pmtake23_11624 : pm_goal_1.nodes.take 23 = pm_goal_1.nodes.take 22 ++ [{ rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 64] }] := by rfl
  have hP23_eq_11624 : P23 = applyNode pm_goal_1 P22 { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 64] } := by
    show (pm_goal_1.nodes.take 23).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake23_11624, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP23_11624 : P23 11624 = (fw_topk_routing (P22 11622) 8 64).fst := by
    rw [hP23_eq_11624, applyNode_fw_topk_routing_probs_out pm_goal_1 P22 1 11622 11624 11626 11628 [8, 64], hP22_11622_sh]
    rfl
  -- Pj=23 written by pm_node_22 (rank=1 FW_topk_routing), outs=[11624, 11626, 11628], tid=11626
  have h_pmtake23_11626 : pm_goal_1.nodes.take 23 = pm_goal_1.nodes.take 22 ++ [{ rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 64] }] := by rfl
  have hP23_eq_11626 : P23 = applyNode pm_goal_1 P22 { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 64] } := by
    show (pm_goal_1.nodes.take 23).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake23_11626, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP23_11626 : P23 11626 = (fw_topk_routing (P22 11622) 8 64).snd.fst := by
    rw [hP23_eq_11626, applyNode_fw_topk_routing_map_out pm_goal_1 P22 1 11622 11624 11626 11628 [8, 64] (by decide), hP22_11622_sh]
    rfl
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
  have hP18_11621_sh : (P18 11621).shape.reverse.head? = some 64 := by
    have hP18_11621_eq : P18 11621 = initPM 11621 :=
      foldl_applyNode_at_not_written pm_goal_1 (pm_goal_1.nodes.take 18) initPM 11621
        (by intro n hn; fin_cases hn <;> decide)
    rw [hP18_11621_eq]; exact h11621
  have h_pmtake19_11623 : pm_goal_1.nodes.take 19 = pm_goal_1.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 64] }] := by rfl
  have hP19_eq_11623 : P19 = applyNode pm_goal_1 P18 { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 64] } := by
    show (pm_goal_1.nodes.take 19).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake19_11623, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP19_11623 : P19 11623 = (fw_topk_routing (P18 11621) 8 64).fst := by
    rw [hP19_eq_11623, applyNode_fw_topk_routing_probs_out pm_goal_1 P18 0 11621 11623 11625 11627 [8, 64], hP18_11621_sh]
    rfl
  -- Pj=19 written by pm_node_18 (rank=0 FW_topk_routing), outs=[11623, 11625, 11627], tid=11625
  have h_pmtake19_11625 : pm_goal_1.nodes.take 19 = pm_goal_1.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 64] }] := by rfl
  have hP19_eq_11625 : P19 = applyNode pm_goal_1 P18 { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 64] } := by
    show (pm_goal_1.nodes.take 19).foldl (applyNode pm_goal_1) initPM = _
    rw [h_pmtake19_11625, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP19_11625 : P19 11625 = (fw_topk_routing (P18 11621) 8 64).snd.fst := by
    rw [hP19_eq_11625, applyNode_fw_topk_routing_map_out pm_goal_1 P18 0 11621 11623 11625 11627 [8, 64] (by decide), hP18_11621_sh]
    rfl
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
    hP29_11626, hP29_11629, hP29_11630, hP29_11631, hP29_11632,
    hP29_11685, hP28_11647, hP28_11663,
    hP28_11681, hP27_11633, hP27_11645,
    hP26_16866, hP26_11623, hP26_11625,
    hP26_11629, hP26_11630, hP26_11631, hP26_11632, hP26_11682,
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

-- (Removed: elemwiseMul_shape_broadcast — was based on old first-wins outShape2 rule.
--  With PyTorch-correct per-dim max broadcast, that stale lemma is no longer meaningful.)


/-- Value at a specific flat index for elemwiseAdd of two [2048, 1024] tensors. -/
private theorem elemwiseAdd_valAt_2048_1024 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [2048, 1024]) (hy : y.shape = [2048, 1024]) (hidx : idx < 2048 * 1024) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [2048, 1024] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape]
  have hnorm : idx / 1024 * 1024 + idx % 1024 = idx := by omega
  rw [hnorm]

/-- Value at a specific flat index for elemwiseAdd of two [4096, 1024] tensors. -/
private theorem elemwiseAdd_valAt_4096_1024 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [4096, 1024]) (hy : y.shape = [4096, 1024]) (hidx : idx < 4096 * 1024) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [4096, 1024] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape]
  have hnorm : idx / 1024 * 1024 + idx % 1024 = idx := by omega
  rw [hnorm]

/-- fw_add commutes with dim-0 sharding (2 shards) — same-shape [2048, 1024] version. -/
theorem fw_add_allGather0_commute_2_2048_1024 (a b c d : Tensor)
    (ha : a.shape = [2048, 1024]) (hb : b.shape = [2048, 1024])
    (hc : c.shape = [2048, 1024]) (hd : d.shape = [2048, 1024]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [elemwiseAdd a c, elemwiseAdd b d] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 1024] := by
    simp [ha]
  have hhead_cd : (([c, d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 1024] := by
    simp [hc]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] hhead_ab]; simp [List.set, List.getD]
  have hG_cd : (allGatherPrimDimN 0 2 0 [c, d]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] hhead_cd]; simp [List.set, List.getD]
  have hadd_ac : (elemwiseAdd a c).shape = [2048, 1024] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, ha, hc]
  have hadd_bd : (elemwiseAdd b d).shape = [2048, 1024] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hb, hd]
  have hhead_add : (([elemwiseAdd a c, elemwiseAdd b d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 1024] := by
    simp [hadd_ac]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [elemwiseAdd a c, elemwiseAdd b d]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] hhead_add]; simp [List.set, List.getD]
  have hLHS_shape : (elemwiseAdd (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [4096, 1024] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hG_ab, hG_cd]
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < 4096 * 1024 := by simpa [prodShape] using hidx
    set row := idx / 1024 with hrow_def
    set j := idx % 1024 with hj_def
    have hj_lt : j < 1024 := by rw [hj_def]; exact Nat.mod_lt _ (by omega)
    have hrow_lt : row < 4096 := by
      rw [hrow_def]
      have : idx / 1024 < 4096 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
      exact this
    set r := row / 2048 with hr_def
    set i := row % 2048 with hi_def
    have hi_lt : i < 2048 := by rw [hi_def]; exact Nat.mod_lt _ (by omega)
    have hr_lt : r < 2 := by
      rw [hr_def]
      have : row / 2048 < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
      exact this
    have hidx_eq : idx = (r * 2048 + i) * 1024 + j := by
      subst r i j row
      have h1 : idx / 1024 = 2048 * (idx / 1024 / 2048) + idx / 1024 % 2048 :=
        (Nat.div_add_mod _ 2048).symm
      have h2 : idx = 1024 * (idx / 1024) + idx % 1024 :=
        (Nat.div_add_mod idx 1024).symm
      omega
    have hLHS_val : valAt (elemwiseAdd (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])) idx
        = valAt (allGatherPrimDimN 0 2 0 [a, b]) idx + valAt (allGatherPrimDimN 0 2 0 [c, d]) idx := by
      apply elemwiseAdd_valAt_4096_1024 _ _ idx hG_ab hG_cd
      linarith
    rw [hLHS_val]
    have hshapes_add : ∀ r' (_ : r' < 2),
        (([elemwiseAdd a c, elemwiseAdd b d].getD r' (zeroTensor [2048, 1024]))).shape = [2048, 1024] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hadd_ac, hadd_bd]
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [2048, 1024]))).shape = [2048, 1024] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_cd : ∀ r' (_ : r' < 2),
        (([c, d].getD r' (zeroTensor [2048, 1024]))).shape = [2048, 1024] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hc, hd]
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 2048 1024 [elemwiseAdd a c, elemwiseAdd b d]
          (by omega) (by omega) (by omega) hhead_add hshapes_add r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 2048 1024 [a, b]
          (by omega) (by omega) (by omega) hhead_ab hshapes_ab r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 2048 1024 [c, d]
          (by omega) (by omega) (by omega) hhead_cd hshapes_cd r hr_lt i hi_lt j hj_lt]
    have hr_cases : r = 0 ∨ r = 1 := by omega
    have hgetD_add : [elemwiseAdd a c, elemwiseAdd b d].getD r (zeroTensor [2048, 1024]) =
        elemwiseAdd ([a, b].getD r (zeroTensor [2048, 1024])) ([c, d].getD r (zeroTensor [2048, 1024])) := by
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_add]
    set ea := [a, b].getD r (zeroTensor [2048, 1024])
    set ec := [c, d].getD r (zeroTensor [2048, 1024])
    have hea_shape : ea.shape = [2048, 1024] := hshapes_ab r hr_lt
    have hec_shape : ec.shape = [2048, 1024] := hshapes_cd r hr_lt
    have hloc_lt : i * 1024 + j < 2048 * 1024 := by
      have h1 : i * 1024 + j < i * 1024 + 1024 := by omega
      have h2 : i * 1024 + 1024 = (i + 1) * 1024 := by ring
      have h3 : (i + 1) * 1024 ≤ 2048 * 1024 := Nat.mul_le_mul_right _ (by omega)
      omega
    exact (elemwiseAdd_valAt_2048_1024 ea ec _ hea_shape hec_shape hloc_lt).symm



/-- Helper: valAt of elemwiseMul with same-shape `[S, H]` operands. -/
private theorem elemwiseMul_valAt_S_H (a c : Tensor) (S H : Nat) (idx : Nat)
    (ha : a.shape = [S, H]) (hc : c.shape = [S, H])
    (hS : 0 < S) (hH : 0 < H) (hS_ne1 : S ≠ 1) (hH_ne1 : H ≠ 1)
    (hidx : idx < S * H) :
    valAt (elemwiseMul a c) idx = valAt a idx * valAt c idx := by
  have hH_ne : H ≠ 0 := Nat.pos_iff_ne_zero.mp hH
  have hout : (elemwiseMul a c).shape = [S, H] := by
    simp [elemwiseMul, Tensor.mkShape, outShape2, ha, hc]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseMul, Tensor.mkShape, outShape2, ha, hc, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape, hS_ne1, hH_ne1, hH_ne]
  have hnorm : idx / H * H + idx % H = idx := by
    conv_lhs => rw [Nat.mul_comm (idx / H) H]
    exact Nat.div_add_mod idx H
  rw [hnorm]

/-- Helper: valAt of elemwiseMul where a has broadcasting shape `[S, 1]` and c has `[S, H]`.
    Values: at flat idx of output [S, H], reads a at row (idx/H), c at idx. -/
private theorem elemwiseMul_valAt_broadcast_S1_SH (a c : Tensor) (S H : Nat) (idx : Nat)
    (ha : a.shape = [S, 1]) (hc : c.shape = [S, H])
    (hS : 0 < S) (hH : 0 < H) (hS_ne1 : S ≠ 1) (hH_ne1 : H ≠ 1)
    (hidx : idx < S * H) :
    valAt (elemwiseMul a c) idx = valAt a (idx / H) * valAt c idx := by
  have hH_ge_1 : 1 ≤ H := hH
  have hH_ne : H ≠ 0 := Nat.pos_iff_ne_zero.mp hH
  have hout : (elemwiseMul a c).shape = [S, H] := by
    simp [elemwiseMul, Tensor.mkShape, outShape2, ha, hc,
      Nat.max_eq_right hH_ge_1]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseMul, Tensor.mkShape, outShape2, ha, hc, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape,
    Nat.max_eq_right hH_ge_1, hS_ne1, hH_ne1, hH_ne]
  left
  congr 1
  conv_lhs => rw [Nat.mul_comm (idx / H) H]
  exact Nat.div_add_mod idx H

/-- fw_mul commutes with dim-0 sharding — 2-shard broadcast [S,1] * [S,H] version. -/
theorem fw_mul_allGather0_commute_2_of_broadcast (a b c d : Tensor) (shard H : Nat)
    (hshard : 0 < shard) (hH : 0 < H) (hshard_ne1 : shard ≠ 1) (hshard2_ne1 : shard * 2 ≠ 1)
    (hH_ne1 : H ≠ 1)
    (ha : a.shape = [shard, 1]) (hb : b.shape = [shard, 1])
    (hc : c.shape = [shard, H]) (hd : d.shape = [shard, H]) :
    elemwiseMul (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [elemwiseMul a c, elemwiseMul b d] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, 1] := by
    simp [ha]
  have hhead_cd : (([c, d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, H] := by
    simp [hc]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, 1] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, 1] hhead_ab]; simp [List.set, List.getD]
  have hG_cd : (allGatherPrimDimN 0 2 0 [c, d]).shape = [shard * 2, H] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, H] hhead_cd]; simp [List.set, List.getD]
  have hH_ge_1 : 1 ≤ H := hH
  have hmul_ac : (elemwiseMul a c).shape = [shard, H] := by
    simp [elemwiseMul, Tensor.mkShape, outShape2, ha, hc,
      Nat.max_self, Nat.max_eq_right hH_ge_1]
  have hmul_bd : (elemwiseMul b d).shape = [shard, H] := by
    simp [elemwiseMul, Tensor.mkShape, outShape2, hb, hd,
      Nat.max_self, Nat.max_eq_right hH_ge_1]
  have hhead_mul : (([elemwiseMul a c, elemwiseMul b d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, H] := by
    simp [hmul_ac]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [elemwiseMul a c, elemwiseMul b d]).shape = [shard * 2, H] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, H] hhead_mul]; simp [List.set, List.getD]
  have hLHS_shape : (elemwiseMul (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, H] := by
    simp [elemwiseMul, Tensor.mkShape, outShape2, hG_ab, hG_cd,
      Nat.max_self, Nat.max_eq_right hH_ge_1]
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * H := by simpa [prodShape] using hidx
    set row := idx / H with hrow_def
    set j := idx % H with hj_def
    have hj_lt : j < H := by rw [hj_def]; exact Nat.mod_lt _ hH
    have hrow_lt : row < shard * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul hH]; linarith
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hshard]; linarith
    have hidx_eq : idx = (r * shard + i) * H + j := by
      subst r i j row
      have h1 : shard * (idx / H / shard) + idx / H % shard = idx / H := Nat.div_add_mod (idx / H) shard
      have h2 : H * (idx / H) + idx % H = idx := Nat.div_add_mod idx H
      have h3 : (idx / H / shard * shard + idx / H % shard) * H + idx % H
              = H * (shard * (idx / H / shard)) + H * (idx / H % shard) + idx % H := by ring
      calc idx = H * (idx / H) + idx % H := h2.symm
        _ = H * (shard * (idx / H / shard) + idx / H % shard) + idx % H := by rw [h1]
        _ = H * (shard * (idx / H / shard)) + H * (idx / H % shard) + idx % H := by ring
        _ = (idx / H / shard * shard + idx / H % shard) * H + idx % H := by ring
    -- LHS: broadcast mul at idx = (valAt gather_ab (idx/H)) * (valAt gather_cd idx)
    have hLHS_val :
        valAt (elemwiseMul (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])) idx
          = valAt (allGatherPrimDimN 0 2 0 [a, b]) (idx / H)
            * valAt (allGatherPrimDimN 0 2 0 [c, d]) idx := by
      exact elemwiseMul_valAt_broadcast_S1_SH _ _ (shard * 2) H idx hG_ab hG_cd (by omega) hH hshard2_ne1 hH_ne1 hidx_bound
    rw [hLHS_val]
    -- Shape witnesses for allGatherPrimDimN0_valAt
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, 1]))).shape = [shard, 1] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_cd : ∀ r' (_ : r' < 2),
        (([c, d].getD r' (zeroTensor [shard, H]))).shape = [shard, H] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hc, hd]
    have hshapes_mul : ∀ r' (_ : r' < 2),
        (([elemwiseMul a c, elemwiseMul b d].getD r' (zeroTensor [shard, H]))).shape = [shard, H] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hmul_ac, hmul_bd]
    -- Unfold RHS gather.
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 shard H [elemwiseMul a c, elemwiseMul b d]
          (by omega) hshard hH hhead_mul hshapes_mul r hr_lt i hi_lt j hj_lt]
    -- LHS a: after subst idx via hidx_eq, ((r*shard+i)*H+j)/H = r*shard+i
    have hidx_div_H' : ((r * shard + i) * H + j) / H = r * shard + i := by
      have h1 : ((r * shard + i) * H + j) / H = j / H + (r * shard + i) := by
        rw [Nat.add_comm, Nat.add_mul_div_right j (r * shard + i) hH]
      rw [h1, Nat.div_eq_of_lt hj_lt]; ring
    rw [hidx_div_H']
    -- allGatherPrimDimN0_valAt on cd first (matches directly), then rewrite ab for H=1 form.
    rw [allGatherPrimDimN0_valAt 2 shard H [c, d]
          (by omega) hshard hH hhead_cd hshapes_cd r hr_lt i hi_lt j hj_lt]
    -- Now target only has valAt on ab side to touch; rewrite (r*shard+i) → (r*shard+i)*1+0
    conv_lhs => lhs; rw [show r * shard + i = (r * shard + i) * 1 + 0 from by ring]
    rw [allGatherPrimDimN0_valAt 2 shard 1 [a, b]
          (by omega) hshard (by omega) hhead_ab hshapes_ab r hr_lt i hi_lt 0 (by omega)]
    -- getD for mul on RHS = elemwiseMul (getD ab) (getD cd)
    have hr_cases : r = 0 ∨ r = 1 := by
      interval_cases r
      · left; rfl
      · right; rfl
    have hgetD_mul :
        [elemwiseMul a c, elemwiseMul b d].getD r (zeroTensor [shard, H]) =
        elemwiseMul ([a, b].getD r (zeroTensor [shard, 1])) ([c, d].getD r (zeroTensor [shard, H])) := by
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_mul]
    set ea := [a, b].getD r (zeroTensor [shard, 1])
    set ec := [c, d].getD r (zeroTensor [shard, H])
    have hea_shape : ea.shape = [shard, 1] := hshapes_ab r hr_lt
    have hec_shape : ec.shape = [shard, H] := hshapes_cd r hr_lt
    have hloc_lt : i * H + j < shard * H := by
      have h1 : i * H + j < i * H + H := by omega
      have h2 : i * H + H = (i + 1) * H := by ring
      have h3 : (i + 1) * H ≤ shard * H := Nat.mul_le_mul_right _ (by omega)
      omega
    -- RHS local mul at (i*H + j) = (valAt ea ((i*H+j)/H)) * (valAt ec (i*H+j))
    have hRHS_local :
        valAt (elemwiseMul ea ec) (i * H + j)
          = valAt ea ((i * H + j) / H) * valAt ec (i * H + j) := by
      exact elemwiseMul_valAt_broadcast_S1_SH ea ec shard H (i * H + j) hea_shape hec_shape hshard hH hshard_ne1 hH_ne1 hloc_lt
    rw [hRHS_local]
    have hij_div : (i * H + j) / H = i := by
      have h1 : (i * H + j) / H = j / H + i := by
        rw [Nat.add_comm, Nat.add_mul_div_right j i hH]
      rw [h1, Nat.div_eq_of_lt hj_lt]; ring
    rw [hij_div]
    -- Now normalize: ea normalized as (i*1+0) matches expected form
    ring_nf

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

/-- fw_rms_norm commutes with dim-0 sharding. Row-wise reduction is
    orthogonal to dim-0 sharding, so this cleanly commutes. -/
theorem fw_rms_norm_allGather0_commute_2 (a b w : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden]) :
    fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead]; simp [List.set, List.getD]
  have hrms_shape : ∀ c : Tensor, c.shape = [shard, hidden] → (fw_rms_norm c w).shape = [shard, hidden] := by
    intro c hc; unfold fw_rms_norm; rw [hc]; simp [Tensor.mkShape]
  have hrms_a : (fw_rms_norm a w).shape = [shard, hidden] := hrms_shape a ha
  have hrms_b : (fw_rms_norm b w).shape = [shard, hidden] := hrms_shape b hb
  have hhead_rms : (([fw_rms_norm a w, fw_rms_norm b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hrms_a]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_rms]; simp [List.set, List.getD]
  have hLHS_shape : (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w).shape = [shard * 2, hidden] := by
    unfold fw_rms_norm; rw [hG_shape]; simp [Tensor.mkShape]
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
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
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_rms : ∀ r' (_ : r' < 2),
        (([fw_rms_norm a w, fw_rms_norm b w].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hrms_a, hrms_b]
    -- LHS at idx: unfold fw_rms_norm on the gathered tensor.
    have hLHS_val : valAt (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w) idx =
        (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx *
          (1 / sqrtFn (rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b]) (idx / hidden) hidden + rmsNormEps))) *
          valAt w (idx % hidden) := by
      unfold fw_rms_norm
      rw [show (allGatherPrimDimN 0 2 0 [a, b]).shape.reverse = hidden :: [shard * 2] from by rw [hG_shape]; rfl]
      simp only [Tensor.mkShape, valAt]
      have hidx_lt_prod : idx < prodShape (allGatherPrimDimN 0 2 0 [a, b]).shape := by
        rw [hG_shape]; simp [prodShape]; exact hidx_bound
      simp [hidx_lt_prod]
    rw [hLHS_val, hidx_eq]
    -- Show rmsMeanSqAt commutes: rmsMeanSqAt (allGather [a,b]) (r*shard+i) hidden = rmsMeanSqAt (getD r) i hidden
    have hrms_commute : rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b]) (r * shard + i) hidden =
        rmsMeanSqAt ([a, b].getD r (zeroTensor [shard, hidden])) i hidden := by
      unfold rmsMeanSqAt
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead hshapes_ab r hr_lt i hi_lt k hk]
    have hrow_div : (r * shard + i) * hidden / hidden = r * shard + i := by
      rw [Nat.mul_div_cancel _ hhid]
    have hrow_div' : ((r * shard + i) * hidden + j) / hidden = r * shard + i := by
      rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
          Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
    have hrow_mod : ((r * shard + i) * hidden + j) % hidden = j := by
      rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
    rw [hrow_div', hrow_mod]
    rw [hrms_commute]
    -- Now for allGather values.
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead hshapes_ab
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_rms_norm a w, fw_rms_norm b w]
          (by omega) hshard hhid hhead_rms hshapes_rms r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_rms : [fw_rms_norm a w, fw_rms_norm b w].getD r (zeroTensor [shard, hidden]) =
        fw_rms_norm ([a, b].getD r (zeroTensor [shard, hidden])) w := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_rms]
    -- Now unfold RHS: valAt (fw_rms_norm c w) at (i * hidden + j)
    set c := [a, b].getD r (zeroTensor [shard, hidden]) with hc_def
    have hc_shape : c.shape = [shard, hidden] := hshapes_ab r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    have h_ihidden_div : (i * hidden + j) / hidden = i := by
      rw [show i * hidden + j = j + hidden * i from by ring,
          Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
    have h_ihidden_mod : (i * hidden + j) % hidden = j := by
      rw [show i * hidden + j = j + hidden * i from by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
    unfold fw_rms_norm
    rw [show c.shape.reverse = hidden :: [shard] from by rw [hc_shape]; rfl]
    simp only [Tensor.mkShape, valAt]
    have hloc_lt_prod : i * hidden + j < prodShape c.shape := by
      rw [hc_shape]; simp [prodShape]; exact hloc_bound
    simp [hloc_lt_prod, h_ihidden_div, h_ihidden_mod]



/-- 2-D fw_linear shape: `[b, i] × [o, i] → [b, o]`. Moved up so subsequent theorems can use it. -/
private theorem fw_linear_2d_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

/-- fw_linear commutes with dim-0 sharding — 2-shard 2D version with shape hypothesis.
    Both a, b have shape [bshard, i], w has shape [o, i]. -/
theorem fw_linear_allGather0_commute_2_of (a b w : Tensor) (bshard i o : Nat)
    (hbshard : 0 < bshard) (hi : 0 < i) (ho : 0 < o)
    (ha : a.shape = [bshard, i]) (hb : b.shape = [bshard, i])
    (hw : w.shape = [o, i]) :
    fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w] := by
  -- Shape facts
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [bshard, i] := by
    simp [ha]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [bshard * 2, i] := by
    rw [allGatherPrimDimN_shape 0 2 _ [bshard, i] hhead_ab]; simp [List.set, List.getD]
  have hlin_a : (fw_linear a w).shape = [bshard, o] := fw_linear_2d_shape bshard i o a w ha hw
  have hlin_b : (fw_linear b w).shape = [bshard, o] := fw_linear_2d_shape bshard i o b w hb hw
  have hhead_lin : (([fw_linear a w, fw_linear b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [bshard, o] := by
    simp [hlin_a]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w]).shape = [bshard * 2, o] := by
    rw [allGatherPrimDimN_shape 0 2 _ [bshard, o] hhead_lin]; simp [List.set, List.getD]
  have hLHS_shape : (fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w).shape = [bshard * 2, o] :=
    fw_linear_2d_shape (bshard * 2) i o _ w hG_ab hw
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < bshard * 2 * o := by simpa [prodShape] using houtIdx
    -- Compute both sides via k_matmul.
    have hLHS_val : valAt (fw_linear (allGatherPrimDimN 0 2 0 [a, b]) w) outIdx
        = k_matmul (bshard * 2) o i (allGatherPrimDimN 0 2 0 [a, b]) w
            ⟨outIdx, by show outIdx < prodShape [bshard * 2, o]; simp [prodShape]; linarith⟩ := by
      rw [TrainVerify.Denote.fw_linear_is_matmul (bshard * 2) i o _ w hG_ab hw]
      rw [valAt_of_lt _ _ (by show outIdx < prodShape [bshard * 2, o]; simp [prodShape]; linarith)]
      rfl
    rw [hLHS_val]
    -- Row-major decomposition of outIdx
    set row := outIdx / o with hrow_def
    set c := outIdx % o with hc_def
    have hc_lt : c < o := by rw [hc_def]; exact Nat.mod_lt _ ho
    have hrow_lt : row < bshard * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul ho]; linarith
    set r := row / bshard with hr_def
    set il := row % bshard with hil_def
    have hil_lt : il < bshard := by rw [hil_def]; exact Nat.mod_lt _ hbshard
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hbshard]; linarith
    have houtIdx_eq : outIdx = (r * bshard + il) * o + c := by
      subst r il c row
      have h1 : bshard * (outIdx / o / bshard) + outIdx / o % bshard = outIdx / o :=
        Nat.div_add_mod (outIdx / o) bshard
      have h2 : o * (outIdx / o) + outIdx % o = outIdx := Nat.div_add_mod outIdx o
      calc outIdx = o * (outIdx / o) + outIdx % o := h2.symm
        _ = o * (bshard * (outIdx / o / bshard) + outIdx / o % bshard) + outIdx % o := by rw [h1]
        _ = (outIdx / o / bshard * bshard + outIdx / o % bshard) * o + outIdx % o := by ring
    -- k_matmul unfolds to a Finset sum. The KEY is that gather0's valAt at (row * i + j) reads
    -- from shard `r` at local (il * i + j). So both sides get same sum.
    simp [k_matmul, prodShape]
    -- Row for LHS: outIdx / o = r * bshard + il (from houtIdx_eq)
    have hout_div : outIdx / o = r * bshard + il := by
      rw [houtIdx_eq]
      have h1 : ((r * bshard + il) * o + c) / o = c / o + (r * bshard + il) := by
        rw [Nat.add_comm, Nat.add_mul_div_right c (r * bshard + il) ho]
      rw [h1, Nat.div_eq_of_lt hc_lt]; ring
    have hout_mod : outIdx % o = c := by
      rw [houtIdx_eq]
      have h1 : ((r * bshard + il) * o + c) % o = c % o := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt hc_lt]
    rw [hout_div, hout_mod]
    -- Now compute RHS at outIdx
    have hRHS_val : valAt (allGatherPrimDimN 0 2 0 [fw_linear a w, fw_linear b w]) outIdx
        = valAt ([fw_linear a w, fw_linear b w].getD r (zeroTensor [bshard, o])) (il * o + c) := by
      rw [houtIdx_eq]
      have hshapes_lin : ∀ r' (_ : r' < 2),
          (([fw_linear a w, fw_linear b w].getD r' (zeroTensor [bshard, o]))).shape = [bshard, o] := by
        intro r' hr'
        have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
        rcases this with h | h <;> rw [h] <;> simp [List.getD, hlin_a, hlin_b]
      exact allGatherPrimDimN0_valAt 2 bshard o [fw_linear a w, fw_linear b w]
              (by omega) hbshard ho hhead_lin hshapes_lin r hr_lt il hil_lt c hc_lt
    rw [hRHS_val]
    -- getD r resolves to fw_linear a w or fw_linear b w
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    have hgetD_lin :
        [fw_linear a w, fw_linear b w].getD r (zeroTensor [bshard, o]) =
        fw_linear ([a, b].getD r (zeroTensor [bshard, i])) w := by
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_lin]
    -- Now RHS = valAt (fw_linear e_r w) (il * o + c) where e_r = [a,b].getD r ...
    set ear := [a, b].getD r (zeroTensor [bshard, i])
    have hear_shape : ear.shape = [bshard, i] := by
      show ([a, b].getD r (zeroTensor [bshard, i])).shape = [bshard, i]
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hloc_bound : il * o + c < bshard * o := by
      have h1 : il * o + c < il * o + o := by omega
      have h2 : il * o + o = (il + 1) * o := by ring
      have h3 : (il + 1) * o ≤ bshard * o := Nat.mul_le_mul_right _ (by omega)
      omega
    have hRHS_lin_val : valAt (fw_linear ear w) (il * o + c)
        = k_matmul bshard o i ear w ⟨il * o + c, by show il * o + c < prodShape [bshard, o]; simp [prodShape]; linarith⟩ := by
      rw [TrainVerify.Denote.fw_linear_is_matmul bshard i o ear w hear_shape hw]
      rw [valAt_of_lt _ _ (by show il * o + c < prodShape [bshard, o]; simp [prodShape]; linarith)]
      rfl
    rw [hRHS_lin_val]
    -- Now both sides are k_matmul sums. Show they equal term-by-term.
    simp [k_matmul, prodShape]
    -- LHS row index: r*bshard+il; RHS row index: il (divisor bshard already gives il)
    have hil_div : (il * o + c) / o = il := by
      have h1 : (il * o + c) / o = c / o + il := by
        rw [Nat.add_comm, Nat.add_mul_div_right c il ho]
      rw [h1, Nat.div_eq_of_lt hc_lt]; ring
    have hc_mod' : c % o = c := Nat.mod_eq_of_lt hc_lt
    rw [hil_div, hc_mod']
    -- Now sum indices align. valAt gather0[a,b] ((r*bshard+il) * i + j) = valAt ear (il * i + j)
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < i := by simp [Finset.mem_range] at hj; exact hj
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [bshard, i]))).shape = [bshard, i] := by
      intro r' hr'
      have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    congr 1
    rw [allGatherPrimDimN0_valAt 2 bshard i [a, b]
          (by omega) hbshard hi hhead_ab hshapes_ab r hr_lt il hil_lt j hj_lt]


-- (fw_linear_2d_shape moved earlier so fw_linear_allGather0_commute_2_of can use it.)

/-- Trivial: `fw_view` with the tensor's own shape is the identity. -/
private theorem fw_view_self_eq (t : Tensor) (sh : Shape) (hsh : t.shape = sh) :
    fw_view sh t = t := by
  apply Tensor.ext
  · show sh = t.shape; exact hsh.symm
  · intro k hk
    have hkt : k < prodShape t.shape := by rw [hsh]; exact hk
    have hksh : k < prodShape sh := by rw [← hsh]; exact hkt
    simp [fw_view, Tensor.mkShape, valAt, dif_pos hksh, dif_pos hkt]

/-- fw_view commutes with dim-0 sharding — 2-shard version with shape-compatibility hypothesis.
    Both a, b have shape [shard, H], sh_shard = [shard, H], sh_full = [shard*2, H]. -/
theorem fw_view_allGather0_commute_2_of (a b : Tensor) (shard H : Nat)
    (hshard : 0 < shard)
    (ha : a.shape = [shard, H]) (hb : b.shape = [shard, H]) :
    fw_view [shard * 2, H] (allGatherPrimDimN 0 2 0 [a, b])
      = allGatherPrimDimN 0 2 0 [fw_view [shard, H] a, fw_view [shard, H] b] := by
  rw [fw_view_self_eq a [shard, H] ha, fw_view_self_eq b [shard, H] hb]
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, H] := by
    simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, H] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, H] hhead_ab]; simp [List.set, List.getD]
  exact fw_view_self_eq (allGatherPrimDimN 0 2 0 [a, b]) [shard * 2, H] hG_shape

/-- Softmax commutes with dim-0 sharding on 2-D `[S, E]` tensors, in the sense that
    row `(r*S + i)` of `softmax (gather0 [a, b])` equals row `i` of `softmax (a_or_b)`.
    Stated at the flat-value level: at flat index `(r*S + i) * E + e`, both are equal. -/
private theorem softmax_gather0_valAt (a b : Tensor) (S E : Nat)
    (hS : 0 < S) (hE : 0 < E)
    (ha : a.shape = [S, E]) (hb : b.shape = [S, E])
    (r : Nat) (hr : r < 2) (i : Nat) (hi : i < S) (e : Nat) (he : e < E) :
    valAt (softmax (allGatherPrimDimN 0 2 0 [a, b])) ((r * S + i) * E + e)
      = valAt (softmax ([a, b].getD r (zeroTensor [S, E]))) (i * E + e) := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [S, E] := by
    simp [ha]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [S * 2, E] := by
    rw [allGatherPrimDimN_shape 0 2 _ [S, E] hhead_ab]; simp [List.set, List.getD]
  have hshapes_ab : ∀ r' (_ : r' < 2),
      (([a, b].getD r' (zeroTensor [S, E]))).shape = [S, E] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
  set ea := [a, b].getD r (zeroTensor [S, E]) with hea_def
  have hea_shape : ea.shape = [S, E] := hshapes_ab r hr
  have hbound_G : (r * S + i) * E + e < prodShape [S * 2, E] := by
    simp [prodShape]
    have h1 : (r * S + i) * E + e < (r * S + i) * E + E := by omega
    have h2 : (r * S + i) * E + E = (r * S + i + 1) * E := by ring
    have h3 : (r * S + i + 1) * E ≤ S * 2 * E := Nat.mul_le_mul_right E (by nlinarith)
    linarith
  have hbound_ea : i * E + e < prodShape [S, E] := by
    simp [prodShape]
    have h1 : i * E + e < i * E + E := by omega
    have h2 : i * E + E = (i + 1) * E := by ring
    have h3 : (i + 1) * E ≤ S * E := Nat.mul_le_mul_right E (by omega)
    linarith
  have he_mod : e % E = e := Nat.mod_eq_of_lt he
  have hLHS : valAt (softmax (allGatherPrimDimN 0 2 0 [a, b])) ((r * S + i) * E + e)
      = (if hexp : (∑ j ∈ Finset.range E, expFn
              (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * S + i) * E + j))) = 0 then 0
         else expFn (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * S + i) * E + e))
              / (∑ j ∈ Finset.range E, expFn
                  (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * S + i) * E + j)))) := by
    unfold softmax
    rw [hG_ab]
    rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, prodShape]; simpa [prodShape] using hbound_G)]
    simp [Tensor.mkShape, List.reverse]
    have hE_ne : E ≠ 0 := Nat.pos_iff_ne_zero.mp hE
    have hdiv : ((r * S + i) * E + e) / E = r * S + i := by
      have h1 : ((r * S + i) * E + e) / E = e / E + (r * S + i) := by
        rw [Nat.add_comm, Nat.add_mul_div_right e (r * S + i) hE]
      rw [h1, Nat.div_eq_of_lt he]; ring
    have hmod : ((r * S + i) * E + e) % E = e := by
      have h1 : ((r * S + i) * E + e) % E = e % E := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt he]
    simp [hE_ne, hdiv, hmod, he_mod]
  have hRHS : valAt (softmax ea) (i * E + e)
      = (if hexp : (∑ j ∈ Finset.range E, expFn (valAt ea (i * E + j))) = 0 then 0
         else expFn (valAt ea (i * E + e))
              / (∑ j ∈ Finset.range E, expFn (valAt ea (i * E + j)))) := by
    unfold softmax
    rw [hea_shape]
    rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, prodShape]; simpa [prodShape] using hbound_ea)]
    simp [Tensor.mkShape, List.reverse]
    have hE_ne : E ≠ 0 := Nat.pos_iff_ne_zero.mp hE
    have hdiv : (i * E + e) / E = i := by
      have h1 : (i * E + e) / E = e / E + i := by
        rw [Nat.add_comm, Nat.add_mul_div_right e i hE]
      rw [h1, Nat.div_eq_of_lt he]; ring
    have hmod : (i * E + e) % E = e := by
      have h1 : (i * E + e) % E = e % E := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt he]
    simp [hE_ne, hdiv, hmod, he_mod]
  have hgather_eq : ∀ j, j < E →
      valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * S + i) * E + j) = valAt ea (i * E + j) := by
    intro j hj
    rw [hea_def]
    exact allGatherPrimDimN0_valAt 2 S E [a, b]
      (by omega) hS hE hhead_ab hshapes_ab r hr i hi j hj
  rw [hLHS, hRHS]
  have hbase_eq : (∑ j ∈ Finset.range E, expFn (valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * S + i) * E + j)))
        = ∑ j ∈ Finset.range E, expFn (valAt ea (i * E + j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < E := by simp [Finset.mem_range] at hj; exact hj
    rw [hgather_eq j hj_lt]
  have he_eq : valAt (allGatherPrimDimN 0 2 0 [a, b]) ((r * S + i) * E + e) = valAt ea (i * E + e) :=
    hgather_eq e he
  rw [hbase_eq, he_eq]

/-- fw_topk_routing fst commutes with dim-0 sharding — proven under E = numExperts hypothesis.
    Pattern_1 usage: a.shape = b.shape = [S=2048, 64], top_k=n=8, numExperts=k=64. -/
theorem fw_topk_routing_fst_allGather0_commute_2_of (a b : Tensor) (S n k : Nat)
    (hS : 0 < S) (hk : 0 < k)
    (ha : a.shape = [S, k]) (hb : b.shape = [S, k]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).fst
      = allGatherPrimDimN 0 2 0
          [(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [S, k] := by
    simp [ha]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [S * 2, k] := by
    rw [allGatherPrimDimN_shape 0 2 _ [S, k] hhead_ab]; simp [List.set, List.getD]
  have hshapes_ab : ∀ r' (_ : r' < 2),
      (([a, b].getD r' (zeroTensor [S, k]))).shape = [S, k] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
  have hprobs_a_shape : (fw_topk_routing a n k).fst.shape = [S, k] := by
    unfold fw_topk_routing
    simp [Tensor.mkShape]
    rw [ha]; rfl
  have hprobs_b_shape : (fw_topk_routing b n k).fst.shape = [S, k] := by
    unfold fw_topk_routing
    simp [Tensor.mkShape]
    rw [hb]; rfl
  have hhead_probs : (([(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst] : List Tensor).head?.map (fun t => t.shape)).getD [] = [S, k] := by
    simp [hprobs_a_shape]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst]).shape = [S * 2, k] := by
    rw [allGatherPrimDimN_shape 0 2 _ [S, k] hhead_probs]; simp [List.set, List.getD]
  have hLHS_shape : (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).fst.shape = [S * 2, k] := by
    unfold fw_topk_routing
    simp [Tensor.mkShape]
    rw [hG_ab]; rfl
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < S * 2 * k := by simpa [prodShape] using houtIdx
    set row := outIdx / k with hrow_def
    set e := outIdx % k with he_def
    have he_lt : e < k := by rw [he_def]; exact Nat.mod_lt _ hk
    have hrow_lt : row < S * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul hk]; linarith
    set r := row / S with hr_def
    set i := row % S with hi_def
    have hi_lt : i < S := by rw [hi_def]; exact Nat.mod_lt _ hS
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hS]; linarith
    have houtIdx_eq : outIdx = (r * S + i) * k + e := by
      subst r i e row
      have h1 : S * (outIdx / k / S) + outIdx / k % S = outIdx / k := Nat.div_add_mod (outIdx / k) S
      have h2 : k * (outIdx / k) + outIdx % k = outIdx := Nat.div_add_mod outIdx k
      calc outIdx = k * (outIdx / k) + outIdx % k := h2.symm
        _ = k * (S * (outIdx / k / S) + outIdx / k % S) + outIdx % k := by rw [h1]
        _ = (outIdx / k / S * S + outIdx / k % S) * k + outIdx % k := by ring
    have hLHS_val : valAt (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).fst outIdx
        = (let gate_scores := softmax (allGatherPrimDimN 0 2 0 [a, b])
           let l := if k = 0 then 0 else outIdx / k
           let e' := if k = 0 then 0 else outIdx % k
           if inTopK gate_scores k n l e' then
             let denom := topkScoreSum gate_scores k n l
             if denom = 0 then 0
             else topkScoresAt gate_scores k l e' / denom
           else 0) := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show outIdx < prodShape [(allGatherPrimDimN 0 2 0 [a, b]).shape.head?.getD 0, k]
        rw [hG_ab]
        simp [prodShape]; linarith)]
    have hRHS_val : valAt (allGatherPrimDimN 0 2 0 [(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst]) outIdx
        = valAt ([(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst].getD r
            (zeroTensor [S, k])) (i * k + e) := by
      rw [houtIdx_eq]
      have hshapes_probs : ∀ r' (_ : r' < 2),
          (([(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst].getD r' (zeroTensor [S, k]))).shape = [S, k] := by
        intro r' hr'
        have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
        rcases this with h | h <;> rw [h] <;> simp [List.getD, hprobs_a_shape, hprobs_b_shape]
      exact allGatherPrimDimN0_valAt 2 S k [(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst]
        (by omega) hS hk hhead_probs hshapes_probs r hr_lt i hi_lt e he_lt
    rw [hRHS_val]
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    have hgetD_probs :
        [(fw_topk_routing a n k).fst, (fw_topk_routing b n k).fst].getD r (zeroTensor [S, k]) =
        (fw_topk_routing ([a, b].getD r (zeroTensor [S, k])) n k).fst := by
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_probs]
    set ea := [a, b].getD r (zeroTensor [S, k]) with hea_def
    have hea_shape : ea.shape = [S, k] := hshapes_ab r hr_lt
    have hlocal_bound : i * k + e < S * k := by
      have h1 : i * k + e < i * k + k := by omega
      have h2 : i * k + k = (i + 1) * k := by ring
      have h3 : (i + 1) * k ≤ S * k := Nat.mul_le_mul_right _ (by omega)
      omega
    have hRHS_local_val : valAt (fw_topk_routing ea n k).fst (i * k + e)
        = (let gate_scores := softmax ea
           let l := if k = 0 then 0 else (i * k + e) / k
           let e' := if k = 0 then 0 else (i * k + e) % k
           if inTopK gate_scores k n l e' then
             let denom := topkScoreSum gate_scores k n l
             if denom = 0 then 0
             else topkScoresAt gate_scores k l e' / denom
           else 0) := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show i * k + e < prodShape [ea.shape.head?.getD 0, k]
        rw [hea_shape]; simp [prodShape]; linarith)]
    rw [hLHS_val, hRHS_local_val]
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    have hout_div : outIdx / k = r * S + i := by
      rw [houtIdx_eq]
      have h1 : ((r * S + i) * k + e) / k = e / k + (r * S + i) := by
        rw [Nat.add_comm, Nat.add_mul_div_right e (r * S + i) hk]
      rw [h1, Nat.div_eq_of_lt he_lt]; ring
    have hout_mod : outIdx % k = e := by
      rw [houtIdx_eq]
      have h1 : ((r * S + i) * k + e) % k = e % k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt he_lt]
    have hloc_div : (i * k + e) / k = i := by
      have h1 : (i * k + e) / k = e / k + i := by
        rw [Nat.add_comm, Nat.add_mul_div_right e i hk]
      rw [h1, Nat.div_eq_of_lt he_lt]; ring
    have hloc_mod : (i * k + e) % k = e := by
      have h1 : (i * k + e) % k = e % k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt he_lt]
    simp only [hk_ne, hout_div, hout_mod, hloc_div, hloc_mod, if_false]
    -- Row-local reductions via softmax_gather0_valAt.
    have hscores_eq : ∀ e' < k,
        topkScoresAt (softmax (allGatherPrimDimN 0 2 0 [a, b])) k (r * S + i) e'
          = topkScoresAt (softmax ea) k i e' := by
      intro e' he'
      unfold topkScoresAt
      rw [hea_def]
      exact softmax_gather0_valAt a b S k hS hk ha hb r hr_lt i hi_lt e' he'
    have hrank_eq : ∀ e' < k,
        topkRank (softmax (allGatherPrimDimN 0 2 0 [a, b])) k (r * S + i) e'
          = topkRank (softmax ea) k i e' := by
      intro e' he'
      unfold topkRank
      congr 1
      apply Finset.filter_congr
      intro e'' he''
      have he''_lt : e'' < k := by simp [Finset.mem_range] at he''; exact he''
      rw [hscores_eq e'' he''_lt, hscores_eq e' he']
    have hinTopK_eq : ∀ e' < k,
        inTopK (softmax (allGatherPrimDimN 0 2 0 [a, b])) k n (r * S + i) e'
          = inTopK (softmax ea) k n i e' := by
      intro e' he'
      unfold inTopK
      rw [hrank_eq e' he']
    have hsum_eq :
        topkScoreSum (softmax (allGatherPrimDimN 0 2 0 [a, b])) k n (r * S + i)
          = topkScoreSum (softmax ea) k n i := by
      unfold topkScoreSum
      apply Finset.sum_congr rfl
      intro e' he'
      have he'_lt : e' < k := by simp [Finset.mem_range] at he'; exact he'
      rw [hinTopK_eq e' he'_lt, hscores_eq e' he'_lt]
    rw [hscores_eq e he_lt, hinTopK_eq e he_lt, hsum_eq]

/-- fw_topk_routing snd_fst commutes with dim-0 sharding — proven under E = numExperts.
    Analogous to fw_topk_routing_fst_allGather0_commute_2_of. -/
theorem fw_topk_routing_snd_fst_allGather0_commute_2_of (a b : Tensor) (S n k : Nat)
    (hS : 0 < S) (hk : 0 < k)
    (ha : a.shape = [S, k]) (hb : b.shape = [S, k]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).snd.fst
      = allGatherPrimDimN 0 2 0
          [(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [S, k] := by
    simp [ha]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [S * 2, k] := by
    rw [allGatherPrimDimN_shape 0 2 _ [S, k] hhead_ab]; simp [List.set, List.getD]
  have hshapes_ab : ∀ r' (_ : r' < 2),
      (([a, b].getD r' (zeroTensor [S, k]))).shape = [S, k] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
  have hmap_a_shape : (fw_topk_routing a n k).snd.fst.shape = [S, k] := by
    unfold fw_topk_routing
    simp [Tensor.mkShape]
    rw [ha]; rfl
  have hmap_b_shape : (fw_topk_routing b n k).snd.fst.shape = [S, k] := by
    unfold fw_topk_routing
    simp [Tensor.mkShape]
    rw [hb]; rfl
  have hhead_map : (([(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst] : List Tensor).head?.map (fun t => t.shape)).getD [] = [S, k] := by
    simp [hmap_a_shape]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst]).shape = [S * 2, k] := by
    rw [allGatherPrimDimN_shape 0 2 _ [S, k] hhead_map]; simp [List.set, List.getD]
  have hLHS_shape : (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).snd.fst.shape = [S * 2, k] := by
    unfold fw_topk_routing
    simp [Tensor.mkShape]
    rw [hG_ab]; rfl
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < S * 2 * k := by simpa [prodShape] using houtIdx
    set row := outIdx / k with hrow_def
    set e := outIdx % k with he_def
    have he_lt : e < k := by rw [he_def]; exact Nat.mod_lt _ hk
    have hrow_lt : row < S * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul hk]; linarith
    set r := row / S with hr_def
    set i := row % S with hi_def
    have hi_lt : i < S := by rw [hi_def]; exact Nat.mod_lt _ hS
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hS]; linarith
    have houtIdx_eq : outIdx = (r * S + i) * k + e := by
      subst r i e row
      have h1 : S * (outIdx / k / S) + outIdx / k % S = outIdx / k := Nat.div_add_mod (outIdx / k) S
      have h2 : k * (outIdx / k) + outIdx % k = outIdx := Nat.div_add_mod outIdx k
      calc outIdx = k * (outIdx / k) + outIdx % k := h2.symm
        _ = k * (S * (outIdx / k / S) + outIdx / k % S) + outIdx % k := by rw [h1]
        _ = (outIdx / k / S * S + outIdx / k % S) * k + outIdx % k := by ring
    have hLHS_val : valAt (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) n k).snd.fst outIdx
        = (let gate_scores := softmax (allGatherPrimDimN 0 2 0 [a, b])
           let l := if k = 0 then 0 else outIdx / k
           let e' := if k = 0 then 0 else outIdx % k
           if inTopK gate_scores k n l e' then (1 : Scalar) else 0) := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show outIdx < prodShape [(allGatherPrimDimN 0 2 0 [a, b]).shape.head?.getD 0, k]
        rw [hG_ab]
        simp [prodShape]; linarith)]
    have hRHS_val : valAt (allGatherPrimDimN 0 2 0 [(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst]) outIdx
        = valAt ([(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst].getD r
            (zeroTensor [S, k])) (i * k + e) := by
      rw [houtIdx_eq]
      have hshapes_map : ∀ r' (_ : r' < 2),
          (([(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst].getD r' (zeroTensor [S, k]))).shape = [S, k] := by
        intro r' hr'
        have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
        rcases this with h | h <;> rw [h] <;> simp [List.getD, hmap_a_shape, hmap_b_shape]
      exact allGatherPrimDimN0_valAt 2 S k [(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst]
        (by omega) hS hk hhead_map hshapes_map r hr_lt i hi_lt e he_lt
    rw [hRHS_val]
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    have hgetD_map :
        [(fw_topk_routing a n k).snd.fst, (fw_topk_routing b n k).snd.fst].getD r (zeroTensor [S, k]) =
        (fw_topk_routing ([a, b].getD r (zeroTensor [S, k])) n k).snd.fst := by
      rcases hr_cases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_map]
    set ea := [a, b].getD r (zeroTensor [S, k]) with hea_def
    have hea_shape : ea.shape = [S, k] := hshapes_ab r hr_lt
    have hlocal_bound : i * k + e < S * k := by
      have h1 : i * k + e < i * k + k := by omega
      have h2 : i * k + k = (i + 1) * k := by ring
      have h3 : (i + 1) * k ≤ S * k := Nat.mul_le_mul_right _ (by omega)
      omega
    have hRHS_local_val : valAt (fw_topk_routing ea n k).snd.fst (i * k + e)
        = (let gate_scores := softmax ea
           let l := if k = 0 then 0 else (i * k + e) / k
           let e' := if k = 0 then 0 else (i * k + e) % k
           if inTopK gate_scores k n l e' then (1 : Scalar) else 0) := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show i * k + e < prodShape [ea.shape.head?.getD 0, k]
        rw [hea_shape]; simp [prodShape]; linarith)]
    rw [hLHS_val, hRHS_local_val]
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    have hout_div : outIdx / k = r * S + i := by
      rw [houtIdx_eq]
      have h1 : ((r * S + i) * k + e) / k = e / k + (r * S + i) := by
        rw [Nat.add_comm, Nat.add_mul_div_right e (r * S + i) hk]
      rw [h1, Nat.div_eq_of_lt he_lt]; ring
    have hout_mod : outIdx % k = e := by
      rw [houtIdx_eq]
      have h1 : ((r * S + i) * k + e) % k = e % k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt he_lt]
    have hloc_div : (i * k + e) / k = i := by
      have h1 : (i * k + e) / k = e / k + i := by
        rw [Nat.add_comm, Nat.add_mul_div_right e i hk]
      rw [h1, Nat.div_eq_of_lt he_lt]; ring
    have hloc_mod : (i * k + e) % k = e := by
      have h1 : (i * k + e) % k = e % k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt he_lt]
    simp only [hk_ne, hout_div, hout_mod, hloc_div, hloc_mod, if_false]
    have hscores_eq : ∀ e' < k,
        topkScoresAt (softmax (allGatherPrimDimN 0 2 0 [a, b])) k (r * S + i) e'
          = topkScoresAt (softmax ea) k i e' := by
      intro e' he'
      unfold topkScoresAt
      rw [hea_def]
      exact softmax_gather0_valAt a b S k hS hk ha hb r hr_lt i hi_lt e' he'
    have hrank_eq : ∀ e' < k,
        topkRank (softmax (allGatherPrimDimN 0 2 0 [a, b])) k (r * S + i) e'
          = topkRank (softmax ea) k i e' := by
      intro e' he'
      unfold topkRank
      congr 1
      apply Finset.filter_congr
      intro e'' he''
      have he''_lt : e'' < k := by simp [Finset.mem_range] at he''; exact he''
      rw [hscores_eq e'' he''_lt, hscores_eq e' he']
    have hinTopK_eq : ∀ e' < k,
        inTopK (softmax (allGatherPrimDimN 0 2 0 [a, b])) k n (r * S + i) e'
          = inTopK (softmax ea) k n i e' := by
      intro e' he'
      unfold inTopK
      rw [hrank_eq e' he']
    rw [hinTopK_eq e he_lt]

-- DELETED (2026-07-04): `Pattern_1_labelsAxiom` — was `∀ (y : Tensor) (vocab l : Nat), valAt y l < vocab`,
-- a vacuous axiom (take vocab=0 → False). Replaced by statement-level hypothesis
-- `hlabels_from_caller` in `goal_1_stmt_with_labels` (surfaced to verifier caller).

/-- 3-D variant of `allGatherPrimDimN0_valAt` for shape `[E, h, d]`:
    at flat idx `((r * E + eLocal) * h + hi) * d + di`, reads shard r at local flat
    `(eLocal * h + hi) * d + di`. Direct unfold proof. -/
private theorem allGatherPrimDimN0_valAt_3d (E h d : Nat) (hE : 0 < E) (hh : 0 < h) (hd : 0 < d)
    (Ws : List Tensor)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [E, h, d])
    (r : Nat) (hr : r < 2) (eLocal : Nat) (heLocal : eLocal < E)
    (hi : Nat) (hi_lt : hi < h) (di : Nat) (hdi_lt : di < d) :
    valAt (allGatherPrimDimN 0 2 0 Ws) (((r * E + eLocal) * h + hi) * d + di)
      = valAt (Ws.getD r (zeroTensor [E, h, d])) ((eLocal * h + hi) * d + di) := by
  unfold allGatherPrimDimN
  rw [hhead]
  simp only [List.drop, List.foldl, List.getD]
  -- shape after set = [E * 2, h, d]
  have hout_bound : ((r * E + eLocal) * h + hi) * d + di < E * 2 * h * d := by
    have hstep1 : ((r * E + eLocal) * h + hi) * d + di
        < ((r * E + eLocal) * h + hi + 1) * d := by
      calc ((r * E + eLocal) * h + hi) * d + di
          < ((r * E + eLocal) * h + hi) * d + d := by omega
        _ = ((r * E + eLocal) * h + hi + 1) * d := by ring
    have hstep2 : (r * E + eLocal) * h + hi + 1 ≤ (r * E + eLocal + 1) * h := by
      have : (r * E + eLocal + 1) * h = (r * E + eLocal) * h + h := by ring
      omega
    have hstep3 : (r * E + eLocal + 1) ≤ E * 2 := by
      calc r * E + eLocal + 1 ≤ r * E + E := by omega
        _ = (r + 1) * E := by ring
        _ ≤ 2 * E := Nat.mul_le_mul_right _ (by omega)
        _ = E * 2 := by ring
    calc ((r * E + eLocal) * h + hi) * d + di
        < ((r * E + eLocal) * h + hi + 1) * d := hstep1
      _ ≤ (r * E + eLocal + 1) * h * d := by
        have := Nat.mul_le_mul_right d hstep2
        nlinarith
      _ ≤ E * 2 * h * d := by
        have := Nat.mul_le_mul_right (h * d) hstep3
        nlinarith
  rw [valAt_of_lt _ _ (by
    show ((r * E + eLocal) * h + hi) * d + di < prodShape ([E, h, d].set 0 (([E, h, d].getD 0 0) * 2))
    simp [prodShape, List.set, List.getD, List.foldl]
    linarith [hout_bound])]
  simp [Tensor.mkShape, List.set, List.getD, List.drop, List.foldl]
  -- The mkShape function computes valAt (Ws.getD r' _) (preIdx * dimStride + jLocal * postStride + k)
  -- shardShape=[E,h,d], gatherDim=0.
  -- dimSize = E, fullDimSize = E*2, postStride = h*d, dimStride = E*h*d, fullDimStride = E*2*h*d
  set idx := ((r * E + eLocal) * h + hi) * d + di with hidx_def
  have hE_ne : E ≠ 0 := Nat.pos_iff_ne_zero.mp hE
  have hh_ne : h ≠ 0 := Nat.pos_iff_ne_zero.mp hh
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hE2_ne : E * 2 ≠ 0 := Nat.mul_ne_zero hE_ne (by omega)
  have hhd_ne : h * d ≠ 0 := Nat.mul_ne_zero hh_ne hd_ne
  have hEhd_ne : E * 2 * (h * d) ≠ 0 := Nat.mul_ne_zero hE2_ne hhd_ne
  -- Show: idx / (E*2*(h*d)) = 0 (since idx < E*2*h*d)
  have hidx_bound2 : idx < E * 2 * (h * d) := by
    rw [hidx_def]; simp only [Nat.mul_assoc]; convert hout_bound using 1; ring
  have hpre_div : idx / (E * 2 * (h * d)) = 0 := Nat.div_eq_of_lt hidx_bound2
  have hpre_mod : idx % (E * 2 * (h * d)) = idx := Nat.mod_eq_of_lt hidx_bound2
  -- jFull = idx / (h*d)
  have hjFull_val : idx / (h * d) = r * E + eLocal := by
    rw [hidx_def]
    have h1 : ((r * E + eLocal) * h + hi) * d + di
        = ((r * E + eLocal) * h + hi) * d + di := rfl
    have h2 : ((r * E + eLocal) * h + hi) * d + di = (r * E + eLocal) * (h * d) + (hi * d + di) := by
      ring
    rw [h2]
    have h_small_lt : hi * d + di < h * d := by
      calc hi * d + di < hi * d + d := by omega
        _ = (hi + 1) * d := by ring
        _ ≤ h * d := Nat.mul_le_mul_right _ (by omega)
    have h_div : ((r * E + eLocal) * (h * d) + (hi * d + di)) / (h * d)
        = (hi * d + di) / (h * d) + (r * E + eLocal) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity)]
    rw [h_div, Nat.div_eq_of_lt h_small_lt]; ring
  -- k = idx % (h*d)
  have hk_val : idx % (h * d) = hi * d + di := by
    rw [hidx_def]
    have h2 : ((r * E + eLocal) * h + hi) * d + di = (r * E + eLocal) * (h * d) + (hi * d + di) := by
      ring
    rw [h2]
    have h_small_lt : hi * d + di < h * d := by
      calc hi * d + di < hi * d + d := by omega
        _ = (hi + 1) * d := by ring
        _ ≤ h * d := Nat.mul_le_mul_right _ (by omega)
    have h_mod : ((r * E + eLocal) * (h * d) + (hi * d + di)) % (h * d)
        = (hi * d + di) % (h * d) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h_mod, Nat.mod_eq_of_lt h_small_lt]
  -- r' = jFull / E = r (since eLocal < E)
  have hr'_val : (r * E + eLocal) / E = r := by
    have h1 : (r * E + eLocal) / E = eLocal / E + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right eLocal r hE]
    rw [h1, Nat.div_eq_of_lt heLocal]; ring
  -- jLocal = jFull % E = eLocal
  have hjLocal_val : (r * E + eLocal) % E = eLocal := by
    have h1 : (r * E + eLocal) % E = eLocal % E := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h1, Nat.mod_eq_of_lt heLocal]
  -- Also idx % (E * 2 * (h * d)) / (h * d) = idx / (h * d) since idx < E*2*(h*d)
  -- And idx % (E * 2 * (h * d)) % (h * d) = idx % (h * d) similarly
  simp [hE_ne, hh_ne, hd_ne, hE2_ne, hhd_ne, hEhd_ne, hpre_div, hpre_mod, hjFull_val, hk_val,
        hr'_val, hjLocal_val]
  -- Remaining: valAt (Ws.getD r _) (0 * (E * (h * d)) + eLocal * (h * d) + (hi * d + di))
  --        =? valAt (Ws.getD r _) ((eLocal * h + hi) * d + di)
  ring_nf



/-- The MoE `fw_all2all_moe_gmm` sum body at fixed (l, h_col, eLocal), abstracted for reuse.
    Note: routing indices use `e = start + eLocal` while weight indices use `eLocal` directly. -/
private noncomputable def moe_gmm_term
    (input rp rm w13 w2 : Tensor)
    (numExp start eLocal l h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar) : Scalar :=
  let e := start + eLocal
  let mask := valAt rm (l * numExp + e)
  if mask = 0 then 0
  else
    let prob := valAt rp (l * numExp + e)
    prob * ∑ d ∈ Finset.range h_inner,
      let gateRaw := ∑ k ∈ Finset.range hModel,
        valAt input (l * hModel + k) *
        valAt w13 ((eLocal * w13Mid + d) * hModel + k)
      let upRaw := ∑ k ∈ Finset.range hModel,
        valAt input (l * hModel + k) *
        valAt w13 ((eLocal * w13Mid + (h_inner + d)) * hModel + k)
      let gateClamped := min swigluLimit gateRaw
      let upClamped   := max (-swigluLimit) (min swigluLimit upRaw)
      let swigluVal   := siluScalar gateClamped * upClamped
      swigluVal * valAt w2 ((eLocal * hModel + h_col) * h_inner + d)

/-- `moe_gmm_term` is congruent under equal valAt of all its inputs at relevant indices.
    Both sides use the same `eLocal` — this is a "same body, different tensors" lemma. -/
private theorem moe_gmm_term_congr
    (input₁ rp₁ rm₁ w13₁ w2₁ input₂ rp₂ rm₂ w13₂ w2₂ : Tensor)
    (numExp start eLocal l₁ l₂ h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar)
    (hmask : valAt rm₁ (l₁ * numExp + (start + eLocal)) = valAt rm₂ (l₂ * numExp + (start + eLocal)))
    (hprob : valAt rp₁ (l₁ * numExp + (start + eLocal)) = valAt rp₂ (l₂ * numExp + (start + eLocal)))
    (hinput : ∀ k, k < hModel → valAt input₁ (l₁ * hModel + k) = valAt input₂ (l₂ * hModel + k))
    (hw13 : ∀ d k, d < h_inner → k < hModel →
      valAt w13₁ ((eLocal * w13Mid + d) * hModel + k) = valAt w13₂ ((eLocal * w13Mid + d) * hModel + k))
    (hw13' : ∀ d k, d < h_inner → k < hModel →
      valAt w13₁ ((eLocal * w13Mid + (h_inner + d)) * hModel + k) = valAt w13₂ ((eLocal * w13Mid + (h_inner + d)) * hModel + k))
    (hw2 : ∀ d, d < h_inner →
      valAt w2₁ ((eLocal * hModel + h_col) * h_inner + d) = valAt w2₂ ((eLocal * hModel + h_col) * h_inner + d)) :
    moe_gmm_term input₁ rp₁ rm₁ w13₁ w2₁ numExp start eLocal l₁ h_col hModel h_inner w13Mid swigluLimit
      = moe_gmm_term input₂ rp₂ rm₂ w13₂ w2₂ numExp start eLocal l₂ h_col hModel h_inner w13Mid swigluLimit := by
  unfold moe_gmm_term
  simp only [hmask]
  by_cases h : valAt rm₂ (l₂ * numExp + (start + eLocal)) = 0
  · simp [h]
  · simp only [h, if_false]
    rw [hprob]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hd_lt : d < h_inner := by simp [Finset.mem_range] at hd; exact hd
    have hgate_eq : (∑ k ∈ Finset.range hModel,
        valAt input₁ (l₁ * hModel + k) *
        valAt w13₁ ((eLocal * w13Mid + d) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input₂ (l₂ * hModel + k) *
          valAt w13₂ ((eLocal * w13Mid + d) * hModel + k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk_lt : k < hModel := by simp [Finset.mem_range] at hk; exact hk
      rw [hinput k hk_lt, hw13 d k hd_lt hk_lt]
    have hup_eq : (∑ k ∈ Finset.range hModel,
        valAt input₁ (l₁ * hModel + k) *
        valAt w13₁ ((eLocal * w13Mid + (h_inner + d)) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input₂ (l₂ * hModel + k) *
          valAt w13₂ ((eLocal * w13Mid + (h_inner + d)) * hModel + k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk_lt : k < hModel := by simp [Finset.mem_range] at hk; exact hk
      rw [hinput k hk_lt, hw13' d k hd_lt hk_lt]
    rw [hgate_eq, hup_eq, hw2 d hd_lt]

/-- `fw_all2all_moe_gmm` value at flat idx `l * hModel + h_col` (with `l < lDim, h_col < hModel`)
    equals the sum of `moe_gmm_term` over the local expert range. -/
private theorem fw_all2all_moe_gmm_valAt
    (input rp rm w13 w2 : Tensor)
    (L hModel numExp E_total start endE topK t_dim d_dim : Nat)
    (hL : 0 < L) (hhModel : 0 < hModel) (hnE : 0 < numExp) (hE_total : 0 < E_total)
    (hstart_le_end : start ≤ endE)
    (ht_even : t_dim = 2 * d_dim)
    (hinput_shape : input.shape = [L, hModel])
    (hrp_shape : rp.shape = [L, numExp])
    (hw13_shape : w13.shape = [E_total, t_dim, hModel])
    (l : Nat) (hl : l < L) (h_col : Nat) (hh_col : h_col < hModel)
    (swigluLimit : Scalar) :
    valAt (fw_all2all_moe_gmm input rp rm w13 w2 numExp start endE topK swigluLimit) (l * hModel + h_col)
      = ∑ eLocal ∈ Finset.range (endE - start),
          moe_gmm_term input rp rm w13 w2 numExp start eLocal l h_col hModel d_dim t_dim swigluLimit := by
  unfold fw_all2all_moe_gmm
  simp only [Tensor.mkShape, valAt]
  -- Bound check for dif_pos
  have hbound : l * hModel + h_col < prodShape [(input.shape.head?).getD 0, (input.shape.reverse.head?).getD 0] := by
    rw [hinput_shape]
    simp [prodShape, List.reverse_cons]
    calc l * hModel + h_col < l * hModel + hModel := by omega
      _ = (l + 1) * hModel := by ring
      _ ≤ L * hModel := Nat.mul_le_mul_right _ (by omega)
  rw [dif_pos hbound]
  -- Now the RHS of the equality is the sum expressed in terms of moe_gmm_term
  -- After simp/unfold, LHS also becomes the same sum structure
  -- The key is that hModel, w13Mid, h_inner, numExp all resolve to what moe_gmm_term expects
  have hModel_eq : (input.shape.reverse.head?).getD 0 = hModel := by
    rw [hinput_shape]; simp
  have hw13Mid_eq : (w13.shape.drop 1).head?.getD 0 = t_dim := by
    rw [hw13_shape]; simp
  have hnumExp_eq : (rp.shape.drop 1).head?.getD 0 = numExp := by
    rw [hrp_shape]; simp
  have hlDim_eq : (input.shape.head?).getD 0 = L := by
    rw [hinput_shape]; simp
  have hh_inner_eq : t_dim / 2 = d_dim := by rw [ht_even]; omega
  -- The valAt (h_col comes from l*hModel+h_col) — compute h = idx % hModel, l' = idx / hModel
  have hh_eq : (l * hModel + h_col) % hModel = h_col := by
    have h1 : (l * hModel + h_col) % hModel = h_col % hModel := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h1, Nat.mod_eq_of_lt hh_col]
  have hl'_eq : (l * hModel + h_col) / hModel = l := by
    have h1 : (l * hModel + h_col) / hModel = h_col / hModel + l := by
      rw [Nat.add_comm, Nat.add_mul_div_right h_col l hhModel]
    rw [h1, Nat.div_eq_of_lt hh_col]; ring
  -- Now expand both sides via the moe_gmm_term unfolding
  unfold moe_gmm_term
  simp only [hModel_eq, hw13Mid_eq, hnumExp_eq, hh_inner_eq, hh_eq, hl'_eq]
  -- Both sides are now sums; the body has raw `if h : ... then val else 0` on LHS
  -- and `valAt` on RHS. Unfold valAt so both match.
  simp only [valAt]

/-! ### Upstream-faithful sharding-commute for `fw_all2all_moe_gmm_full`.

The old `fw_all2all_moe_gmm_split_commute_2_of` theorem (still below for legacy
reference) proves the sharding commute for `fw_all2all_moe_gmm` (the per-rank
partial variant), but required routing-map disjointness axioms
(`Pattern_1_rma/rmbDisjointAxiom`) that were themselves vacuous — universally
quantified over routing_map without any binding to the actual dispatched form.

The upstream-faithful `fw_all2all_moe_gmm_full` doesn't have this problem:
both LHS and RHS sum over the FULL expert range `[0, numExp)` using the same
gathered `w13_full`/`w2_full` weights. The sharding commute reduces to
"input/rp/rm split along L axis + gather = identity at each L slot".

DELETED: `Pattern_1_rmaDisjointAxiom` and `Pattern_1_rmbDisjointAxiom` — no
longer needed because the disjointness constraint is now encoded
by-construction in the allGather layout of `w13s`/`w2s`. -/

/-- Bridge lemma: `fw_all2all_moe_gmm` on gathered weights (same numRanks for
    both w13s and w2s) = `fw_all2all_moe_gmm_full` on the shard lists. Follows
    from `_full`'s definition (gather-then-call-old-kernel). Requires
    `w13s.length = w2s.length` because the two `numRanks` in the RHS come from
    the same `let` in `_full`. -/
theorem fw_all2all_moe_gmm_eq_full_on_shards
    (input rp rm : Tensor) (w13s w2s : List Tensor)
    (numExp topK : Nat) (swigluLimit : Scalar)
    (hlen : w13s.length = w2s.length) :
    fw_all2all_moe_gmm input rp rm
        (allGatherPrimDimN 0 w13s.length 0 w13s)
        (allGatherPrimDimN 0 w2s.length 0 w2s)
        numExp 0 numExp topK swigluLimit
      = fw_all2all_moe_gmm_full input rp rm w13s w2s numExp topK swigluLimit := by
  unfold fw_all2all_moe_gmm_full
  rw [hlen]

/-- Upstream-faithful sharding commute for `fw_all2all_moe_gmm_full` when
    inputs/routing tensors are split along L axis across 2 ranks, weights
    already in per-rank shard form. Statement: gather-of-inputs, applied to
    full kernel with sharded weights, equals gather-of-per-rank-outputs
    (each per-rank output uses the same weight shards).

    Provable pointwise: kernel body at output flat idx `l * hM + h` only
    reads row `l` of input/rp/rm. Both sides use identical
    `allGatherPrimDimN 0 2 0 [w13_a, w13_b]` (and w2). LHS's `l ∈ [0, 2L)`
    splits by allGather into `l < L → in_a[l]` vs `l ≥ L → in_b[l-L]`; RHS
    mirrors via its own gather. No disjointness needed.

    NOTE (2026-07-04): pointwise valAt proof deferred. `sorry` is the ONLY
    remaining axiomatic hole in Pattern_1 besides the labels-training-data
    axiom (`Pattern_1_labelsAxiom`). Statement is upstream-faithful (no
    disjointness hypothesis, weights are gathered on both sides). -/
theorem fw_all2all_moe_gmm_full_split_commute_2
    (input_a input_b rp_a rp_b rm_a rm_b w13_a w13_b w2_a w2_b : Tensor)
    (L hM E_shard topK t_dim d_dim : Nat) (swigluLimit : Scalar)
    (hL : 0 < L) (hhM : 0 < hM) (hE : 0 < E_shard) (ht : 0 < t_dim) (hd : 0 < d_dim)
    (ht_even : t_dim = 2 * d_dim)
    (hinput_a : input_a.shape = [L, hM]) (hinput_b : input_b.shape = [L, hM])
    (hrp_a : rp_a.shape = [L, E_shard * 2]) (hrp_b : rp_b.shape = [L, E_shard * 2])
    (hrm_a : rm_a.shape = [L, E_shard * 2]) (hrm_b : rm_b.shape = [L, E_shard * 2])
    (hw13_a : w13_a.shape = [E_shard, t_dim, hM]) (hw13_b : w13_b.shape = [E_shard, t_dim, hM])
    (hw2_a : w2_a.shape = [E_shard, hM, d_dim]) (hw2_b : w2_b.shape = [E_shard, hM, d_dim]) :
    fw_all2all_moe_gmm_full
        (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [rp_a, rp_b])
        (allGatherPrimDimN 0 2 0 [rm_a, rm_b])
        [w13_a, w13_b] [w2_a, w2_b]
        (E_shard * 2) topK swigluLimit
      = allGatherPrimDimN 0 2 0
          [fw_all2all_moe_gmm_full input_a rp_a rm_a [w13_a, w13_b] [w2_a, w2_b]
              (E_shard * 2) topK swigluLimit,
           fw_all2all_moe_gmm_full input_b rp_b rm_b [w13_a, w13_b] [w2_a, w2_b]
              (E_shard * 2) topK swigluLimit] := by
  -- Unfold both sides to `fw_all2all_moe_gmm` on gathered w13/w2 (same weights).
  unfold fw_all2all_moe_gmm_full
  -- Reduce list length to numeric 2.
  simp only [List.length_cons, List.length_nil, show (0 + 1 + 1 : Nat) = 2 from rfl]
  -- Setup local abbreviations
  set numExp := E_shard * 2 with hnumExp_def
  have hnE : 0 < numExp := by rw [hnumExp_def]; positivity
  set gW13 := allGatherPrimDimN 0 2 0 [w13_a, w13_b] with hgW13_def
  set gW2 := allGatherPrimDimN 0 2 0 [w2_a, w2_b] with hgW2_def
  -- Shape witnesses for allGathers
  have hhead_input : (([input_a, input_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, hM] := by simp [hinput_a]
  have hshapes_input : ∀ r' (_ : r' < 2), (([input_a, input_b].getD r' (zeroTensor [L, hM]))).shape = [L, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hinput_a, hinput_b]
  have hhead_rp : (([rp_a, rp_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, numExp] := by
    simp [hrp_a, hnumExp_def]
  have hshapes_rp : ∀ r' (_ : r' < 2), (([rp_a, rp_b].getD r' (zeroTensor [L, numExp]))).shape = [L, numExp] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hrp_a, hrp_b, hnumExp_def]
  have hhead_rm : (([rm_a, rm_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, numExp] := by
    simp [hrm_a, hnumExp_def]
  have hshapes_rm : ∀ r' (_ : r' < 2), (([rm_a, rm_b].getD r' (zeroTensor [L, numExp]))).shape = [L, numExp] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hrm_a, hrm_b, hnumExp_def]
  -- Gathered input shape [L*2, hM]
  have hG_input : (allGatherPrimDimN 0 2 0 [input_a, input_b]).shape = [L * 2, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, hM] hhead_input]; simp [List.set, List.getD]
  have hG_rp : (allGatherPrimDimN 0 2 0 [rp_a, rp_b]).shape = [L * 2, numExp] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, numExp] hhead_rp]; simp [List.set, List.getD]
  have hG_rm : (allGatherPrimDimN 0 2 0 [rm_a, rm_b]).shape = [L * 2, numExp] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, numExp] hhead_rm]; simp [List.set, List.getD]
  -- Per-rank local moe_gmm output shape [L, hM] (uses gathered gW13/gW2)
  have hloc_a_shape : (fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2
                        numExp 0 numExp topK swigluLimit).shape = [L, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hinput_a]; rfl
  have hloc_b_shape : (fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2
                        numExp 0 numExp topK swigluLimit).shape = [L, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hinput_b]; rfl
  have hhead_loc : (([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
                      fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, hM] := by
    simp [hloc_a_shape]
  have hshapes_loc : ∀ r' (_ : r' < 2),
      (([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
         fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit].getD r' (zeroTensor [L, hM]))).shape = [L, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hloc_a_shape, hloc_b_shape]
  -- LHS / RHS overall shape [L*2, hM]
  have hLHS_shape : (fw_all2all_moe_gmm (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [rp_a, rp_b])
        (allGatherPrimDimN 0 2 0 [rm_a, rm_b])
        gW13 gW2 numExp 0 numExp topK swigluLimit).shape = [L * 2, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hG_input]; rfl
  have hRHS_shape : (allGatherPrimDimN 0 2 0
        [fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
         fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit]).shape = [L * 2, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, hM] hhead_loc]; simp [List.set, List.getD]
  -- Prove tensor equality: shape equal + pointwise value equal
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < L * 2 * hM := by simpa [prodShape] using houtIdx
    -- Decompose outIdx into (row, col) then (r, i)
    set row := outIdx / hM with hrow_def
    set col := outIdx % hM with hcol_def
    have hcol_lt : col < hM := by rw [hcol_def]; exact Nat.mod_lt _ hhM
    have hrow_lt : row < L * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul hhM]; linarith
    have houtIdx_eq : outIdx = row * hM + col := by
      have h1 : hM * (outIdx / hM) + outIdx % hM = outIdx := Nat.div_add_mod outIdx hM
      rw [hrow_def, hcol_def]
      linarith [Nat.mul_comm hM (outIdx / hM)]
    set r := row / L with hr_def
    set i := row % L with hi_def
    have hi_lt : i < L := by rw [hi_def]; exact Nat.mod_lt _ hL
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hL]; linarith
    have hrow_eq : row = r * L + i := by
      have h1 : L * (row / L) + row % L = row := Nat.div_add_mod row L
      rw [hr_def, hi_def]
      linarith [Nat.mul_comm L (row / L)]
    -- Set arithmetic for both sides
    rw [houtIdx_eq, hrow_eq]
    have hrow_lt' : r * L + i < L * 2 := by
      calc r * L + i < r * L + L := by omega
        _ = (r + 1) * L := by ring
        _ ≤ 2 * L := Nat.mul_le_mul_right _ (by omega)
        _ = L * 2 := by ring
    -- LHS valAt using fw_all2all_moe_gmm_valAt (need gW13 shape to obtain t_dim/d_dim decoding)
    have hG_w13 : gW13.shape = [E_shard * 2, t_dim, hM] := by
      rw [hgW13_def]
      have hhead_w13 : (([w13_a, w13_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [E_shard, t_dim, hM] := by simp [hw13_a]
      rw [allGatherPrimDimN_shape 0 2 _ [E_shard, t_dim, hM] hhead_w13]; simp [List.set, List.getD]
    -- Apply fw_all2all_moe_gmm_valAt to LHS with lDim = L*2 (gathered).
    rw [fw_all2all_moe_gmm_valAt _ _ _ _ _ (L * 2) hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
        (by omega) hhM hnE (by omega) (by omega) ht_even hG_input hG_rp hG_w13
        (r * L + i) hrow_lt' col hcol_lt swigluLimit]
    -- Apply allGatherPrimDimN0_valAt to RHS's outer allGather.
    rw [allGatherPrimDimN0_valAt 2 L hM
        [fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
         fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit]
        (by omega) hL hhM hhead_loc hshapes_loc r hr_lt i hi_lt col hcol_lt]
    -- Case on r=0 vs r=1
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    rcases hr_cases with hr0 | hr1
    · -- Case r = 0: RHS = shard 0's moe_gmm on in_a rp_a rm_a with gW13/gW2, sum range [0, numExp)
      rw [hr0]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show ([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
                 fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit].getD 0 (zeroTensor [L, hM]))
                = fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit from rfl]
      rw [fw_all2all_moe_gmm_valAt input_a rp_a rm_a gW13 gW2
          L hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
          hL hhM hnE (by omega) (by omega) ht_even hinput_a hrp_a hG_w13 i hi_lt col hcol_lt swigluLimit]
      -- Both sides: ∑ eLocal ∈ range numExp, moe_gmm_term (X, ..., 0, eLocal, l, col, ...) where l is:
      -- LHS: l = 0*L + i (needs simp)
      -- RHS: l = i
      -- All other args (numExp/start=0/eLocal/hM/d_dim/t_dim/sl) match. Weights (gW13, gW2) same.
      -- Only differ in input/rp/rm: LHS = gather0'd, RHS = a's raw.
      have hsub_zero : E_shard * 2 - 0 = E_shard * 2 := by omega
      rw [hsub_zero]
      apply Finset.sum_congr rfl
      intro x hx
      have hx_lt : x < E_shard * 2 := by simp [Finset.mem_range] at hx; exact hx
      have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
      apply moe_gmm_term_congr
      · -- hmask: valAt (gather0 rm) (i * numExp + (0+x)) = valAt rm_a (i * numExp + (0+x))
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rm_a, rm_b]
            (by omega) hL hnE hhead_rm hshapes_rm 0 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl] at this
        -- `this` is now (i * numExp + x) form; need to expose `(0 + x)` to match moe_gmm_term_congr
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hprob: valAt (gather0 rp) (i * numExp + (0+x)) = valAt rp_a (i * numExp + (0+x))
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rp_a, rp_b]
            (by omega) hL hnE hhead_rp hshapes_rp 0 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl] at this
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hinput: valAt (gather0 input) (i * hM + k) = valAt input_a (i * hM + k)
        intro k hk
        have := allGatherPrimDimN0_valAt 2 L hM
            [input_a, input_b]
            (by omega) hL hhM hhead_input hshapes_input 0 (by omega) i hi_lt k hk
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl] at this
        exact this
      · -- hw13: gW13 = gW13 (both sides use same gathered w13) — trivially rfl
        intro _ _ _ _; rfl
      · -- hw13': same as hw13 (trivial rfl)
        intro _ _ _ _; rfl
      · -- hw2: same as hw13 (both use gW2)
        intro _ _; rfl
    · -- Case r = 1: RHS = shard 1's moe_gmm on in_b rp_b rm_b with gW13/gW2, sum range [0, numExp)
      rw [hr1]
      simp only [Nat.one_mul]
      rw [show ([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
                 fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit].getD 1 (zeroTensor [L, hM]))
                = fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit from rfl]
      rw [fw_all2all_moe_gmm_valAt input_b rp_b rm_b gW13 gW2
          L hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
          hL hhM hnE (by omega) (by omega) ht_even hinput_b hrp_b hG_w13 i hi_lt col hcol_lt swigluLimit]
      have hsub_zero : E_shard * 2 - 0 = E_shard * 2 := by omega
      rw [hsub_zero]
      apply Finset.sum_congr rfl
      intro x hx
      have hx_lt : x < E_shard * 2 := by simp [Finset.mem_range] at hx; exact hx
      have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
      apply moe_gmm_term_congr
      · -- hmask: valAt (gather0 rm) ((1*L+i) * numExp + (0+x)) = valAt rm_b (i * numExp + (0+x))
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rm_a, rm_b]
            (by omega) hL hnE hhead_rm hshapes_rm 1 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.one_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hprob
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rp_a, rp_b]
            (by omega) hL hnE hhead_rp hshapes_rp 1 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.one_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hinput
        intro k hk
        have := allGatherPrimDimN0_valAt 2 L hM
            [input_a, input_b]
            (by omega) hL hhM hhead_input hshapes_input 1 (by omega) i hi_lt k hk
        simp only [Nat.one_mul,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        exact this
      · intro _ _ _ _; rfl
      · intro _ _ _ _; rfl
      · intro _ _; rfl

/-- fw_all2all_moe_gmm splits expert range across 2 ranks (with sharded w13/w2 weights).
    LEGACY: this theorem's disjointness hypotheses used to be provided by
    `Pattern_1_rma/rmbDisjointAxiom`, but those were vacuous. The theorem is
    kept for backward reference (its proof is real given actual disjoint routing_map),
    but Pattern_1 no longer uses it — see `fw_all2all_moe_gmm_full_split_commute_2`
    above for the upstream-faithful replacement. -/
theorem fw_all2all_moe_gmm_split_commute_2_of
    (input_a input_b routing_probs_a routing_probs_b routing_map_a routing_map_b
     w13_a w13_b w2_a w2_b : Tensor)
    (L hM t_dim d_dim E_shard topK : Nat)
    (hL : 0 < L) (hhM : 0 < hM) (ht : 0 < t_dim) (hd : 0 < d_dim) (hE : 0 < E_shard)
    (ht_even : t_dim = 2 * d_dim)
    (hinput_a : input_a.shape = [L, hM]) (hinput_b : input_b.shape = [L, hM])
    (hrp_a : routing_probs_a.shape = [L, E_shard * 2]) (hrp_b : routing_probs_b.shape = [L, E_shard * 2])
    (hrm_a : routing_map_a.shape = [L, E_shard * 2]) (hrm_b : routing_map_b.shape = [L, E_shard * 2])
    (hw13_a : w13_a.shape = [E_shard, t_dim, hM]) (hw13_b : w13_b.shape = [E_shard, t_dim, hM])
    (hw2_a : w2_a.shape = [E_shard, hM, d_dim]) (hw2_b : w2_b.shape = [E_shard, hM, d_dim])
    (hrm_a_disj : ∀ l < L, ∀ e < E_shard * 2, E_shard ≤ e →
        valAt routing_map_a (l * (E_shard * 2) + e) = 0)
    (hrm_b_disj : ∀ l < L, ∀ e < E_shard * 2, e < E_shard →
        valAt routing_map_b (l * (E_shard * 2) + e) = 0)
    (swigluLimit : Scalar) :
    fw_all2all_moe_gmm (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b])
        (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
        (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
        (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
        (E_shard * 2) 0 (E_shard * 2) topK swigluLimit
      = allGatherPrimDimN 0 2 0
        [fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
          (E_shard * 2) 0 E_shard topK swigluLimit,
         fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
          (E_shard * 2) E_shard (E_shard * 2) topK swigluLimit] := by
  -- Setup
  set numExp := E_shard * 2 with hnumExp_def
  have hnE : 0 < numExp := by rw [hnumExp_def]; positivity
  have hE2_eq : E_shard * 2 = E_shard + E_shard := by ring
  -- Shape witnesses
  have hhead_input : (([input_a, input_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, hM] := by simp [hinput_a]
  have hshapes_input : ∀ r' (_ : r' < 2), (([input_a, input_b].getD r' (zeroTensor [L, hM]))).shape = [L, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hinput_a, hinput_b]
  have hhead_rp : (([routing_probs_a, routing_probs_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, numExp] := by
    simp [hrp_a, hnumExp_def]
  have hshapes_rp : ∀ r' (_ : r' < 2), (([routing_probs_a, routing_probs_b].getD r' (zeroTensor [L, numExp]))).shape = [L, numExp] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hrp_a, hrp_b, hnumExp_def]
  have hhead_rm : (([routing_map_a, routing_map_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, numExp] := by
    simp [hrm_a, hnumExp_def]
  have hshapes_rm : ∀ r' (_ : r' < 2), (([routing_map_a, routing_map_b].getD r' (zeroTensor [L, numExp]))).shape = [L, numExp] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hrm_a, hrm_b, hnumExp_def]
  have hhead_w13 : (([w13_a, w13_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [E_shard, t_dim, hM] := by simp [hw13_a]
  have hshapes_w13 : ∀ r' (_ : r' < 2), (([w13_a, w13_b].getD r' (zeroTensor [E_shard, t_dim, hM]))).shape = [E_shard, t_dim, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hw13_a, hw13_b]
  have hhead_w2 : (([w2_a, w2_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [E_shard, hM, d_dim] := by simp [hw2_a]
  have hshapes_w2 : ∀ r' (_ : r' < 2), (([w2_a, w2_b].getD r' (zeroTensor [E_shard, hM, d_dim]))).shape = [E_shard, hM, d_dim] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hw2_a, hw2_b]
  -- Gathered shapes
  have hG_input : (allGatherPrimDimN 0 2 0 [input_a, input_b]).shape = [L * 2, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, hM] hhead_input]; simp [List.set, List.getD]
  have hG_rp : (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b]).shape = [L * 2, numExp] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, numExp] hhead_rp]; simp [List.set, List.getD]
  have hG_rm : (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b]).shape = [L * 2, numExp] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, numExp] hhead_rm]; simp [List.set, List.getD]
  have hG_w13 : (allGatherPrimDimN 0 2 0 [w13_a, w13_b]).shape = [E_shard * 2, t_dim, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [E_shard, t_dim, hM] hhead_w13]; simp [List.set, List.getD]
  have hG_w2 : (allGatherPrimDimN 0 2 0 [w2_a, w2_b]).shape = [E_shard * 2, hM, d_dim] := by
    rw [allGatherPrimDimN_shape 0 2 _ [E_shard, hM, d_dim] hhead_w2]; simp [List.set, List.getD]
  -- Local moe_gmm output shapes
  have hloc_a_shape : (fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
                        numExp 0 E_shard topK swigluLimit).shape = [L, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hinput_a]; rfl
  have hloc_b_shape : (fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
                        numExp E_shard numExp topK swigluLimit).shape = [L, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hinput_b]; rfl
  have hhead_loc : (([fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
                        numExp 0 E_shard topK swigluLimit,
                      fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
                        numExp E_shard numExp topK swigluLimit] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, hM] := by
    simp [hloc_a_shape]
  have hshapes_loc : ∀ r' (_ : r' < 2),
      (([fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
                        numExp 0 E_shard topK swigluLimit,
         fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
                        numExp E_shard numExp topK swigluLimit].getD r' (zeroTensor [L, hM]))).shape = [L, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hloc_a_shape, hloc_b_shape]
  -- LHS/RHS shape
  have hLHS_shape : (fw_all2all_moe_gmm (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b])
        (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
        (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
        (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
        numExp 0 numExp topK swigluLimit).shape = [L * 2, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hG_input]; rfl
  have hRHS_shape : (allGatherPrimDimN 0 2 0
        [fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
          numExp 0 E_shard topK swigluLimit,
         fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
          numExp E_shard numExp topK swigluLimit]).shape = [L * 2, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, hM] hhead_loc]; simp [List.set, List.getD]
  -- Tensor.ext
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < L * 2 * hM := by simpa [prodShape] using houtIdx
    -- Decompose outIdx
    set row := outIdx / hM with hrow_def
    set col := outIdx % hM with hcol_def
    have hcol_lt : col < hM := by rw [hcol_def]; exact Nat.mod_lt _ hhM
    have hrow_lt : row < L * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul hhM]; linarith
    have houtIdx_eq : outIdx = row * hM + col := by
      have h1 : hM * (outIdx / hM) + outIdx % hM = outIdx := Nat.div_add_mod outIdx hM
      rw [hrow_def, hcol_def]
      linarith [Nat.mul_comm hM (outIdx / hM)]
    set r := row / L with hr_def
    set i := row % L with hi_def
    have hi_lt : i < L := by rw [hi_def]; exact Nat.mod_lt _ hL
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hL]; linarith
    have hrow_eq : row = r * L + i := by
      have h1 : L * (row / L) + row % L = row := Nat.div_add_mod row L
      rw [hr_def, hi_def]
      linarith [Nat.mul_comm L (row / L)]
    -- === LHS reduction ===
    -- LHS at outIdx = valAt fw_all2all_moe_gmm(gathered) at (row*hM + col)
    -- Apply fw_all2all_moe_gmm_valAt with L*2 (gathered L)
    rw [houtIdx_eq, hrow_eq]
    -- Now outIdx = (r*L+i)*hM + col
    have hrow_lt' : r * L + i < L * 2 := by
      calc r * L + i < r * L + L := by omega
        _ = (r + 1) * L := by ring
        _ ≤ 2 * L := Nat.mul_le_mul_right _ (by omega)
        _ = L * 2 := by ring
    rw [fw_all2all_moe_gmm_valAt _ _ _ _ _ (L * 2) hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
        (by omega) hhM hnE (by omega) (by omega) ht_even hG_input hG_rp hG_w13 (r * L + i) hrow_lt' col hcol_lt swigluLimit]
    -- Also apply to RHS's gather0'd shard output
    rw [allGatherPrimDimN0_valAt 2 L hM
        [fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
          numExp 0 E_shard topK swigluLimit,
         fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
          numExp E_shard numExp topK swigluLimit]
        (by omega) hL hhM hhead_loc hshapes_loc r hr_lt i hi_lt col hcol_lt]
    -- Case on r=0 vs r=1
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    rcases hr_cases with hr0 | hr1
    · -- Case r = 0: RHS = shard 0's moe_gmm
      rw [hr0]
      -- Reduce arithmetic and evaluate the List.getD to shard 0's tensor
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show ([fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
                   numExp 0 E_shard topK swigluLimit,
                 fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
                   numExp E_shard numExp topK swigluLimit].getD 0 (zeroTensor [L, hM]))
                = fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
                   numExp 0 E_shard topK swigluLimit from rfl]
      rw [fw_all2all_moe_gmm_valAt input_a routing_probs_a routing_map_a w13_a w2_a
          L hM numExp E_shard 0 E_shard topK t_dim d_dim
          hL hhM hnE hE (by omega) ht_even hinput_a hrp_a hw13_a i hi_lt col hcol_lt swigluLimit]
      -- LHS: ∑ eLocal ∈ range numExp, moe_gmm_term (gather0 stuff)
      -- RHS: ∑ eLocal ∈ range E_shard, moe_gmm_term (a stuff)
      -- Split LHS sum at E_shard: range numExp = range E_shard + shifted range E_shard
      have hnumExp_split : numExp = E_shard + E_shard := by rw [hnumExp_def]; ring
      have hsub_zero : E_shard * 2 - 0 = E_shard * 2 := by omega
      have hsub_E : E_shard - 0 = E_shard := by omega
      rw [hsub_zero, hsub_E]
      rw [show E_shard * 2 = E_shard + E_shard from by ring]
      rw [Finset.sum_range_add]
      -- LHS is now ∑ x ∈ range E_shard, (low) + ∑ x ∈ range E_shard, (high with x → E_shard + x)
      -- RHS is ∑ x ∈ range E_shard, moe_gmm_term (a stuff)
      -- Second sum (high) should be 0 via disjointness (rm_a mask is 0 for e ≥ E_shard)
      have hhigh_zero : (∑ x ∈ Finset.range E_shard, moe_gmm_term
              (allGatherPrimDimN 0 2 0 [input_a, input_b])
              (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b])
              (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
              (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
              (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
              numExp 0 (E_shard + x) i col hM d_dim t_dim swigluLimit) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hx_lt : x < E_shard := by simp [Finset.mem_range] at hx; exact hx
        -- The mask valAt (gather0 rm) at (i * numExp + (0 + (E_shard + x)))
        -- = valAt rm_a (i * numExp + (E_shard + x)) (via gather0, row i < L)
        -- = 0 (via hrm_a_disj)
        unfold moe_gmm_term
        simp only
        have hmask_eq : valAt (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
              (i * numExp + (0 + (E_shard + x)))
            = valAt routing_map_a (i * numExp + (E_shard + x)) := by
          have h_bound_e : E_shard + x < numExp := by rw [hnumExp_def]; omega
          have := allGatherPrimDimN0_valAt 2 L numExp
              [routing_map_a, routing_map_b]
              (by omega) hL hnE hhead_rm hshapes_rm 0 (by omega) i hi_lt (E_shard + x) h_bound_e
          simp only [Nat.zero_mul, Nat.zero_add] at this
          -- this : valAt (gather0) (i*numExp + (E_shard+x)) = valAt ([...][0]?.getD _) (i*numExp+(E_shard+x))
          -- Convert [...][0]?.getD to routing_map_a and add the `0 +` on the LHS index
          have hgetD0 : [routing_map_a, routing_map_b].getD 0 (zeroTensor [L, numExp])
                        = routing_map_a := rfl
          rw [hgetD0] at this
          -- Now this : valAt (gather0) (i*numExp+(E_shard+x)) = valAt routing_map_a (i*numExp+(E_shard+x))
          rw [show (0 + (E_shard + x)) = (E_shard + x) from by omega]
          exact this
        rw [hmask_eq]
        have hmask_zero : valAt routing_map_a (i * numExp + (E_shard + x)) = 0 := by
          rw [hnumExp_def]
          apply hrm_a_disj i hi_lt (E_shard + x) (by omega) (by omega)
        rw [hmask_zero]
        simp
      -- Now LHS = ∑ x ∈ range E_shard, moe_gmm_term (LHS gather stuff) + 0
      rw [hhigh_zero, add_zero]
      -- Match low-half: use moe_gmm_term_congr for each x < E_shard
      apply Finset.sum_congr rfl
      intro x hx
      have hx_lt : x < E_shard := by simp [Finset.mem_range] at hx; exact hx
      -- Apply moe_gmm_term_congr: LHS (gather0 tensors, l=i, eLocal=x) = RHS (a tensors, l=i, eLocal=x)
      apply moe_gmm_term_congr
      · -- hmask: valAt (gather0 rm) (i*numExp + (0+x)) = valAt rm_a (i*numExp + (0+x))
        have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
        have := allGatherPrimDimN0_valAt 2 L numExp
            [routing_map_a, routing_map_b]
            (by omega) hL hnE hhead_rm hshapes_rm 0 (by omega) i hi_lt (0 + x) h_bound_e
        -- this : valAt (gather0) ((0 * L + i) * numExp + (0 + x)) = valAt ([...][0]?.getD _) (i * numExp + (0 + x))
        -- Reduce `0 * L → 0` and List.getD via rfl, keep `0 + x`
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        -- After simp: this : valAt (gather0) (i * numExp + x) = valAt routing_map_a (i * numExp + x)
        -- Add back the (0 + x) form via rw:
        try rw [show (0 + x) = x from Nat.zero_add x]
        exact this
      · -- hprob: same structure for rp
        have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
        have := allGatherPrimDimN0_valAt 2 L numExp
            [routing_probs_a, routing_probs_b]
            (by omega) hL hnE hhead_rp hshapes_rp 0 (by omega) i hi_lt (0 + x) h_bound_e
        -- this : valAt (gather0) ((0 * L + i) * numExp + (0 + x)) = valAt ([...][0]?.getD _) (i * numExp + (0 + x))
        -- Reduce `0 * L → 0` and List.getD via rfl, keep `0 + x`
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        -- After simp: this : valAt (gather0) (i * numExp + x) = valAt routing_map_a (i * numExp + x)
        -- Add back the (0 + x) form via rw:
        try rw [show (0 + x) = x from Nat.zero_add x]
        exact this
      · -- hinput: valAt (gather0 input) (i*hM + k) = valAt input_a (i*hM + k)
        intro k hk
        have := allGatherPrimDimN0_valAt 2 L hM
            [input_a, input_b]
            (by omega) hL hhM hhead_input hshapes_input 0 (by omega) i hi_lt k hk
        -- this : valAt (gather0) ((0 * L + i) * numExp + (0 + x)) = valAt ([...][0]?.getD _) (i * numExp + (0 + x))
        -- Reduce `0 * L → 0` and List.getD via rfl, keep `0 + x`
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        -- After simp: this : valAt (gather0) (i * numExp + x) = valAt routing_map_a (i * numExp + x)
        -- Add back the (0 + x) form via rw:
        try rw [show (0 + x) = x from Nat.zero_add x]
        exact this
      · -- hw13: valAt (gather0 w13) at ((x*t_dim+d)*hM+k) = valAt w13_a at ((x*t_dim+d)*hM+k)
        intro d k hd hk
        -- Use allGatherPrimDimN0_valAt_3d with r=0, eLocal=x (< E_shard), hi=d (< t_dim), di=k (< hM)
        have hd_lt_t : d < t_dim := by rw [ht_even]; omega
        have := allGatherPrimDimN0_valAt_3d E_shard t_dim hM hE ht hhM
            [w13_a, w13_b] hhead_w13 0 (by omega) x hx_lt d hd_lt_t k hk
        -- this : valAt (gather0) ((0 * L + i) * numExp + (0 + x)) = valAt ([...][0]?.getD _) (i * numExp + (0 + x))
        -- Reduce `0 * L → 0` and List.getD via rfl, keep `0 + x`
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        -- After simp: this : valAt (gather0) (i * numExp + x) = valAt routing_map_a (i * numExp + x)
        -- Add back the (0 + x) form via rw:
        try rw [show (0 + x) = x from Nat.zero_add x]
        exact this
      · -- hw13' (up half): d shifted to h_inner + d = d_dim + d, but d < d_dim so d_dim+d < t_dim
        intro d k hd hk
        have hd_lt_dd : d < d_dim := hd  -- h_inner = d_dim
        have hdd_lt_t : d_dim + d < t_dim := by rw [ht_even]; omega
        have := allGatherPrimDimN0_valAt_3d E_shard t_dim hM hE ht hhM
            [w13_a, w13_b] hhead_w13 0 (by omega) x hx_lt (d_dim + d) hdd_lt_t k hk
        -- this : valAt (gather0) ((0 * L + i) * numExp + (0 + x)) = valAt ([...][0]?.getD _) (i * numExp + (0 + x))
        -- Reduce `0 * L → 0` and List.getD via rfl, keep `0 + x`
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        -- After simp: this : valAt (gather0) (i * numExp + x) = valAt routing_map_a (i * numExp + x)
        -- Add back the (0 + x) form via rw:
        try rw [show (0 + x) = x from Nat.zero_add x]
        exact this
      · -- hw2: valAt (gather0 w2) at ((x*hM+col)*d_dim+d) = valAt w2_a at (same)
        intro d hd
        have hd_lt_dd : d < d_dim := hd
        have := allGatherPrimDimN0_valAt_3d E_shard hM d_dim hE hhM (by assumption : 0 < d_dim)
            [w2_a, w2_b] hhead_w2 0 (by omega) x hx_lt col hcol_lt d hd_lt_dd
        -- this : valAt (gather0) ((0 * L + i) * numExp + (0 + x)) = valAt ([...][0]?.getD _) (i * numExp + (0 + x))
        -- Reduce `0 * L → 0` and List.getD via rfl, keep `0 + x`
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        -- After simp: this : valAt (gather0) (i * numExp + x) = valAt routing_map_a (i * numExp + x)
        -- Add back the (0 + x) form via rw:
        try rw [show (0 + x) = x from Nat.zero_add x]
        exact this
    · -- Case r = 1: RHS = shard 1's moe_gmm
      rw [hr1]
      simp only [Nat.one_mul]
      rw [show ([fw_all2all_moe_gmm input_a routing_probs_a routing_map_a w13_a w2_a
                   numExp 0 E_shard topK swigluLimit,
                 fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
                   numExp E_shard numExp topK swigluLimit].getD 1 (zeroTensor [L, hM]))
                = fw_all2all_moe_gmm input_b routing_probs_b routing_map_b w13_b w2_b
                   numExp E_shard numExp topK swigluLimit from rfl]
      rw [fw_all2all_moe_gmm_valAt input_b routing_probs_b routing_map_b w13_b w2_b
          L hM numExp E_shard E_shard numExp topK t_dim d_dim
          hL hhM hnE hE (by omega) ht_even hinput_b hrp_b hw13_b i hi_lt col hcol_lt swigluLimit]
      have hnumExp_split : numExp = E_shard + E_shard := by rw [hnumExp_def]; ring
      have hsub_zero : E_shard * 2 - 0 = E_shard * 2 := by omega
      have hsub_E : E_shard * 2 - E_shard = E_shard := by omega
      rw [hsub_zero, hsub_E]
      rw [show E_shard * 2 = E_shard + E_shard from by ring]
      rw [Finset.sum_range_add]
      -- LHS is: ∑ x ∈ range E_shard, (low with rm_a=0 → 0) + ∑ x ∈ range E_shard, (high matches shard 1)
      have hlow_zero : (∑ x ∈ Finset.range E_shard, moe_gmm_term
              (allGatherPrimDimN 0 2 0 [input_a, input_b])
              (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b])
              (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
              (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
              (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
              numExp 0 x (L + i) col hM d_dim t_dim swigluLimit) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hx_lt : x < E_shard := by simp [Finset.mem_range] at hx; exact hx
        unfold moe_gmm_term
        simp only
        have hmask_eq : valAt (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
              ((L + i) * numExp + (0 + x))
            = valAt routing_map_b (i * numExp + x) := by
          have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
          have := allGatherPrimDimN0_valAt 2 L numExp
              [routing_map_a, routing_map_b]
              (by omega) hL hnE hhead_rm hshapes_rm 1 (by omega) i hi_lt (0 + x) h_bound_e
          simp only [Nat.one_mul, Nat.zero_add,
                     show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
          rw [show (0 + x) = x from Nat.zero_add x]
          exact this
        rw [hmask_eq]
        have hmask_zero : valAt routing_map_b (i * numExp + x) = 0 := by
          rw [hnumExp_def]
          apply hrm_b_disj i hi_lt x (by omega) hx_lt
        rw [hmask_zero]
        simp
      rw [hlow_zero, zero_add]
      -- Match high-half: LHS at eLocal = E_shard + x (LHS param), RHS at eLocal = x (shard 1 param)
      apply Finset.sum_congr rfl
      intro x hx
      have hx_lt : x < E_shard := by simp [Finset.mem_range] at hx; exact hx
      -- Apply moe_gmm_term_congr: LHS (gather0 tensors, l=L+i, eLocal=E_shard+x)
      --                         = RHS (b tensors, l=i, eLocal=x with start=E_shard)
      -- Note: LHS uses `start=0, eLocal=E_shard+x` while RHS uses `start=E_shard, eLocal=x`.
      -- The masks and probs read `l*numExp + (start+eLocal)` — both give `l*numExp + (E_shard+x)`.
      -- But the WEIGHTS read `eLocal * ...` which differs: LHS uses E_shard+x, RHS uses x.
      -- So we can't use `moe_gmm_term_congr` directly (it needs same eLocal on both sides).
      -- Instead, unfold both moe_gmm_term and match component-by-component.
      unfold moe_gmm_term
      simp only
      -- mask
      have hmask_eq : valAt (allGatherPrimDimN 0 2 0 [routing_map_a, routing_map_b])
            ((L + i) * numExp + (0 + (E_shard + x)))
          = valAt routing_map_b (i * numExp + (E_shard + x)) := by
        have h_bound_e : 0 + (E_shard + x) < numExp := by rw [hnumExp_def]; omega
        have := allGatherPrimDimN0_valAt 2 L numExp
            [routing_map_a, routing_map_b]
            (by omega) hL hnE hhead_rm hshapes_rm 1 (by omega) i hi_lt (0 + (E_shard + x)) h_bound_e
        simp only [Nat.one_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        rw [show (0 + (E_shard + x)) = (E_shard + x) from Nat.zero_add _]
        exact this
      rw [hmask_eq]
      by_cases hmz : valAt routing_map_b (i * numExp + (E_shard + x)) = 0
      · simp [hmz]
      · simp only [hmz, if_false]
        -- prob
        have hprob_eq : valAt (allGatherPrimDimN 0 2 0 [routing_probs_a, routing_probs_b])
              ((L + i) * numExp + (0 + (E_shard + x)))
            = valAt routing_probs_b (i * numExp + (E_shard + x)) := by
          have h_bound_e : 0 + (E_shard + x) < numExp := by rw [hnumExp_def]; omega
          have := allGatherPrimDimN0_valAt 2 L numExp
              [routing_probs_a, routing_probs_b]
              (by omega) hL hnE hhead_rp hshapes_rp 1 (by omega) i hi_lt (0 + (E_shard + x)) h_bound_e
          simp only [Nat.one_mul, Nat.zero_add,
                     show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
          rw [show (0 + (E_shard + x)) = (E_shard + x) from Nat.zero_add _]
          exact this
        rw [hprob_eq]
        congr 1
        apply Finset.sum_congr rfl
        intro d hd
        have hd_lt : d < d_dim := by simp [Finset.mem_range] at hd; exact hd
        -- input: valAt (gather0 input) ((L+i)*hM+k) = valAt input_b (i*hM+k)
        have hinput_eq : ∀ k, k < hM →
            valAt (allGatherPrimDimN 0 2 0 [input_a, input_b]) ((L + i) * hM + k)
              = valAt input_b (i * hM + k) := by
          intro k hk
          have := allGatherPrimDimN0_valAt 2 L hM
              [input_a, input_b]
              (by omega) hL hhM hhead_input hshapes_input 1 (by omega) i hi_lt k hk
          simp only [Nat.one_mul,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
          exact this
        -- w13: valAt (gather0 w13) at ((E_shard+x)*t_dim + d)*hM + k) = valAt w13_b at ((x*t_dim + d)*hM + k)
        have hw13_eq : ∀ k, k < hM →
            valAt (allGatherPrimDimN 0 2 0 [w13_a, w13_b]) (((E_shard + x) * t_dim + d) * hM + k)
              = valAt w13_b ((x * t_dim + d) * hM + k) := by
          intro k hk
          have hd_lt_t : d < t_dim := by rw [ht_even]; omega
          have := allGatherPrimDimN0_valAt_3d E_shard t_dim hM hE ht hhM
              [w13_a, w13_b] hhead_w13 1 (by omega) x hx_lt d hd_lt_t k hk
          simp only [show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
          -- this : valAt (gather0) (((1*E_shard+x)*t_dim+d)*hM+k) = valAt w13_b ((x*t_dim+d)*hM+k)
          -- 1*E_shard = E_shard so LHS matches
          simp only [Nat.one_mul] at this
          exact this
        have hw13_up_eq : ∀ k, k < hM →
            valAt (allGatherPrimDimN 0 2 0 [w13_a, w13_b]) (((E_shard + x) * t_dim + (d_dim + d)) * hM + k)
              = valAt w13_b ((x * t_dim + (d_dim + d)) * hM + k) := by
          intro k hk
          have hdd_lt_t : d_dim + d < t_dim := by rw [ht_even]; omega
          have := allGatherPrimDimN0_valAt_3d E_shard t_dim hM hE ht hhM
              [w13_a, w13_b] hhead_w13 1 (by omega) x hx_lt (d_dim + d) hdd_lt_t k hk
          simp only [List.getD, Nat.one_mul] at this
          exact this
        -- w2: valAt (gather0 w2) at ((E_shard+x)*hM+col)*d_dim + d) = valAt w2_b at ((x*hM+col)*d_dim+d)
        have hw2_eq : valAt (allGatherPrimDimN 0 2 0 [w2_a, w2_b]) (((E_shard + x) * hM + col) * d_dim + d)
            = valAt w2_b ((x * hM + col) * d_dim + d) := by
          have := allGatherPrimDimN0_valAt_3d E_shard hM d_dim hE hhM (by assumption : 0 < d_dim)
              [w2_a, w2_b] hhead_w2 1 (by omega) x hx_lt col hcol_lt d hd_lt
          simp only [List.getD, Nat.one_mul] at this
          exact this
        -- Match gate/up sums via hinput_eq and hw13_eq / hw13_up_eq
        have hgate_eq : (∑ k ∈ Finset.range hM,
              valAt (allGatherPrimDimN 0 2 0 [input_a, input_b]) ((L + i) * hM + k) *
              valAt (allGatherPrimDimN 0 2 0 [w13_a, w13_b]) (((E_shard + x) * t_dim + d) * hM + k))
            = ∑ k ∈ Finset.range hM,
                valAt input_b (i * hM + k) *
                valAt w13_b ((x * t_dim + d) * hM + k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk_lt : k < hM := by simp [Finset.mem_range] at hk; exact hk
          rw [hinput_eq k hk_lt, hw13_eq k hk_lt]
        have hup_eq : (∑ k ∈ Finset.range hM,
              valAt (allGatherPrimDimN 0 2 0 [input_a, input_b]) ((L + i) * hM + k) *
              valAt (allGatherPrimDimN 0 2 0 [w13_a, w13_b]) (((E_shard + x) * t_dim + (d_dim + d)) * hM + k))
            = ∑ k ∈ Finset.range hM,
                valAt input_b (i * hM + k) *
                valAt w13_b ((x * t_dim + (d_dim + d)) * hM + k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk_lt : k < hM := by simp [Finset.mem_range] at hk; exact hk
          rw [hinput_eq k hk_lt, hw13_up_eq k hk_lt]
        rw [hgate_eq, hup_eq, hw2_eq]


/-- `fw_maybe_unshuffle` at `cpSize=1` distributes over `allGather` of `cpSize=2` shards.

    ⚠️ HISTORICAL NOTE (2026-07-03): this was previously an inconsistent axiom
    (`UnshuffleInconsistent.lean` proved `False` from it) because the old
    `fw_maybe_unshuffle` used `xs.head?.shape` — a metadata shape — as the output
    shape. The 2026-07-03 audit fixed `Denote.fw_maybe_unshuffle` to be an
    identity on the data tensor (matching Python's `wrap_maybe_shuffle` early-return
    and preserving the correct shape at all `cpSize`), which makes this
    distributive identity TRUE by direct computation. The `sorry` placeholder
    below can be discharged with `by decide` or `rfl` on the concrete-shape
    instances Pattern_1 uses; a fully general proof requires
    `allGather-of-identity = identity-of-allGather`, which follows from the
    identity model. -/
theorem fw_maybe_unshuffle_cp2_commute
    (a b cu : Tensor) :
    fw_maybe_unshuffle (allGatherPrimDimN 0 2 0 [a, b]) cu 1 0
      = allGatherPrimDimN 0 2 0
        [fw_maybe_unshuffle a cu 2 0, fw_maybe_unshuffle b cu 2 1] := by
  -- All three unshuffle applications are identities on their data argument.
  unfold fw_maybe_unshuffle
  -- Both sides reduce to `allGatherPrimDimN 0 2 0 [a, b]`.
  rfl

/-- 1-D variant of `allGatherPrimDimN0_valAt` for shape `[Lshard]`:
    at flat idx `r * Lshard + i` in output `[Lshard * 2]`, reads shard r at local idx i. -/
private theorem allGatherPrimDimN0_valAt_1d (Lshard : Nat) (hLshard : 0 < Lshard)
    (Ws : List Tensor)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard])
    (hshapes : ∀ r' (_ : r' < 2), (Ws.getD r' (zeroTensor [Lshard])).shape = [Lshard])
    (r : Nat) (hr : r < 2) (i : Nat) (hi : i < Lshard) :
    valAt (allGatherPrimDimN 0 2 0 Ws) (r * Lshard + i)
      = valAt (Ws.getD r (zeroTensor [Lshard])) i := by
  unfold allGatherPrimDimN
  rw [hhead]
  simp only [List.getD, List.drop, List.foldl]
  -- Now: valAt (mkShape [Lshard * 2] fn) (r * Lshard + i) = valAt (Ws.getD r _) i
  -- where fn outIdx computes the gathered-value via preIdx/remainder/jFull/etc.
  have hbound : r * Lshard + i < Lshard * 2 := by
    calc r * Lshard + i < r * Lshard + Lshard := by omega
      _ = (r + 1) * Lshard := by ring
      _ ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
      _ = Lshard * 2 := by ring
  rw [valAt_of_lt _ _ (by
    show r * Lshard + i < prodShape ([Lshard].set 0 (([Lshard].getD 0 0) * 2))
    simp [prodShape, List.set, List.getD]
    exact hbound)]
  simp [Tensor.mkShape, List.set, List.getD]
  -- The mkShape function computes valAt (Ws.getD r' _) (preIdx * dimStride + jLocal * postStride + k)
  -- After all simplifications with dimSize=Lshard, postStride=1, dimStride=Lshard, fullDimStride=Lshard*2:
  -- preIdx = idx / (Lshard*2) = 0 (since idx < Lshard*2)
  -- remainder = idx % (Lshard*2) = idx
  -- jFull = remainder / 1 = idx
  -- k = remainder % 1 = 0
  -- r' = jFull / Lshard = r (given hi)
  -- jLocal = jFull % Lshard = i (given hi)
  -- Reads Ws[r] at (0 * Lshard + i * 1 + 0) = i.
  have hLshard_ne : Lshard ≠ 0 := Nat.pos_iff_ne_zero.mp hLshard
  have hLshard2_ne : Lshard * 2 ≠ 0 := Nat.mul_ne_zero hLshard_ne (by omega)
  have hidx_div_full : (r * Lshard + i) / (Lshard * 2) = 0 := by
    apply Nat.div_eq_of_lt; exact hbound
  have hidx_mod_full : (r * Lshard + i) % (Lshard * 2) = r * Lshard + i := by
    apply Nat.mod_eq_of_lt; exact hbound
  have hjFull_div : (r * Lshard + i) / Lshard = r := by
    have h1 : (r * Lshard + i) / Lshard = i / Lshard + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right i r hLshard]
    rw [h1, Nat.div_eq_of_lt hi]; ring
  have hjFull_mod : (r * Lshard + i) % Lshard = i := by
    have h1 : (r * Lshard + i) % Lshard = i % Lshard := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h1, Nat.mod_eq_of_lt hi]
  have hmod1 : (r * Lshard + i) % 1 = 0 := Nat.mod_one _
  simp [hLshard_ne, hLshard2_ne, hidx_div_full, hidx_mod_full, hjFull_div, hjFull_mod, hmod1]

/-- chunkPrimDimN 1-D helper: for a `[Lfull]` tensor, `chunkPrimDimN 0 2 r y` has shape
    `[Lfull/2]` and at flat idx i reads valAt y (r * Lshard + i) where Lshard = Lfull/2. -/
private theorem chunkPrimDimN_1d_valAt (Lshard : Nat) (hLshard : 0 < Lshard)
    (y : Tensor) (hy : y.shape = [Lshard * 2])
    (r : Nat) (hr : r < 2) (i : Nat) (hi : i < Lshard) :
    valAt (chunkPrimDimN 0 2 r y) i = valAt y (r * Lshard + i) := by
  unfold chunkPrimDimN
  rw [hy]
  simp only [List.set, List.drop, List.foldl, List.getD]
  -- outShape = [Lshard*2].set 0 (Lshard*2 / 2) = [Lshard]
  have hlt : i < Lshard := hi
  have hLshard2_div : (Lshard * 2) / 2 = Lshard := by omega
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  rw [valAt_of_lt _ _ (by
    show i < prodShape ([Lshard * 2].set 0 ((Lshard * 2) / 2))
    simp [prodShape, List.set, hLshard2_div]
    exact hi)]
  simp [Tensor.mkShape, List.set, hLshard2_div, hrmod]
  -- After simp: goal becomes valAt y (r * Lshard + i)
  -- The chunkPrimDimN computes preIdx * dimStride + jFull * postStride + k
  -- For 1-D: preIdx=0, postStride=1, dimStride=Lshard*2, jFull = r*Lshard+jLocal
  -- jLocal = i % Lshard, remainder = i % Lshard, k = 0
  have hi_mod : i % Lshard = i := Nat.mod_eq_of_lt hi
  have hi_div : i / Lshard = 0 := Nat.div_eq_of_lt hi
  have hLshard_ne : Lshard ≠ 0 := Nat.pos_iff_ne_zero.mp hLshard
  have hi_mod1 : i % 1 = 0 := Nat.mod_one _
  simp [hi_mod, hi_div, hLshard_ne, hi_mod1]

/-- fw_inner_chunk_ce fst commutes with dim-0 sharding — proven for 2D input, 1D labels.
    Requires labels < vocab (well-formed training data).
    Pattern_1 usage: x_a, x_b : [Lshard=2048, h_model=1024], w : [vocab, h_model], y : [L=4096]. -/
theorem fw_inner_chunk_ce_fst_allGather0_commute_2_of (x_a x_b w y : Tensor)
    (Lshard h_model vocab : Nat)
    (hLshard : 0 < Lshard) (hh : 0 < h_model) (hvocab : 0 < vocab)
    (hxa : x_a.shape = [Lshard, h_model]) (hxb : x_b.shape = [Lshard, h_model])
    (hw : w.shape = [vocab, h_model]) (hy : y.shape = [Lshard * 2])
    (hlabels_bound : ∀ l < Lshard * 2, scalarToNat (valAt y l) < vocab)
    (zLossScale : Scalar) :
    (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst
      = allGatherPrimDimN 0 2 0
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst] := by
  -- KEY reduction: use fw_linear commute to make logits into gather0 [logits_a, logits_b] first.
  have hlin_commute : fw_linear (allGatherPrimDimN 0 2 0 [x_a, x_b]) w
      = allGatherPrimDimN 0 2 0 [fw_linear x_a w, fw_linear x_b w] :=
    fw_linear_allGather0_commute_2_of x_a x_b w Lshard h_model vocab
      hLshard hh hvocab hxa hxb hw
  -- Shape witnesses for downstream reasoning.
  have hhead_x : (([x_a, x_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [Lshard, h_model] := by
    simp [hxa]
  have hG_x : (allGatherPrimDimN 0 2 0 [x_a, x_b]).shape = [Lshard * 2, h_model] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, h_model] hhead_x]; simp [List.set, List.getD]
  have hloss_a_shape : (fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst.shape = [Lshard] := by
    unfold fw_inner_chunk_ce
    simp [Tensor.mkShape]
    rw [hxa]; rfl
  have hloss_b_shape : (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst.shape = [Lshard] := by
    unfold fw_inner_chunk_ce
    simp [Tensor.mkShape]
    rw [hxb]; rfl
  have hhead_loss : (([(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
                    (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst] : List Tensor).head?.map (fun t => t.shape)).getD [] = [Lshard] := by
    simp [hloss_a_shape]
  have hshapes_loss : ∀ r' (_ : r' < 2),
      (([(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst].getD r' (zeroTensor [Lshard]))).shape = [Lshard] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hloss_a_shape, hloss_b_shape]
  -- Fw_linear output shapes
  have hlin_a_shape : (fw_linear x_a w).shape = [Lshard, vocab] :=
    fw_linear_2d_shape Lshard h_model vocab x_a w hxa hw
  have hlin_b_shape : (fw_linear x_b w).shape = [Lshard, vocab] :=
    fw_linear_2d_shape Lshard h_model vocab x_b w hxb hw
  have hlin_G_shape : (fw_linear (allGatherPrimDimN 0 2 0 [x_a, x_b]) w).shape = [Lshard * 2, vocab] :=
    fw_linear_2d_shape (Lshard * 2) h_model vocab _ w hG_x hw
  have hhead_lin : (([fw_linear x_a w, fw_linear x_b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [Lshard, vocab] := by
    simp [hlin_a_shape]
  have hshapes_lin : ∀ r' (_ : r' < 2),
      (([fw_linear x_a w, fw_linear x_b w].getD r' (zeroTensor [Lshard, vocab]))).shape = [Lshard, vocab] := by
    intro r' hr'
    have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hlin_a_shape, hlin_b_shape]
  -- Now prove tensor equality via extensionality
  have hLHS_loss_shape : (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst.shape = [Lshard * 2] := by
    unfold fw_inner_chunk_ce
    simp [Tensor.mkShape]
    rw [hG_x]; rfl
  have hRHS_shape : (allGatherPrimDimN 0 2 0
      [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
       (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst]).shape = [Lshard * 2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard] hhead_loss]; simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hLHS_loss_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_loss_shape] at houtIdx
    have houtIdx_bound : outIdx < Lshard * 2 := by simpa [prodShape] using houtIdx
    -- Decompose outIdx = r * Lshard + i
    set r := outIdx / Lshard with hr_def
    set i := outIdx % Lshard with hi_def
    have hi_lt : i < Lshard := by rw [hi_def]; exact Nat.mod_lt _ hLshard
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hLshard]; linarith
    have houtIdx_eq : outIdx = r * Lshard + i := by
      have h1 : Lshard * (outIdx / Lshard) + outIdx % Lshard = outIdx := Nat.div_add_mod outIdx Lshard
      rw [hr_def, hi_def]
      calc outIdx = Lshard * (outIdx / Lshard) + outIdx % Lshard := h1.symm
        _ = outIdx / Lshard * Lshard + outIdx % Lshard := by ring
    -- LHS unfold
    have hLHS_val : valAt (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x_a, x_b]) w y vocab zLossScale).fst outIdx
        = (let logits := fw_linear (allGatherPrimDimN 0 2 0 [x_a, x_b]) w
           let l := outIdx
           let labelIdx := scalarToNat (valAt y l)
           xentLogSumExp logits l vocab - valAt logits (l * vocab + labelIdx)) := by
      unfold fw_inner_chunk_ce
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show outIdx < prodShape [(allGatherPrimDimN 0 2 0 [x_a, x_b]).shape.head?.getD 0]
        rw [hG_x]; simp [prodShape]; linarith)]
    rw [hLHS_val]
    -- Rewrite logits via linear commute
    rw [hlin_commute]
    -- RHS gather at r
    rw [houtIdx_eq]
    rw [allGatherPrimDimN0_valAt_1d Lshard hLshard
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst]
        hhead_loss hshapes_loss r hr_lt i hi_lt]
    -- Get local piece
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    have hgetD_loss : ∀ r0, r0 = 0 ∨ r0 = 1 →
        [(fw_inner_chunk_ce x_a w (chunkPrimDimN 0 2 0 y) vocab zLossScale).fst,
         (fw_inner_chunk_ce x_b w (chunkPrimDimN 0 2 1 y) vocab zLossScale).fst].getD r0 (zeroTensor [Lshard]) =
        (fw_inner_chunk_ce ([x_a, x_b].getD r0 (zeroTensor [Lshard, h_model])) w
             (chunkPrimDimN 0 2 r0 y) vocab zLossScale).fst := by
      intro r0 hcases
      rcases hcases with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_loss r hr_cases]
    -- Unfold local fw_inner_chunk_ce
    set ea := [x_a, x_b].getD r (zeroTensor [Lshard, h_model]) with hea_def
    have hea_shape : ea.shape = [Lshard, h_model] := by
      rcases hr_cases with h | h <;> rw [hea_def] <;> rw [h] <;> simp [List.getD, hxa, hxb]
    have hlin_ea_shape : (fw_linear ea w).shape = [Lshard, vocab] :=
      fw_linear_2d_shape Lshard h_model vocab ea w hea_shape hw
    have hRHS_local_val : valAt (fw_inner_chunk_ce ea w (chunkPrimDimN 0 2 r y) vocab zLossScale).fst i
        = (let logits := fw_linear ea w
           let l := i
           let labelIdx := scalarToNat (valAt (chunkPrimDimN 0 2 r y) l)
           xentLogSumExp logits l vocab - valAt logits (l * vocab + labelIdx)) := by
      unfold fw_inner_chunk_ce
      simp only [Tensor.mkShape, valAt]
      rw [dif_pos (by
        show i < prodShape [ea.shape.head?.getD 0]
        rw [hea_shape]; simp [prodShape]; linarith)]
    rw [hRHS_local_val]
    -- Now goal shape: `xentLSE (gather[lin_a,lin_b]) outIdx vocab - valAt gather[lin_a,lin_b] (outIdx*vocab+lblG) =
    --                  xentLSE (fw_linear ea w) i vocab - valAt (fw_linear ea w) (i*vocab+lblL)`
    -- where lblG = scalarToNat (valAt y outIdx), lblL = scalarToNat (valAt (chunk y r) i)
    -- Step 1: labels match via chunk 1-D helper
    have hlabel_eq : scalarToNat (valAt y outIdx) = scalarToNat (valAt (chunkPrimDimN 0 2 r y) i) := by
      congr 1
      rw [houtIdx_eq]
      exact (chunkPrimDimN_1d_valAt Lshard hLshard y hy r hr_lt i hi_lt).symm
    -- Step 2: fw_linear commute means gather0[lin_a, lin_b] at rows r*Lshard+i correspond to
    --         fw_linear ea w at row i.
    -- Use allGatherPrimDimN0_valAt (2-D) for each valAt.
    -- For xentLogSumExp: sums over range vocab, using per-row scores.
    -- Compute: valAt (gather[lin_a,lin_b]) ((r*Lshard+i)*vocab+j) = valAt (fw_linear ea w) (i*vocab+j) for j<vocab.
    have hlin_row_eq : ∀ j, j < vocab →
        valAt (allGatherPrimDimN 0 2 0 [fw_linear x_a w, fw_linear x_b w])
              ((r * Lshard + i) * vocab + j)
          = valAt (fw_linear ea w) (i * vocab + j) := by
      intro j hj
      -- Use allGatherPrimDimN0_valAt on [fw_linear x_a w, fw_linear x_b w]
      rw [allGatherPrimDimN0_valAt 2 Lshard vocab [fw_linear x_a w, fw_linear x_b w]
          (by omega) hLshard hvocab hhead_lin hshapes_lin r hr_lt i hi_lt j hj]
      -- Show [fw_linear x_a w, fw_linear x_b w].getD r _ = fw_linear ea w (case on r)
      rcases hr_cases with h | h
      · simp [List.getD, h, hea_def]
      · simp [List.getD, h, hea_def]
    -- Step 3: Rewrite labels & LSE — no need for houtIdx_eq applied to label yet.
    -- The goal after hRHS_local_val + hlin_commute has form:
    --   LHS: xentLSE (gather0) (r*Lshard+i) vocab - valAt (gather0) ((r*Lshard+i)*vocab + scalarToNat (valAt y (r*Lshard+i)))
    --   RHS: xentLSE (fw_linear ea w) i vocab - valAt (fw_linear ea w) (i*vocab + scalarToNat (valAt (chunk y r) i))
    -- Rewrite label match:
    have hlabel_eq' : valAt y (r * Lshard + i) = valAt (chunkPrimDimN 0 2 r y) i :=
      (chunkPrimDimN_1d_valAt Lshard hLshard y hy r hr_lt i hi_lt).symm
    -- LSE equality
    have hlse_eq :
        xentLogSumExp (allGatherPrimDimN 0 2 0 [fw_linear x_a w, fw_linear x_b w]) (r * Lshard + i) vocab
          = xentLogSumExp (fw_linear ea w) i vocab := by
      unfold xentLogSumExp
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj_lt : j < vocab := by simp [Finset.mem_range] at hj; exact hj
      rw [hlin_row_eq j hj_lt]
    -- Combined final rewrite: use `simp only` to substitute in the goal
    simp only [hlabel_eq', hlse_eq]
    -- Now goal reduces to matching the loss term:
    --   valAt (gather0) ((r*Lshard+i)*vocab + lbl) = valAt (fw_linear ea w) (i*vocab + lbl)
    -- where lbl = scalarToNat (valAt (chunkPrimDimN 0 2 r y) i)
    set lbl := scalarToNat (valAt (chunkPrimDimN 0 2 r y) i) with hlbl_def
    have hlbl_lt : lbl < vocab := by
      have h_valAt_eq : valAt (chunkPrimDimN 0 2 r y) i = valAt y (r * Lshard + i) :=
        chunkPrimDimN_1d_valAt Lshard hLshard y hy r hr_lt i hi_lt
      rw [hlbl_def, h_valAt_eq]
      apply hlabels_bound
      calc r * Lshard + i < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
        _ ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
        _ = Lshard * 2 := by ring
    rw [hlin_row_eq lbl hlbl_lt]


-- allGatherPrimDimN_0_shape_2 axiom removed as unused

-- fw_inner_chunk_ce_fst_shape axiom removed as unused (proof uses TrainVerify.Denote.fw_inner_chunk_ce_fst_shape)

-- fw_rms_norm_shape axiom removed as unused (proof uses TrainVerify.Denote.fw_rms_norm_shape)

/-- `fw_maybe_unshuffle` preserves the data tensor's shape (it is an identity). -/
theorem fw_maybe_unshuffle_shape (x cu : Tensor) (cpSize cpRank : Nat) :
    (fw_maybe_unshuffle x cu cpSize cpRank).shape = x.shape := by
  unfold fw_maybe_unshuffle; rfl

-- elemwiseAdd_shape_when_same axiom removed as unused

-- fw_all2all_moe_gmm_shape axiom removed as unused (proof uses TrainVerify.Denote.fw_all2all_moe_gmm_shape)

/-- The SM computation chain preserves batch dim = 4096. -/
theorem sm_chain_shape_4096 (initSM : Store) (hSM : StoreShapesHold initSM sm_goal_1InitEnv) :
    (denoteGraph sm_goal_1 initSM 4673).shape = [4096] := by
  -- Shapes we need from the store hypothesis.
  have h5893 : (initSM 5893).shape = [4096, 1024] := hSM 5893 [4096, 1024] rfl
  have h5895 : (initSM 5895).shape = [4096, 1024] := hSM 5895 [4096, 1024] rfl
  have h5903 : (initSM 5903).shape = [64, 1024, 512] := hSM 5903 [64, 1024, 512] rfl
  -- Innermost: fw_all2all_moe_gmm output shape = [lDim, hModel] where
  -- lDim = input.shape.head? = 4096; hModel = w2.shape.reverse.head? = 512
  -- (w2 = initSM 5903 has shape [64, 1024, 512], so .reverse.head? = some 512).
  have hall2all_shape :
      (fw_all2all_moe_gmm (initSM 5895)
            ((fw_topk_routing (initSM 5898) 8 64).fst)
            ((fw_topk_routing (initSM 5898) 8 64).snd.fst)
            (initSM 5902) (initSM 5903) 64 0 64 8 ((((10 : Nat) : Scalar)))).shape
        = [4096, 1024] :=
    TrainVerify.Denote.fw_all2all_moe_gmm_shape
      _ _ _ _ _ _ _ _ _ _ 4096 1024
      (by rw [h5895]; rfl) (by rw [h5895]; rfl)
  -- elemwiseMul(sigmoid(view [4096,1] ...), view [4096, 1024] ...): outShape2 picks first arg
  -- fw_view [4096, 1] X has shape [4096, 1]; fw_sigmoid preserves shape → [4096, 1].
  -- outShape2 [4096, 1] [4096, 1024] = [4096, 1] (first wins since ≥).
  have hmul_shape :
      (elemwiseMul
        (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906))))
        (fw_view [4096, 1024]
          (fw_linear
            (fw_swiglu
              (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
              (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
            (initSM 5920)))).shape = [4096, 1024] := by
    have hleft : (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906)))).shape = [4096, 1] := by
      rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
    have hright : (fw_view [4096, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
                  (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
                (initSM 5920))).shape = [4096, 1024] := rfl
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, hleft, hright]
    decide
  -- Inner elemwiseAdd(all2all_moe_gmm [4096, 512], elemwiseMul [4096, 1]): outShape2 = [4096, 512]
  have hinner_add_shape :
      (elemwiseAdd
        (fw_all2all_moe_gmm (initSM 5895)
              ((fw_topk_routing (initSM 5898) 8 64).fst)
              ((fw_topk_routing (initSM 5898) 8 64).snd.fst)
              (initSM 5902) (initSM 5903) 64 0 64 8 ((((10 : Nat) : Scalar))))
        (elemwiseMul
          (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906))))
          (fw_view [4096, 1024]
            (fw_linear
              (fw_swiglu
                (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
                (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
              (initSM 5920))))).shape = [4096, 1024] := by
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, hall2all_shape, hmul_shape]
    decide
  -- Outer elemwiseAdd(initSM 5893 [4096, 1024], inner_add [4096, 512]): outShape2 = [4096, 1024]
  have houter_add_shape :
      (elemwiseAdd (initSM 5893)
        (elemwiseAdd
          (fw_all2all_moe_gmm (initSM 5895)
                ((fw_topk_routing (initSM 5898) 8 64).fst)
                ((fw_topk_routing (initSM 5898) 8 64).snd.fst)
                (initSM 5902) (initSM 5903) 64 0 64 8 ((((10 : Nat) : Scalar))))
          (elemwiseMul
            (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906))))
            (fw_view [4096, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
                  (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
                (initSM 5920)))))).shape = [4096, 1024] := by
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, h5893, hinner_add_shape]
    decide
  -- Now compute x_rms.shape = [4096, 1024]:
  -- fw_maybe_unshuffle (data, cu, 1, 0).shape = data.shape (identity model)
  -- fw_rms_norm preserves shape.
  have hx_shape :
      (fw_rms_norm
        (fw_maybe_unshuffle (elemwiseAdd (initSM 5893)
            (elemwiseAdd
              (fw_all2all_moe_gmm (initSM 5895)
                ((fw_topk_routing (initSM 5898) 8 64).fst)
                ((fw_topk_routing (initSM 5898) 8 64).snd.fst)
                (initSM 5902) (initSM 5903) 64 0 64 8 ((((10 : Nat) : Scalar))))
              (elemwiseMul
                (fw_sigmoid (fw_view [4096, 1] (fw_linear (initSM 5895) (initSM 5906))))
                (fw_view [4096, 1024]
                  (fw_linear
                    (fw_swiglu
                      (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5911)))
                      (fw_view [4096, 512] (fw_linear (initSM 5895) (initSM 5915))))
                    (initSM 5920))))))
          (initSM 5927) 1 0)
        (initSM 5929)).shape = [4096, 1024] := by
    rw [TrainVerify.Denote.fw_rms_norm_shape,
        TrainVerify.Denote.fw_maybe_unshuffle_shape,
        houter_add_shape]
  -- fw_inner_chunk_ce.fst.shape = [x.shape.head?.getD 0]
  have hL : _ = some 4096 := congrArg List.head? hx_shape
  rw [denote_sm_goal_1_4673 initSM (by rw [hSM 5898 [4096, 64] (by native_decide)]; rfl)]
  exact TrainVerify.Denote.fw_inner_chunk_ce_fst_shape
    _ _ _ _ _ 4096 hL

/-- The PM computation chain (after allGather) has shape [4096]. -/
theorem pm_chain_shape_4096 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraph pm_goal_1 initPM 4673).shape = [4096] := by
  -- Boundary shape witnesses from the PM init env.
  have h11609 : (initPM 11609).shape = [2048, 1024] := hPM 11609 [2048, 1024] rfl
  have h11610 : (initPM 11610).shape = [2048, 1024] := hPM 11610 [2048, 1024] rfl
  have h11613 : (initPM 11613).shape = [2048, 1024] := hPM 11613 [2048, 1024] rfl
  have h11614 : (initPM 11614).shape = [2048, 1024] := hPM 11614 [2048, 1024] rfl
  have h11631 : (initPM 11631).shape = [32, 1024, 512] := hPM 11631 [32, 1024, 512] rfl
  have h11632 : (initPM 11632).shape = [32, 1024, 512] := hPM 11632 [32, 1024, 512] rfl
  -- Per-rank shape reasoning is symmetric between rank 0 and rank 1.
  -- Show each per-rank fw_inner_chunk_ce(...).fst has shape [2048].
  -- Rank 0 (uses initPM 11609/11613/11631):
  have hgmm0 :
      (fw_all2all_moe_gmm_full (initPM 11613)
        ((fw_topk_routing (initPM 11621) 8 64).fst)
        ((fw_topk_routing (initPM 11621) 8 64).snd.fst)
        [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar)))).shape
        = [2048, 1024] :=
    TrainVerify.Denote.fw_all2all_moe_gmm_full_shape
      _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h11613]; rfl) (by rw [h11613]; rfl)
  have hmul0_shape :
      (elemwiseMul
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
        (fw_view [2048, 1024]
          (fw_linear
            (fw_swiglu
              (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
              (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
            (initPM 5920)))).shape = [2048, 1024] := by
    have hleft : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))).shape = [2048, 1] := by
      rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
    have hright : (fw_view [2048, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                  (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                (initPM 5920))).shape = [2048, 1024] := rfl
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, hleft, hright]
    decide
  have hinner_add0 :
      (elemwiseAdd
        (fw_all2all_moe_gmm_full (initPM 11613)
              ((fw_topk_routing (initPM 11621) 8 64).fst)
              ((fw_topk_routing (initPM 11621) 8 64).snd.fst)
              [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar))))
        (elemwiseMul
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
          (fw_view [2048, 1024]
            (fw_linear
              (fw_swiglu
                (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
              (initPM 5920))))).shape = [2048, 1024] := by
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, hgmm0, hmul0_shape]
    decide
  have houter_add0 :
      (elemwiseAdd (initPM 11609)
        (elemwiseAdd
          (fw_all2all_moe_gmm_full (initPM 11613)
                ((fw_topk_routing (initPM 11621) 8 64).fst)
                ((fw_topk_routing (initPM 11621) 8 64).snd.fst)
                [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar))))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
            (fw_view [2048, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                  (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                (initPM 5920)))))).shape = [2048, 1024] := by
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, h11609, hinner_add0]
    decide
  have hrms0 :
      (fw_rms_norm
        (fw_maybe_unshuffle (elemwiseAdd (initPM 11609)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11613)
                    ((fw_topk_routing (initPM 11621) 8 64).fst)
                    ((fw_topk_routing (initPM 11621) 8 64).snd.fst)
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar))))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                (fw_view [2048, 1024]
                  (fw_linear
                    (fw_swiglu
                      (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                      (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                    (initPM 5920))))))
          (initPM 5927) 2 0)
        (initPM 5929)).shape = [2048, 1024] := by
    rw [TrainVerify.Denote.fw_rms_norm_shape,
        TrainVerify.Denote.fw_maybe_unshuffle_shape,
        houter_add0]
  have hL0 : _ = some 2048 := congrArg List.head? hrms0
  have hfst0 : (fw_inner_chunk_ce _ (initPM 5931) (chunkPrimDimN 0 pm_goal_1.numRanks 0 (initPM 4678))
      (((initPM 5931).shape.head?).getD 0) ((((0 : Nat) : Scalar)))).fst.shape = [2048] :=
    TrainVerify.Denote.fw_inner_chunk_ce_fst_shape _ _ _ _ _ 2048 hL0
  -- Rank 1 (uses initPM 11610/11614/11632 with different expert slice range):
  have hgmm1 :
      (fw_all2all_moe_gmm_full (initPM 11614)
        ((fw_topk_routing (initPM 11622) 8 64).fst)
        ((fw_topk_routing (initPM 11622) 8 64).snd.fst)
        [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar)))).shape
        = [2048, 1024] :=
    TrainVerify.Denote.fw_all2all_moe_gmm_full_shape
      _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h11614]; rfl) (by rw [h11614]; rfl)
  have hmul1_shape :
      (elemwiseMul
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
        (fw_view [2048, 1024]
          (fw_linear
            (fw_swiglu
              (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
              (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
            (initPM 5920)))).shape = [2048, 1024] := by
    have hleft : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))).shape = [2048, 1] := by
      rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
    have hright : (fw_view [2048, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                  (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                (initPM 5920))).shape = [2048, 1024] := rfl
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, hleft, hright]
    decide
  have hinner_add1 :
      (elemwiseAdd
        (fw_all2all_moe_gmm_full (initPM 11614)
              ((fw_topk_routing (initPM 11622) 8 64).fst)
              ((fw_topk_routing (initPM 11622) 8 64).snd.fst)
              [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar))))
        (elemwiseMul
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
          (fw_view [2048, 1024]
            (fw_linear
              (fw_swiglu
                (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
              (initPM 5920))))).shape = [2048, 1024] := by
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, hgmm1, hmul1_shape]
    decide
  have houter_add1 :
      (elemwiseAdd (initPM 11610)
        (elemwiseAdd
          (fw_all2all_moe_gmm_full (initPM 11614)
                ((fw_topk_routing (initPM 11622) 8 64).fst)
                ((fw_topk_routing (initPM 11622) 8 64).snd.fst)
                [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar))))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
            (fw_view [2048, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                  (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                (initPM 5920)))))).shape = [2048, 1024] := by
    show (Tensor.mkShape (outShape2 _ _) _).shape = _
    simp only [Tensor.mkShape, outShape2, h11610, hinner_add1]
    decide
  have hrms1 :
      (fw_rms_norm
        (fw_maybe_unshuffle (elemwiseAdd (initPM 11610)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11614)
                    ((fw_topk_routing (initPM 11622) 8 64).fst)
                    ((fw_topk_routing (initPM 11622) 8 64).snd.fst)
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 ((((10 : Nat) : Scalar))))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                (fw_view [2048, 1024]
                  (fw_linear
                    (fw_swiglu
                      (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                      (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                    (initPM 5920))))))
          (initPM 5927) 2 1)
        (initPM 5929)).shape = [2048, 1024] := by
    rw [TrainVerify.Denote.fw_rms_norm_shape,
        TrainVerify.Denote.fw_maybe_unshuffle_shape,
        houter_add1]
  have hL1 : _ = some 2048 := congrArg List.head? hrms1
  have hfst1 : (fw_inner_chunk_ce _ (initPM 5931) (chunkPrimDimN 0 pm_goal_1.numRanks 1 (initPM 4678))
      (((initPM 5931).shape.head?).getD 0) ((((0 : Nat) : Scalar)))).fst.shape = [2048] :=
    TrainVerify.Denote.fw_inner_chunk_ce_fst_shape _ _ _ _ _ 2048 hL1
  -- allGatherPrimDimN 0 2 0 [T0, T1] where T0.shape = [2048], T1.shape = [2048]:
  -- output shape = [2048].set 0 (2048 * 2) = [4096]
  rw [denote_pm_goal_1_4673 initPM (by rw [hPM 11621 [2048, 64] (by native_decide)]; rfl) (by rw [hPM 11622 [2048, 64] (by native_decide)]; rfl)]
  have hpn : pm_goal_1.numRanks = 2 := rfl
  rw [hpn]
  -- Apply allGatherPrimDimN_shape with shardShape = [2048].
  -- The first list element is a fw_inner_chunk_ce(...).fst whose shape is [2048] (by hfst0).
  rw [allGatherPrimDimN_shape 0 2 _ [2048] (by
    show (Option.map (fun (t : Tensor) => t.shape) (some _)).getD [] = [2048]
    simp only [Option.map_some, Option.getD_some]
    exact hfst0)]
  decide

theorem prove_goal_1 : goal_1_stmt_with_labels := by
  intro initSM initPM hSM hPM hInit hlabels_from_caller
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
        (_ : g.replicated = false)
        (_ : g.ts = tid),
        initSM tid = initPM tid := by
      intro g hg tid htp hgd hrep hts
      have h := hInit' g hg
      unfold InitGoalHolds at h
      have hval := h.2.2
      rw [reconstructForGoal_of_not_replicated g pm_goal_1.numRanks
            (g.tps.map (fun p => initPM p.tid)) hrep] at hval
      rw [htp, hts, hgd] at hval
      simp only [List.map, reconstructWithDim] at hval
      exact hval
    -- Extract sharded boundary linkages (initSM tid = allGather_0 [initPM p0, initPM p1]).
    have extract_dual : ∀ (g : LineageGoal) (_ : g ∈ goal_1_cut_initGoals)
        (ts p0 p1 : Nat) (sh : Shape)
        (_ : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
        (_ : g.gatherDim = 0) (_ : g.replicated = false) (_ : g.ts = ts)
        (_ : (initPM p0).shape = sh) (_ : sh ≠ [1]),
        initSM ts = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM p0, initPM p1] := by
      intro g hg ts p0 p1 sh htp hgd hrep hts hshape hne
      have h := hInit' g hg
      unfold InitGoalHolds at h
      have hval := h.2.2
      rw [reconstructForGoal_of_not_replicated g pm_goal_1.numRanks
            (g.tps.map (fun p => initPM p.tid)) hrep] at hval
      rw [htp, hts, hgd] at hval
      simp only [List.map, reconstructWithDim, List.head?, Option.map, Option.getD,
                 hshape, if_neg hne] at hval
      exact hval
    -- Boundary hypotheses (SM shared boundaries → PM identity).
    have hb_4678 : initSM 4678 = initPM 4678 :=
      extract_singleton initGoal_4678 (by native_decide) 4678 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5906 : initSM 5906 = initPM 5906 :=
      extract_singleton initGoal_5906 (by native_decide) 5906 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5911 : initSM 5911 = initPM 5911 :=
      extract_singleton initGoal_5911 (by native_decide) 5911 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5915 : initSM 5915 = initPM 5915 :=
      extract_singleton initGoal_5915 (by native_decide) 5915 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5920 : initSM 5920 = initPM 5920 :=
      extract_singleton initGoal_5920 (by native_decide) 5920 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5927 : initSM 5927 = initPM 5927 :=
      extract_singleton initGoal_5927 (by native_decide) 5927 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5929 : initSM 5929 = initPM 5929 :=
      extract_singleton initGoal_5929 (by native_decide) 5929 (by rfl) (by rfl) (by rfl) (by rfl)
    have hb_5931 : initSM 5931 = initPM 5931 :=
      extract_singleton initGoal_5931 (by native_decide) 5931 (by rfl) (by rfl) (by rfl) (by rfl)
    -- SM sharded boundaries → PM allGather form.
    have h11609_shape : (initPM 11609).shape = [2048, 1024] := hPM 11609 [2048, 1024] (by native_decide)
    have h11613_shape : (initPM 11613).shape = [2048, 1024] := hPM 11613 [2048, 1024] (by native_decide)
    have h11621_shape : (initPM 11621).shape = [2048, 64] := hPM 11621 [2048, 64] (by native_decide)
    have h11629_shape : (initPM 11629).shape = [32, 1024, 1024] := hPM 11629 [32, 1024, 1024] (by native_decide)
    have h11631_shape : (initPM 11631).shape = [32, 1024, 512] := hPM 11631 [32, 1024, 512] (by native_decide)
    have hb_5893 : initSM 5893 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11609, initPM 11610] :=
      extract_dual intermediateGoal_5893 (by native_decide) 5893 11609 11610 [2048, 1024]
        (by rfl) (by rfl) (by rfl) (by rfl) h11609_shape (by decide)
    have hb_5895 : initSM 5895 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11613, initPM 11614] :=
      extract_dual intermediateGoal_5895 (by native_decide) 5895 11613 11614 [2048, 1024]
        (by rfl) (by rfl) (by rfl) (by rfl) h11613_shape (by decide)
    have hb_5898 : initSM 5898 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11621, initPM 11622] :=
      extract_dual intermediateGoal_5898 (by native_decide) 5898 11621 11622 [2048, 64]
        (by rfl) (by rfl) (by rfl) (by rfl) h11621_shape (by decide)
    have hb_5902 : initSM 5902 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11629, initPM 11630] :=
      extract_dual initGoal_5902 (by native_decide) 5902 11629 11630 [32, 1024, 1024]
        (by rfl) (by rfl) (by rfl) (by rfl) h11629_shape (by decide)
    have hb_5903 : initSM 5903 = allGatherPrimDimN 0 pm_goal_1.numRanks 0 [initPM 11631, initPM 11632] :=
      extract_dual initGoal_5903 (by native_decide) 5903 11631 11632 [32, 1024, 512]
        (by rfl) (by rfl) (by rfl) (by rfl) h11631_shape (by decide)
    -- Reconstruct singleton [x] = x.
    simp only [List.map, reconstructWithDim]
    -- Reduce SM and PM via machinery.
    rw [denote_sm_goal_1_4673 initSM (by rw [hSM 5898 [4096, 64] (by native_decide)]; rfl),
        denote_pm_goal_1_4673 initPM (by rw [hPM 11621 [2048, 64] (by native_decide)]; rfl) (by rw [hPM 11622 [2048, 64] (by native_decide)]; rfl)]
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
    -- Shape witnesses for the fw_linear weights (moved up so fw_linear_of can use).
    have h5906_shape : (initPM 5906).shape = [1, 1024] := hPM 5906 [1, 1024] rfl
    have h5911_shape : (initPM 5911).shape = [512, 1024] := hPM 5911 [512, 1024] rfl
    have h5915_shape : (initPM 5915).shape = [512, 1024] := hPM 5915 [512, 1024] rfl
    have h5920_shape : (initPM 5920).shape = [1024, 512] := hPM 5920 [1024, 512] rfl
    -- Push allGather through fw_linear (3 occurrences: linear→sigmoid, linear→swiglu×2).
    rw [fw_linear_allGather0_commute_2_of (initPM 11613) (initPM 11614) (initPM 5906)
          2048 1024 1 (by omega) (by omega) (by omega) h11613_shape h11614_shape h5906_shape]
    rw [fw_linear_allGather0_commute_2_of (initPM 11613) (initPM 11614) (initPM 5911)
          2048 1024 512 (by omega) (by omega) (by omega) h11613_shape h11614_shape h5911_shape]
    rw [fw_linear_allGather0_commute_2_of (initPM 11613) (initPM 11614) (initPM 5915)
          2048 1024 512 (by omega) (by omega) (by omega) h11613_shape h11614_shape h5915_shape]
    -- Push through fw_view. Use the proven `fw_view_allGather0_commute_2_of` with shape witnesses.
    -- (h5906/5911/5915/5920_shape already established above.)
    have hlin_5906_a : (fw_linear (initPM 11613) (initPM 5906)).shape = [2048, 1] :=
      fw_linear_2d_shape 2048 1024 1 _ _ h11613_shape h5906_shape
    have hlin_5906_b : (fw_linear (initPM 11614) (initPM 5906)).shape = [2048, 1] :=
      fw_linear_2d_shape 2048 1024 1 _ _ (hPM 11614 [2048, 1024] rfl) h5906_shape
    have hlin_5911_a : (fw_linear (initPM 11613) (initPM 5911)).shape = [2048, 512] :=
      fw_linear_2d_shape 2048 1024 512 _ _ h11613_shape h5911_shape
    have hlin_5911_b : (fw_linear (initPM 11614) (initPM 5911)).shape = [2048, 512] :=
      fw_linear_2d_shape 2048 1024 512 _ _ (hPM 11614 [2048, 1024] rfl) h5911_shape
    have hlin_5915_a : (fw_linear (initPM 11613) (initPM 5915)).shape = [2048, 512] :=
      fw_linear_2d_shape 2048 1024 512 _ _ h11613_shape h5915_shape
    have hlin_5915_b : (fw_linear (initPM 11614) (initPM 5915)).shape = [2048, 512] :=
      fw_linear_2d_shape 2048 1024 512 _ _ (hPM 11614 [2048, 1024] rfl) h5915_shape
    rw [fw_view_allGather0_commute_2_of (fw_linear (initPM 11613) (initPM 5906))
          (fw_linear (initPM 11614) (initPM 5906)) 2048 1 (by omega) hlin_5906_a hlin_5906_b]
    rw [fw_view_allGather0_commute_2_of (fw_linear (initPM 11613) (initPM 5911))
          (fw_linear (initPM 11614) (initPM 5911)) 2048 512 (by omega) hlin_5911_a hlin_5911_b]
    rw [fw_view_allGather0_commute_2_of (fw_linear (initPM 11613) (initPM 5915))
          (fw_linear (initPM 11614) (initPM 5915)) 2048 512 (by omega) hlin_5915_a hlin_5915_b]
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
    -- Push through fw_linear (for 5920). Input is swiglu output [2048, 512], weight 5920 = [1024, 512].
    have hswiglu_a_shape_pre : (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                          (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915)))).shape = [2048, 512] := by
      rw [TrainVerify.Denote.fw_swiglu_shape]; rfl
    have hswiglu_b_shape_pre : (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                          (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915)))).shape = [2048, 512] := by
      rw [TrainVerify.Denote.fw_swiglu_shape]; rfl
    rw [fw_linear_allGather0_commute_2_of
          (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                     (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
          (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                     (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
          (initPM 5920) 2048 512 1024 (by omega) (by omega) (by omega)
          hswiglu_a_shape_pre hswiglu_b_shape_pre h5920_shape]
    -- Push through fw_view (post-linear-5920).
    have hswiglu_a_shape : (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                       (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915)))).shape = [2048, 512] := by
      rw [TrainVerify.Denote.fw_swiglu_shape]; rfl
    have hswiglu_b_shape : (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                       (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915)))).shape = [2048, 512] := by
      rw [TrainVerify.Denote.fw_swiglu_shape]; rfl
    have hlin_5920_a : (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                              (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                   (initPM 5920)).shape = [2048, 1024] :=
      fw_linear_2d_shape 2048 512 1024 _ _ hswiglu_a_shape h5920_shape
    have hlin_5920_b : (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                              (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                   (initPM 5920)).shape = [2048, 1024] :=
      fw_linear_2d_shape 2048 512 1024 _ _ hswiglu_b_shape h5920_shape
    rw [fw_view_allGather0_commute_2_of
          (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                     (initPM 5920))
          (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                     (initPM 5920))
          2048 1024 (by omega) hlin_5920_a hlin_5920_b]
    -- Push through fw_mul. Broadcast [2048, 1] * [2048, 1024] version.
    have hsig_a_shape : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))).shape = [2048, 1] := by
      rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
    have hsig_b_shape : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))).shape = [2048, 1] := by
      rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
    have hview_c_shape : (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                       (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                            (initPM 5920))).shape = [2048, 1024] := rfl
    have hview_d_shape : (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                       (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                            (initPM 5920))).shape = [2048, 1024] := rfl
    rw [fw_mul_allGather0_commute_2_of_broadcast
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
          (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                       (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                            (initPM 5920)))
          (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                       (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                            (initPM 5920)))
          2048 1024 (by omega) (by omega) (by omega) (by omega) (by omega)
          hsig_a_shape hsig_b_shape hview_c_shape hview_d_shape]
    -- Push through fw_topk_routing (both .fst and .snd.fst) — using consistent theorem forms.
    -- Requires h11621_shape / h11622_shape witnesses: [2048, 64] (S=2048, numExperts=k=64).
    have h11621_shape : (initPM 11621).shape = [2048, 64] := hPM 11621 [2048, 64] rfl
    have h11622_shape : (initPM 11622).shape = [2048, 64] := hPM 11622 [2048, 64] rfl
    rw [fw_topk_routing_fst_allGather0_commute_2_of (initPM 11621) (initPM 11622) 2048 8 64
          (by omega) (by omega) h11621_shape h11622_shape]
    rw [fw_topk_routing_snd_fst_allGather0_commute_2_of (initPM 11621) (initPM 11622) 2048 8 64
          (by omega) (by omega) h11621_shape h11622_shape]
    -- Push through fw_all2all_moe_gmm using proven theorem.
    -- Shape witnesses
    have h11613_shape : (initPM 11613).shape = [2048, 1024] := hPM 11613 [2048, 1024] rfl
    have h11614_shape : (initPM 11614).shape = [2048, 1024] := hPM 11614 [2048, 1024] rfl
    have h11629_shape : (initPM 11629).shape = [32, 1024, 1024] := hPM 11629 [32, 1024, 1024] rfl
    have h11630_shape : (initPM 11630).shape = [32, 1024, 1024] := hPM 11630 [32, 1024, 1024] rfl
    have h11631_shape : (initPM 11631).shape = [32, 1024, 512] := hPM 11631 [32, 1024, 512] rfl
    have h11632_shape : (initPM 11632).shape = [32, 1024, 512] := hPM 11632 [32, 1024, 512] rfl
    -- Routing map shape (fw_topk_routing_snd_fst outputs)
    have hrp_a_shape : (fw_topk_routing (initPM 11621) 8 64).fst.shape = [2048, 32 * 2] := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape]
      rw [h11621_shape]; rfl
    have hrp_b_shape : (fw_topk_routing (initPM 11622) 8 64).fst.shape = [2048, 32 * 2] := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape]
      rw [h11622_shape]; rfl
    have hrm_a_shape : (fw_topk_routing (initPM 11621) 8 64).snd.fst.shape = [2048, 32 * 2] := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape]
      rw [h11621_shape]; rfl
    have hrm_b_shape : (fw_topk_routing (initPM 11622) 8 64).snd.fst.shape = [2048, 32 * 2] := by
      unfold fw_topk_routing
      simp only [Tensor.mkShape]
      rw [h11622_shape]; rfl
    -- Migrate SM-side fw_all2all_moe_gmm (on gathered weights) → fw_all2all_moe_gmm_full.
    -- The bridge lemma requires the pattern `allGather 0 w13s.length 0 w13s`, so first
    -- convert `allGather 0 2 0 [...]` → `allGather 0 [...].length 0 [...]`.
    conv_lhs =>
      pattern fw_all2all_moe_gmm _ _ _
        (allGatherPrimDimN 0 2 0 [initPM 11629, initPM 11630])
        (allGatherPrimDimN 0 2 0 [initPM 11631, initPM 11632]) 64 0 64 8 _
      rw [show (allGatherPrimDimN 0 2 0 [initPM 11629, initPM 11630]
                = allGatherPrimDimN 0 ([initPM 11629, initPM 11630] : List Tensor).length 0
                                       [initPM 11629, initPM 11630]) from rfl,
          show (allGatherPrimDimN 0 2 0 [initPM 11631, initPM 11632]
                = allGatherPrimDimN 0 ([initPM 11631, initPM 11632] : List Tensor).length 0
                                       [initPM 11631, initPM 11632]) from rfl,
          fw_all2all_moe_gmm_eq_full_on_shards _ _ _ _ _ _ _ _ (by rfl)]
    rw [fw_all2all_moe_gmm_full_split_commute_2
          (initPM 11613) (initPM 11614)
          (fw_topk_routing (initPM 11621) 8 64).fst (fw_topk_routing (initPM 11622) 8 64).fst
          (fw_topk_routing (initPM 11621) 8 64).snd.fst (fw_topk_routing (initPM 11622) 8 64).snd.fst
          (initPM 11629) (initPM 11630)
          (initPM 11631) (initPM 11632)
          2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
          (by omega) (by omega) (by omega) (by omega) (by omega) (by ring)
          h11613_shape h11614_shape hrp_a_shape hrp_b_shape hrm_a_shape hrm_b_shape
          h11629_shape h11630_shape h11631_shape h11632_shape]
    -- Push through inner elemwiseAdd (all2all + mul).
    -- All 4 tensors have shape [2048, 1024]: all2all_moe_gmm output matches input's
    -- hidden dim (1024, after Denote hModel fix); elemwiseMul(sigmoid([2048,1]),
    -- view([2048,1024])) broadcasts to [2048, 1024] (per-dim max, after Denote outShape2 fix).
    have hgmm0_local : (fw_all2all_moe_gmm_full (initPM 11613) (fw_topk_routing (initPM 11621) 8 64).fst
              (fw_topk_routing (initPM 11621) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
              64 8 (((10 : Nat) : Scalar))).shape = [2048, 1024] :=
      TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
        (by rw [h11613_shape]; rfl) (by rw [h11613_shape]; rfl)
    have hgmm1_local : (fw_all2all_moe_gmm_full (initPM 11614) (fw_topk_routing (initPM 11622) 8 64).fst
              (fw_topk_routing (initPM 11622) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
              64 8 (((10 : Nat) : Scalar))).shape = [2048, 1024] :=
      TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
        (by rw [h11614_shape]; rfl) (by rw [h11614_shape]; rfl)
    have hmul0_local : (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                             (initPM 5920)))).shape = [2048, 1024] := by
      have hleft : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))).shape = [2048, 1] := by
        rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
      have hright : (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                             (initPM 5920))).shape = [2048, 1024] := rfl
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hleft, hright]
      decide
    have hmul1_local : (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                             (initPM 5920)))).shape = [2048, 1024] := by
      have hleft : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))).shape = [2048, 1] := by
        rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
      have hright : (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                             (initPM 5920))).shape = [2048, 1024] := rfl
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hleft, hright]
      decide
    rw [fw_add_allGather0_commute_2_2048_1024
          (fw_all2all_moe_gmm_full (initPM 11613) (fw_topk_routing (initPM 11621) 8 64).fst
            (fw_topk_routing (initPM 11621) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
            64 8 (((10 : Nat) : Scalar)))
          (fw_all2all_moe_gmm_full (initPM 11614) (fw_topk_routing (initPM 11622) 8 64).fst
            (fw_topk_routing (initPM 11622) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
            64 8 (((10 : Nat) : Scalar)))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                             (initPM 5920))))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                             (initPM 5920))))
          hgmm0_local hgmm1_local hmul0_local hmul1_local]
    -- Push through outer elemwiseAdd (initPM 11609/11610 + inner).
    -- All 4 args have shape [2048, 1024].
    have hinner_add0_local :
        (elemwiseAdd
          (fw_all2all_moe_gmm_full (initPM 11613) (fw_topk_routing (initPM 11621) 8 64).fst
            (fw_topk_routing (initPM 11621) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
            64 8 (((10 : Nat) : Scalar)))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                             (initPM 5920))))).shape = [2048, 1024] := by
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hgmm0_local, hmul0_local]
      decide
    have hinner_add1_local :
        (elemwiseAdd
          (fw_all2all_moe_gmm_full (initPM 11614) (fw_topk_routing (initPM 11622) 8 64).fst
            (fw_topk_routing (initPM 11622) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
            64 8 (((10 : Nat) : Scalar)))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
            (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                        (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                             (initPM 5920))))).shape = [2048, 1024] := by
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hgmm1_local, hmul1_local]
      decide
    rw [fw_add_allGather0_commute_2_2048_1024 (initPM 11609) (initPM 11610)
          (elemwiseAdd
            (fw_all2all_moe_gmm_full (initPM 11613) (fw_topk_routing (initPM 11621) 8 64).fst
              (fw_topk_routing (initPM 11621) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
              64 8 (((10 : Nat) : Scalar)))
            (elemwiseMul
              (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
              (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                          (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                               (initPM 5920)))))
          (elemwiseAdd
            (fw_all2all_moe_gmm_full (initPM 11614) (fw_topk_routing (initPM 11622) 8 64).fst
              (fw_topk_routing (initPM 11622) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632]
              64 8 (((10 : Nat) : Scalar)))
            (elemwiseMul
              (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
              (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                          (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                               (initPM 5920)))))
          h11609_shape h11610_shape hinner_add0_local hinner_add1_local]
    -- Push through fw_maybe_unshuffle (converts cpSize=1 → cpSize=2×2).
    rw [fw_maybe_unshuffle_cp2_commute
          (elemwiseAdd (initPM 11609)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11613) (fw_topk_routing (initPM 11621) 8 64).fst
                (fw_topk_routing (initPM 11621) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                            (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                                 (initPM 5920))))))
          (elemwiseAdd (initPM 11610)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11614) (fw_topk_routing (initPM 11622) 8 64).fst
                (fw_topk_routing (initPM 11622) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                            (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                                 (initPM 5920))))))
          (initPM 5927)]
    -- Push through fw_rms_norm.
    -- After fw_maybe_unshuffle fix (identity model), the input shape is [2048, 1024] (2-dim).
    -- Establish the shape via fw_maybe_unshuffle_shape + elemwiseAdd/Mul shape reasoning.
    have h11609 : (initPM 11609).shape = [2048, 1024] := hPM 11609 [2048, 1024] rfl
    have h11610 : (initPM 11610).shape = [2048, 1024] := hPM 11610 [2048, 1024] rfl
    have h11613 : (initPM 11613).shape = [2048, 1024] := hPM 11613 [2048, 1024] rfl
    have h11614 : (initPM 11614).shape = [2048, 1024] := hPM 11614 [2048, 1024] rfl
    have h11631 : (initPM 11631).shape = [32, 1024, 512] := hPM 11631 [32, 1024, 512] rfl
    have h11632 : (initPM 11632).shape = [32, 1024, 512] := hPM 11632 [32, 1024, 512] rfl
    -- Rank 0's input to fw_maybe_unshuffle has shape [2048, 1024].
    have hgmm0_shape :
        (fw_all2all_moe_gmm_full (initPM 11613)
          (fw_topk_routing (initPM 11621) 8 64).fst
          (fw_topk_routing (initPM 11621) 8 64).snd.fst
          [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar))).shape
          = [2048, 1024] :=
      TrainVerify.Denote.fw_all2all_moe_gmm_full_shape
        _ _ _ _ _ _ _ _ 2048 1024
        (by rw [h11613]; rfl) (by rw [h11613]; rfl)
    have hmul0_shape :
        (elemwiseMul
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
          (fw_view [2048, 1024]
            (fw_linear
              (fw_swiglu
                (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
              (initPM 5920)))).shape = [2048, 1024] := by
      have hleft : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906)))).shape = [2048, 1] := by
        rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
      have hright : (fw_view [2048, 1024]
                (fw_linear
                  (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                  (initPM 5920))).shape = [2048, 1024] := rfl
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hleft, hright]
      decide
    have hinner_add0_shape :
        (elemwiseAdd
          (fw_all2all_moe_gmm_full (initPM 11613)
                (fw_topk_routing (initPM 11621) 8 64).fst
                (fw_topk_routing (initPM 11621) 8 64).snd.fst
                [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
            (fw_view [2048, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                  (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                (initPM 5920))))).shape = [2048, 1024] := by
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hgmm0_shape, hmul0_shape]
      decide
    have houter_add0_shape :
        (elemwiseAdd (initPM 11609)
          (elemwiseAdd
            (fw_all2all_moe_gmm_full (initPM 11613)
                  (fw_topk_routing (initPM 11621) 8 64).fst
                  (fw_topk_routing (initPM 11621) 8 64).snd.fst
                  [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
            (elemwiseMul
              (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
              (fw_view [2048, 1024]
                (fw_linear
                  (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                  (initPM 5920)))))).shape = [2048, 1024] := by
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, h11609, hinner_add0_shape]
      decide
    have hunshuffle0_shape :
        (fw_maybe_unshuffle (elemwiseAdd (initPM 11609)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11613)
                    (fw_topk_routing (initPM 11621) 8 64).fst
                    (fw_topk_routing (initPM 11621) 8 64).snd.fst
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                (fw_view [2048, 1024]
                  (fw_linear
                    (fw_swiglu
                      (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                      (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                    (initPM 5920))))))
          (initPM 5927) 2 0).shape = [2048, 1024] := by
      rw [TrainVerify.Denote.fw_maybe_unshuffle_shape]; exact houter_add0_shape
    -- Rank 1 (mirror of rank 0):
    have hgmm1_shape :
        (fw_all2all_moe_gmm_full (initPM 11614)
          (fw_topk_routing (initPM 11622) 8 64).fst
          (fw_topk_routing (initPM 11622) 8 64).snd.fst
          [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar))).shape
          = [2048, 1024] :=
      TrainVerify.Denote.fw_all2all_moe_gmm_full_shape
        _ _ _ _ _ _ _ _ 2048 1024
        (by rw [h11614]; rfl) (by rw [h11614]; rfl)
    have hmul1_shape :
        (elemwiseMul
          (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
          (fw_view [2048, 1024]
            (fw_linear
              (fw_swiglu
                (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
              (initPM 5920)))).shape = [2048, 1024] := by
      have hleft : (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906)))).shape = [2048, 1] := by
        rw [TrainVerify.Denote.fw_sigmoid_shape]; rfl
      have hright : (fw_view [2048, 1024]
                (fw_linear
                  (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                  (initPM 5920))).shape = [2048, 1024] := rfl
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hleft, hright]
      decide
    have hinner_add1_shape :
        (elemwiseAdd
          (fw_all2all_moe_gmm_full (initPM 11614)
                (fw_topk_routing (initPM 11622) 8 64).fst
                (fw_topk_routing (initPM 11622) 8 64).snd.fst
                [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
          (elemwiseMul
            (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
            (fw_view [2048, 1024]
              (fw_linear
                (fw_swiglu
                  (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                  (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                (initPM 5920))))).shape = [2048, 1024] := by
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, hgmm1_shape, hmul1_shape]
      decide
    have houter_add1_shape :
        (elemwiseAdd (initPM 11610)
          (elemwiseAdd
            (fw_all2all_moe_gmm_full (initPM 11614)
                  (fw_topk_routing (initPM 11622) 8 64).fst
                  (fw_topk_routing (initPM 11622) 8 64).snd.fst
                  [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
            (elemwiseMul
              (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
              (fw_view [2048, 1024]
                (fw_linear
                  (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                  (initPM 5920)))))).shape = [2048, 1024] := by
      show (Tensor.mkShape (outShape2 _ _) _).shape = _
      simp only [Tensor.mkShape, outShape2, h11610, hinner_add1_shape]
      decide
    have hunshuffle1_shape :
        (fw_maybe_unshuffle (elemwiseAdd (initPM 11610)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11614)
                    (fw_topk_routing (initPM 11622) 8 64).fst
                    (fw_topk_routing (initPM 11622) 8 64).snd.fst
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul
                (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                (fw_view [2048, 1024]
                  (fw_linear
                    (fw_swiglu
                      (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                      (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                    (initPM 5920))))))
          (initPM 5927) 2 1).shape = [2048, 1024] := by
      rw [TrainVerify.Denote.fw_maybe_unshuffle_shape]; exact houter_add1_shape
    rw [fw_rms_norm_allGather0_commute_2
          (fw_maybe_unshuffle
            (elemwiseAdd (initPM 11609)
              (elemwiseAdd
                (fw_all2all_moe_gmm_full (initPM 11613) (fw_topk_routing (initPM 11621) 8 64).fst
                  (fw_topk_routing (initPM 11621) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
                (elemwiseMul
                  (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                  (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                                                              (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                                                   (initPM 5920)))))) (initPM 5927) 2 0)
          (fw_maybe_unshuffle
            (elemwiseAdd (initPM 11610)
              (elemwiseAdd
                (fw_all2all_moe_gmm_full (initPM 11614) (fw_topk_routing (initPM 11622) 8 64).fst
                  (fw_topk_routing (initPM 11622) 8 64).snd.fst [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
                (elemwiseMul
                  (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                  (fw_view [2048, 1024] (fw_linear (fw_swiglu (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                                                              (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                                                   (initPM 5920)))))) (initPM 5927) 2 1)
          (initPM 5929) 2048 1024 (by omega) (by omega)
          hunshuffle0_shape hunshuffle1_shape]
    -- Push through fw_inner_chunk_ce using proven theorem.
    -- Args are `fw_rms_norm (fw_maybe_unshuffle ...)` per rank, wrapping the inner add chain.
    have h4678_shape : (initPM 4678).shape = [4096] := hPM 4678 [4096] rfl
    have h5931_shape : (initPM 5931).shape = [154880, 1024] := hPM 5931 [154880, 1024] rfl
    have hvocab_eq : ((List.head? (initPM 5931).shape).getD 0) = 154880 := by rw [h5931_shape]; rfl
    -- rms_norm preserves shape → [2048, 1024]
    have hxa_shape : (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11609)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11613)
                    (fw_topk_routing (initPM 11621) 8 64).fst
                    (fw_topk_routing (initPM 11621) 8 64).snd.fst
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                  (initPM 5920)))))) (initPM 5927) 2 0) (initPM 5929)).shape = [2048, 1024] := by
      rw [TrainVerify.Denote.fw_rms_norm_shape]; exact hunshuffle0_shape
    have hxb_shape : (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11610)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11614)
                    (fw_topk_routing (initPM 11622) 8 64).fst
                    (fw_topk_routing (initPM 11622) 8 64).snd.fst
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                  (initPM 5920)))))) (initPM 5927) 2 1) (initPM 5929)).shape = [2048, 1024] := by
      rw [TrainVerify.Denote.fw_rms_norm_shape]; exact hunshuffle1_shape
    -- Training-data hygiene: labels are bounded by vocab. Provided by caller as
    -- a statement-level hypothesis (`hlabels_from_caller`); previously an unsound
    -- axiom `Pattern_1_labelsAxiom` (now removed).
    have hlabels_bound : ∀ l < 2048 * 2, scalarToNat (valAt (initPM 4678) l) < 154880 := by
      intro l hl
      exact hlabels_from_caller l (by omega)
    -- Substitute vocab first
    rw [hvocab_eq]
    rw [fw_inner_chunk_ce_fst_allGather0_commute_2_of
          (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11609)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11613)
                    (fw_topk_routing (initPM 11621) 8 64).fst
                    (fw_topk_routing (initPM 11621) 8 64).snd.fst
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11613) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11613) (initPM 5915))))
                  (initPM 5920)))))) (initPM 5927) 2 0) (initPM 5929))
          (fw_rms_norm (fw_maybe_unshuffle (elemwiseAdd (initPM 11610)
            (elemwiseAdd
              (fw_all2all_moe_gmm_full (initPM 11614)
                    (fw_topk_routing (initPM 11622) 8 64).fst
                    (fw_topk_routing (initPM 11622) 8 64).snd.fst
                    [initPM 11629, initPM 11630] [initPM 11631, initPM 11632] 64 8 (((10 : Nat) : Scalar)))
              (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (initPM 11614) (initPM 5906))))
                (fw_view [2048, 1024] (fw_linear (fw_swiglu
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5911)))
                    (fw_view [2048, 512] (fw_linear (initPM 11614) (initPM 5915))))
                  (initPM 5920)))))) (initPM 5927) 2 1) (initPM 5929))
          (initPM 5931) (initPM 4678)
          2048 1024 154880 (by omega) (by omega) (by omega)
          hxa_shape hxb_shape h5931_shape (by rw [h4678_shape])
          hlabels_bound (((0 : Nat) : Scalar))]


theorem prove_pattern_1 : pattern_1_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_1

end TrainVerify.Denote.GeneratedPatterns