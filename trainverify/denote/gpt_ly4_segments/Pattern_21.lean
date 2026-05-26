/- Auto-generated pattern proof file.
   Pattern: 21
   Hash: 0c671a7b0d6e6d62
   Goals: 25, 50, 105
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_127
import denote.gpt_ly4_segments.Pattern_44

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_21_goalIds : List Nat := [25, 50, 105]
inductive pattern_21_target : Prop → Prop
  | goal_25 : pattern_21_target goal_25_stmt
  | goal_50 : pattern_21_target goal_50_stmt
  | goal_105 : pattern_21_target goal_105_stmt

def pattern_21_stmt : Prop :=
  ∀ {target : Prop}, pattern_21_target target → target

set_option maxRecDepth 32768

/-! ## Chunk-of-allGather inverse for shape `[1, 2, 32]` (copied from Pattern_5). -/

private lemma valAt_ag1_1_2_32_pj_p21 (xs : List Tensor) (p j : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [1, 2, 32])
    (hp : p < 8) (hj : j < 32) :
    valAt (allGatherPrimDimN 1 4 0 xs) (p * 32 + j) =
      valAt (xs.getD (p / 2) (zeroTensor [1, 2, 32])) ((p % 2) * 32 + j) := by
  have hshape_out : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hidx_lt : p * 32 + j < 256 := by
    have : p * 32 ≤ 7 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  have hlt_prod : p * 32 + j < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hshape_out]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hlt_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.drop, List.foldl,
    show ([1, 2, 32] : List Nat).getD 1 0 = 2 from rfl,
    show (2 : Nat) * 4 * 32 = 256 from by norm_num,
    show (2 : Nat) * 32 = 64 from by norm_num,
    show (256 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega,
    ite_false]
  have hd256 : (p * 32 + j) / 256 = 0 := by
    apply Nat.div_eq_of_lt; omega
  have hm256 : (p * 32 + j) % 256 = p * 32 + j := Nat.mod_eq_of_lt hidx_lt
  have hd32 : (p * 32 + j) / 32 = p := by omega
  have hm32 : (p * 32 + j) % 32 = j := by omega
  rw [hm256, hd32, hm32]
  congr 1
  rw [hd256]
  ring

private lemma chunk1_4_of_ag1_1_2_32_p21 (xs : List Tensor) (r : Nat) (hr : r < 4)
    (hhead : (xs.head?.map (·.shape)).getD [] = [1, 2, 32])
    (hshapes : ∀ i, i < 4 →
      (xs.getD i (zeroTensor [1, 2, 32])).shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 xs) =
      xs.getD r (zeroTensor [1, 2, 32]) := by
  have hag_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hchunk_shape : (chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 xs)).shape =
      [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hag_shape (by omega)]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hchunk_shape, hshapes r hr]
  · intro idx hidx
    have hidx_lt : idx < 64 := by
      rw [hchunk_shape] at hidx; simp [prodShape] at hidx; omega
    set p := idx / 32 with hpdef
    set j := idx % 32 with hjdef
    have hpb : p < 2 := by simp [hpdef]; omega
    have hjb : j < 32 := by simp [hjdef]; omega
    have hidx_eq : idx = p * 32 + j := by simp [hpdef, hjdef]; omega
    rw [hidx_eq]
    rw [chunk_dim1_4_1_8_32_valAt _ r p j hag_shape hr hpb hjb]
    have hrp_lt : r * 2 + p < 8 := by
      have : r * 2 ≤ 3 * 2 := Nat.mul_le_mul_right 2 (by omega); omega
    rw [valAt_ag1_1_2_32_pj_p21 xs (r * 2 + p) j hhead hrp_lt hjb]
    have hd : (r * 2 + p) / 2 = r := by omega
    have hm : (r * 2 + p) % 2 = p := by omega
    rw [hd, hm]

private lemma chunk1_4_of_ag1_1_2_32_explicit_p21 (t0 t1 t2 t3 : Tensor) (r : Nat) (hr : r < 4)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) =
      ([t0, t1, t2, t3]).getD r (zeroTensor [1, 2, 32]) := by
  apply chunk1_4_of_ag1_1_2_32_p21 _ r hr
  · simp [h0]
  · intro i hi
    match i, hi with
    | 0, _ => simpa [List.getD] using h0
    | 1, _ => simpa [List.getD] using h1
    | 2, _ => simpa [List.getD] using h2
    | 3, _ => simpa [List.getD] using h3

private lemma chunk1_4_of_ag1_1_2_32_idx0_p21 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 0 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t0 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p21 t0 t1 t2 t3 0 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx1_p21 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 1 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t1 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p21 t0 t1 t2 t3 1 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx2_p21 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 2 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t2 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p21 t0 t1 t2 t3 2 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx3_p21 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 3 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t3 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p21 t0 t1 t2 t3 3 (by omega) h0 h1 h2 h3]; rfl

/-! ## Generic singleton lift for `FW_layernorm` + `AllGather dim=1` -/

private theorem layernorm_dim1_4_singleton_lift
    (initSM initPM : Store)
    (smOutTid smInTid wTid bTid agOutTid : Tid)
    (pmOut0 pmOut1 pmOut2 pmOut3 : Tid)
    (pmIn0 pmIn1 pmIn2 pmIn3 : Tid)
    (h_sm_eval : denoteGraph sm initSM smOutTid =
      fw_layernorm (denoteGraph sm initSM smInTid)
                   (denoteGraph sm initSM wTid)
                   (denoteGraph sm initSM bTid))
    (h_pm_ag : denoteGraph pm initPM agOutTid =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
         denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3])
    (h_pm0_eval : denoteGraph pm initPM pmOut0 =
      fw_layernorm (denoteGraph pm initPM pmIn0)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (h_pm1_eval : denoteGraph pm initPM pmOut1 =
      fw_layernorm (denoteGraph pm initPM pmIn1)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (h_pm2_eval : denoteGraph pm initPM pmOut2 =
      fw_layernorm (denoteGraph pm initPM pmIn2)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (h_pm3_eval : denoteGraph pm initPM pmOut3 =
      fw_layernorm (denoteGraph pm initPM pmIn3)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hW_sm_pm : denoteGraph sm initSM wTid = denoteGraph pm initPM wTid)
    (hB_sm_pm : denoteGraph sm initSM bTid = denoteGraph pm initPM bTid)
    (hxshape : (denoteGraph sm initSM smInTid).shape = [1, 8, 32])
    (hI0 : (denoteGraph pm initPM pmIn0).shape = [1, 2, 32])
    (hI1 : (denoteGraph pm initPM pmIn1).shape = [1, 2, 32])
    (hI2 : (denoteGraph pm initPM pmIn2).shape = [1, 2, 32])
    (hI3 : (denoteGraph pm initPM pmIn3).shape = [1, 2, 32])
    (h_input_gather : denoteGraph sm initSM smInTid =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM pmIn0, denoteGraph pm initPM pmIn1,
         denoteGraph pm initPM pmIn2, denoteGraph pm initPM pmIn3]) :
    (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] ∧
      ([(denoteGraph pm initPM agOutTid).shape] =
        ([[1, 8, 32]] : List Shape)) ∧
      denoteGraph sm initSM smOutTid =
        reconstructWithDim 0 pm.numRanks 0
          [denoteGraph pm initPM agOutTid] := by
  -- Piece output shapes (from PM evals + layernorm shape lemma).
  have hP0_shape : (denoteGraph pm initPM pmOut0).shape = [1, 2, 32] := by
    rw [h_pm0_eval]; exact fw_layernorm_shape_1_2_32 _ _ _ hI0
  have hP1_shape : (denoteGraph pm initPM pmOut1).shape = [1, 2, 32] := by
    rw [h_pm1_eval]; exact fw_layernorm_shape_1_2_32 _ _ _ hI1
  have hP2_shape : (denoteGraph pm initPM pmOut2).shape = [1, 2, 32] := by
    rw [h_pm2_eval]; exact fw_layernorm_shape_1_2_32 _ _ _ hI2
  have hP3_shape : (denoteGraph pm initPM pmOut3).shape = [1, 2, 32] := by
    rw [h_pm3_eval]; exact fw_layernorm_shape_1_2_32 _ _ _ hI3
  have hhead_pieces :
      (([denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
         denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3]
         : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hP0_shape]
  have hag_pieces_shape :
      (allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
         denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3]).shape =
      [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead_pieces]; simp [List.set, List.getD]
  have hagOut_shape : (denoteGraph pm initPM agOutTid).shape = [1, 8, 32] := by
    rw [h_pm_ag]; exact hag_pieces_shape
  -- SM output shape.
  have hSmOut_shape : (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] := by
    rw [h_sm_eval]; exact fw_layernorm_shape_1_8_32 _ _ _ hxshape
  refine ⟨hSmOut_shape, ?_, ?_⟩
  · simp [hagOut_shape]
  · rw [show pm.numRanks = pm.numRanks from rfl, reconstructWithDim_singleton]
    rw [h_pm_ag, h_sm_eval, h_input_gather]
    -- LHS: fw_layernorm (allGather [inputs]) w b
    -- Apply split.
    have hag_inputs_shape :
        (allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM pmIn0, denoteGraph pm initPM pmIn1,
           denoteGraph pm initPM pmIn2, denoteGraph pm initPM pmIn3]).shape =
        [1, 8, 32] := by
      have hh :
          (([denoteGraph pm initPM pmIn0, denoteGraph pm initPM pmIn1,
             denoteGraph pm initPM pmIn2, denoteGraph pm initPM pmIn3]
             : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
        simp [hI0]
      rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD]
    rw [fw_layernorm_split_dim1_4_1_8_32 _ (denoteGraph sm initSM wTid)
        (denoteGraph sm initSM bTid) hag_inputs_shape]
    -- Now both sides are `allGather [fw_layernorm (chunk r ag) w b]`.
    rw [chunk1_4_of_ag1_1_2_32_idx0_p21 _ _ _ _ hI0 hI1 hI2 hI3,
        chunk1_4_of_ag1_1_2_32_idx1_p21 _ _ _ _ hI0 hI1 hI2 hI3,
        chunk1_4_of_ag1_1_2_32_idx2_p21 _ _ _ _ hI0 hI1 hI2 hI3,
        chunk1_4_of_ag1_1_2_32_idx3_p21 _ _ _ _ hI0 hI1 hI2 hI3]
    rw [hW_sm_pm, hB_sm_pm]
    rw [← h_pm0_eval, ← h_pm1_eval, ← h_pm2_eval, ← h_pm3_eval]

/-! ## Per-goal NodeDecls and eval lemmas -/

@[reducible] private def n_sm_p21_25 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [934, 594, 595], outs := [596] }
@[reducible] private def n_pm_p21_25_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [1525, 594, 595], outs := [1529] }
@[reducible] private def n_pm_p21_25_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [1526, 594, 595], outs := [1530] }
@[reducible] private def n_pm_p21_25_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [1527, 594, 595], outs := [1531] }
@[reducible] private def n_pm_p21_25_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [1528, 594, 595], outs := [1532] }
@[reducible] private def n_pm_p21_25_ag : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := ((List.range 4).map (fun r => 1529 + r)), outs := [596], params := [1] }

@[reducible] private def n_sm_p21_50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [977, 629, 630], outs := [631] }
@[reducible] private def n_pm_p21_50_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [2081, 629, 630], outs := [2085] }
@[reducible] private def n_pm_p21_50_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [2082, 629, 630], outs := [2086] }
@[reducible] private def n_pm_p21_50_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [2083, 629, 630], outs := [2087] }
@[reducible] private def n_pm_p21_50_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [2084, 629, 630], outs := [2088] }
@[reducible] private def n_pm_p21_50_ag : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := ((List.range 4).map (fun r => 2085 + r)), outs := [631], params := [1] }

@[reducible] private def n_sm_p21_105 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [707, 708, 709], outs := [710] }
@[reducible] private def n_pm_p21_105_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [3321, 708, 709], outs := [3345] }
@[reducible] private def n_pm_p21_105_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [3322, 708, 709], outs := [3346] }
@[reducible] private def n_pm_p21_105_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [3323, 708, 709], outs := [3347] }
@[reducible] private def n_pm_p21_105_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [3324, 708, 709], outs := [3348] }
@[reducible] private def n_pm_p21_105_ag : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := ((List.range 4).map (fun r => 3345 + r)), outs := [710], params := [1] }

set_option maxHeartbeats 4000000 in
private theorem sm_eval_596 (initSM : Store) :
    denoteGraph sm initSM 596 = fw_layernorm (denoteGraph sm initSM 934) (denoteGraph sm initSM 594) (denoteGraph sm initSM 595) := by
  have hsub : (denoteGraph sm initSM) 596 =
      (denoteGraph { sm with nodes := sm.nodes.take 27 } initSM) 596 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 596
      (sm.nodes.take 27) (sm.nodes.drop 27)
      (List.take_append_drop 27 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 27 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 26 ++ [n_sm_p21_25] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_p21_25] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_p21_25 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_p21_25 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_p21_25 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [934, 594, 595], outs := [596], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 26 } initSM 934 = denoteGraph sm initSM 934 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 934
      (sm.nodes.take 26) (sm.nodes.drop 26)
      (List.take_append_drop 26 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 26 } initSM 594 = denoteGraph sm initSM 594 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 594
      (sm.nodes.take 26) (sm.nodes.drop 26)
      (List.take_append_drop 26 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 26 } initSM 595 = denoteGraph sm initSM 595 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 595
      (sm.nodes.take 26) (sm.nodes.drop 26)
      (List.take_append_drop 26 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem sm_eval_631 (initSM : Store) :
    denoteGraph sm initSM 631 = fw_layernorm (denoteGraph sm initSM 977) (denoteGraph sm initSM 629) (denoteGraph sm initSM 630) := by
  have hsub : (denoteGraph sm initSM) 631 =
      (denoteGraph { sm with nodes := sm.nodes.take 55 } initSM) 631 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 631
      (sm.nodes.take 55) (sm.nodes.drop 55)
      (List.take_append_drop 55 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 55 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 54 ++ [n_sm_p21_50] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_p21_50] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_p21_50 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_p21_50 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_p21_50 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [977, 629, 630], outs := [631], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 54 } initSM 977 = denoteGraph sm initSM 977 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 977
      (sm.nodes.take 54) (sm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 54 } initSM 629 = denoteGraph sm initSM 629 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 629
      (sm.nodes.take 54) (sm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 54 } initSM 630 = denoteGraph sm initSM 630 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 630
      (sm.nodes.take 54) (sm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem sm_eval_710 (initSM : Store) :
    denoteGraph sm initSM 710 = fw_layernorm (denoteGraph sm initSM 707) (denoteGraph sm initSM 708) (denoteGraph sm initSM 709) := by
  have hsub : (denoteGraph sm initSM) 710 =
      (denoteGraph { sm with nodes := sm.nodes.take 116 } initSM) 710 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 710
      (sm.nodes.take 116) (sm.nodes.drop 116)
      (List.take_append_drop 116 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 116 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 115 ++ [n_sm_p21_105] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_p21_105] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_p21_105 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_p21_105 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_p21_105 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [707, 708, 709], outs := [710], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 115 } initSM 707 = denoteGraph sm initSM 707 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 707
      (sm.nodes.take 115) (sm.nodes.drop 115)
      (List.take_append_drop 115 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 115 } initSM 708 = denoteGraph sm initSM 708 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 708
      (sm.nodes.take 115) (sm.nodes.drop 115)
      (List.take_append_drop 115 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 115 } initSM 709 = denoteGraph sm initSM 709 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 709
      (sm.nodes.take 115) (sm.nodes.drop 115)
      (List.take_append_drop 115 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_1529 (initPM : Store) :
    denoteGraph pm initPM 1529 = fw_layernorm (denoteGraph pm initPM 1525) (denoteGraph pm initPM 594) (denoteGraph pm initPM 595) := by
  have hsub : (denoteGraph pm initPM) 1529 =
      (denoteGraph { pm with nodes := pm.nodes.take 161 } initPM) 1529 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1529
      (pm.nodes.take 161) (pm.nodes.drop 161)
      (List.take_append_drop 161 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 161 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 160 ++ [n_pm_p21_25_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_25_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_25_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_25_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_25_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [1525, 594, 595], outs := [1529], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 160 } initPM 1525 = denoteGraph pm initPM 1525 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1525
      (pm.nodes.take 160) (pm.nodes.drop 160)
      (List.take_append_drop 160 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 160 } initPM 594 = denoteGraph pm initPM 594 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 594
      (pm.nodes.take 160) (pm.nodes.drop 160)
      (List.take_append_drop 160 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 160 } initPM 595 = denoteGraph pm initPM 595 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 595
      (pm.nodes.take 160) (pm.nodes.drop 160)
      (List.take_append_drop 160 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_1530 (initPM : Store) :
    denoteGraph pm initPM 1530 = fw_layernorm (denoteGraph pm initPM 1526) (denoteGraph pm initPM 594) (denoteGraph pm initPM 595) := by
  have hsub : (denoteGraph pm initPM) 1530 =
      (denoteGraph { pm with nodes := pm.nodes.take 162 } initPM) 1530 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1530
      (pm.nodes.take 162) (pm.nodes.drop 162)
      (List.take_append_drop 162 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 162 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 161 ++ [n_pm_p21_25_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_25_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_25_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_25_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_25_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [1526, 594, 595], outs := [1530], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 161 } initPM 1526 = denoteGraph pm initPM 1526 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1526
      (pm.nodes.take 161) (pm.nodes.drop 161)
      (List.take_append_drop 161 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 161 } initPM 594 = denoteGraph pm initPM 594 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 594
      (pm.nodes.take 161) (pm.nodes.drop 161)
      (List.take_append_drop 161 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 161 } initPM 595 = denoteGraph pm initPM 595 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 595
      (pm.nodes.take 161) (pm.nodes.drop 161)
      (List.take_append_drop 161 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_1531 (initPM : Store) :
    denoteGraph pm initPM 1531 = fw_layernorm (denoteGraph pm initPM 1527) (denoteGraph pm initPM 594) (denoteGraph pm initPM 595) := by
  have hsub : (denoteGraph pm initPM) 1531 =
      (denoteGraph { pm with nodes := pm.nodes.take 163 } initPM) 1531 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1531
      (pm.nodes.take 163) (pm.nodes.drop 163)
      (List.take_append_drop 163 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 163 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 162 ++ [n_pm_p21_25_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_25_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_25_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_25_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_25_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [1527, 594, 595], outs := [1531], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 162 } initPM 1527 = denoteGraph pm initPM 1527 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1527
      (pm.nodes.take 162) (pm.nodes.drop 162)
      (List.take_append_drop 162 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 162 } initPM 594 = denoteGraph pm initPM 594 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 594
      (pm.nodes.take 162) (pm.nodes.drop 162)
      (List.take_append_drop 162 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 162 } initPM 595 = denoteGraph pm initPM 595 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 595
      (pm.nodes.take 162) (pm.nodes.drop 162)
      (List.take_append_drop 162 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_1532 (initPM : Store) :
    denoteGraph pm initPM 1532 = fw_layernorm (denoteGraph pm initPM 1528) (denoteGraph pm initPM 594) (denoteGraph pm initPM 595) := by
  have hsub : (denoteGraph pm initPM) 1532 =
      (denoteGraph { pm with nodes := pm.nodes.take 164 } initPM) 1532 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1532
      (pm.nodes.take 164) (pm.nodes.drop 164)
      (List.take_append_drop 164 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 164 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 163 ++ [n_pm_p21_25_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_25_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_25_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_25_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_25_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [1528, 594, 595], outs := [1532], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 163 } initPM 1528 = denoteGraph pm initPM 1528 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1528
      (pm.nodes.take 163) (pm.nodes.drop 163)
      (List.take_append_drop 163 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 163 } initPM 594 = denoteGraph pm initPM 594 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 594
      (pm.nodes.take 163) (pm.nodes.drop 163)
      (List.take_append_drop 163 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 163 } initPM 595 = denoteGraph pm initPM 595 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 595
      (pm.nodes.take 163) (pm.nodes.drop 163)
      (List.take_append_drop 163 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_2085 (initPM : Store) :
    denoteGraph pm initPM 2085 = fw_layernorm (denoteGraph pm initPM 2081) (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  have hsub : (denoteGraph pm initPM) 2085 =
      (denoteGraph { pm with nodes := pm.nodes.take 359 } initPM) 2085 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2085
      (pm.nodes.take 359) (pm.nodes.drop 359)
      (List.take_append_drop 359 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 359 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 358 ++ [n_pm_p21_50_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_50_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_50_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_50_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_50_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [2081, 629, 630], outs := [2085], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 358 } initPM 2081 = denoteGraph pm initPM 2081 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2081
      (pm.nodes.take 358) (pm.nodes.drop 358)
      (List.take_append_drop 358 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 358 } initPM 629 = denoteGraph pm initPM 629 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 629
      (pm.nodes.take 358) (pm.nodes.drop 358)
      (List.take_append_drop 358 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 358 } initPM 630 = denoteGraph pm initPM 630 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 630
      (pm.nodes.take 358) (pm.nodes.drop 358)
      (List.take_append_drop 358 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_2086 (initPM : Store) :
    denoteGraph pm initPM 2086 = fw_layernorm (denoteGraph pm initPM 2082) (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  have hsub : (denoteGraph pm initPM) 2086 =
      (denoteGraph { pm with nodes := pm.nodes.take 360 } initPM) 2086 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2086
      (pm.nodes.take 360) (pm.nodes.drop 360)
      (List.take_append_drop 360 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 360 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 359 ++ [n_pm_p21_50_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_50_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_50_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_50_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_50_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [2082, 629, 630], outs := [2086], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 359 } initPM 2082 = denoteGraph pm initPM 2082 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2082
      (pm.nodes.take 359) (pm.nodes.drop 359)
      (List.take_append_drop 359 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 359 } initPM 629 = denoteGraph pm initPM 629 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 629
      (pm.nodes.take 359) (pm.nodes.drop 359)
      (List.take_append_drop 359 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 359 } initPM 630 = denoteGraph pm initPM 630 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 630
      (pm.nodes.take 359) (pm.nodes.drop 359)
      (List.take_append_drop 359 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_2087 (initPM : Store) :
    denoteGraph pm initPM 2087 = fw_layernorm (denoteGraph pm initPM 2083) (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  have hsub : (denoteGraph pm initPM) 2087 =
      (denoteGraph { pm with nodes := pm.nodes.take 361 } initPM) 2087 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2087
      (pm.nodes.take 361) (pm.nodes.drop 361)
      (List.take_append_drop 361 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 361 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 360 ++ [n_pm_p21_50_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_50_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_50_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_50_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_50_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [2083, 629, 630], outs := [2087], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 360 } initPM 2083 = denoteGraph pm initPM 2083 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2083
      (pm.nodes.take 360) (pm.nodes.drop 360)
      (List.take_append_drop 360 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 360 } initPM 629 = denoteGraph pm initPM 629 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 629
      (pm.nodes.take 360) (pm.nodes.drop 360)
      (List.take_append_drop 360 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 360 } initPM 630 = denoteGraph pm initPM 630 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 630
      (pm.nodes.take 360) (pm.nodes.drop 360)
      (List.take_append_drop 360 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_2088 (initPM : Store) :
    denoteGraph pm initPM 2088 = fw_layernorm (denoteGraph pm initPM 2084) (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  have hsub : (denoteGraph pm initPM) 2088 =
      (denoteGraph { pm with nodes := pm.nodes.take 362 } initPM) 2088 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2088
      (pm.nodes.take 362) (pm.nodes.drop 362)
      (List.take_append_drop 362 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 362 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 361 ++ [n_pm_p21_50_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_50_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_50_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_50_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_50_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [2084, 629, 630], outs := [2088], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 361 } initPM 2084 = denoteGraph pm initPM 2084 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2084
      (pm.nodes.take 361) (pm.nodes.drop 361)
      (List.take_append_drop 361 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 361 } initPM 629 = denoteGraph pm initPM 629 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 629
      (pm.nodes.take 361) (pm.nodes.drop 361)
      (List.take_append_drop 361 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 361 } initPM 630 = denoteGraph pm initPM 630 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 630
      (pm.nodes.take 361) (pm.nodes.drop 361)
      (List.take_append_drop 361 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3345 (initPM : Store) :
    denoteGraph pm initPM 3345 = fw_layernorm (denoteGraph pm initPM 3321) (denoteGraph pm initPM 708) (denoteGraph pm initPM 709) := by
  have hsub : (denoteGraph pm initPM) 3345 =
      (denoteGraph { pm with nodes := pm.nodes.take 763 } initPM) 3345 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3345
      (pm.nodes.take 763) (pm.nodes.drop 763)
      (List.take_append_drop 763 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 763 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 762 ++ [n_pm_p21_105_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_105_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_105_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_105_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_105_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [3321, 708, 709], outs := [3345], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 762 } initPM 3321 = denoteGraph pm initPM 3321 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3321
      (pm.nodes.take 762) (pm.nodes.drop 762)
      (List.take_append_drop 762 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 762 } initPM 708 = denoteGraph pm initPM 708 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 708
      (pm.nodes.take 762) (pm.nodes.drop 762)
      (List.take_append_drop 762 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 762 } initPM 709 = denoteGraph pm initPM 709 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 709
      (pm.nodes.take 762) (pm.nodes.drop 762)
      (List.take_append_drop 762 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3346 (initPM : Store) :
    denoteGraph pm initPM 3346 = fw_layernorm (denoteGraph pm initPM 3322) (denoteGraph pm initPM 708) (denoteGraph pm initPM 709) := by
  have hsub : (denoteGraph pm initPM) 3346 =
      (denoteGraph { pm with nodes := pm.nodes.take 764 } initPM) 3346 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3346
      (pm.nodes.take 764) (pm.nodes.drop 764)
      (List.take_append_drop 764 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 764 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 763 ++ [n_pm_p21_105_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_105_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_105_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_105_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_105_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [3322, 708, 709], outs := [3346], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 763 } initPM 3322 = denoteGraph pm initPM 3322 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3322
      (pm.nodes.take 763) (pm.nodes.drop 763)
      (List.take_append_drop 763 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 763 } initPM 708 = denoteGraph pm initPM 708 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 708
      (pm.nodes.take 763) (pm.nodes.drop 763)
      (List.take_append_drop 763 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 763 } initPM 709 = denoteGraph pm initPM 709 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 709
      (pm.nodes.take 763) (pm.nodes.drop 763)
      (List.take_append_drop 763 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3347 (initPM : Store) :
    denoteGraph pm initPM 3347 = fw_layernorm (denoteGraph pm initPM 3323) (denoteGraph pm initPM 708) (denoteGraph pm initPM 709) := by
  have hsub : (denoteGraph pm initPM) 3347 =
      (denoteGraph { pm with nodes := pm.nodes.take 765 } initPM) 3347 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3347
      (pm.nodes.take 765) (pm.nodes.drop 765)
      (List.take_append_drop 765 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 765 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 764 ++ [n_pm_p21_105_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_105_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_105_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_105_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_105_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [3323, 708, 709], outs := [3347], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 764 } initPM 3323 = denoteGraph pm initPM 3323 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3323
      (pm.nodes.take 764) (pm.nodes.drop 764)
      (List.take_append_drop 764 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 764 } initPM 708 = denoteGraph pm initPM 708 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 708
      (pm.nodes.take 764) (pm.nodes.drop 764)
      (List.take_append_drop 764 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 764 } initPM 709 = denoteGraph pm initPM 709 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 709
      (pm.nodes.take 764) (pm.nodes.drop 764)
      (List.take_append_drop 764 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3348 (initPM : Store) :
    denoteGraph pm initPM 3348 = fw_layernorm (denoteGraph pm initPM 3324) (denoteGraph pm initPM 708) (denoteGraph pm initPM 709) := by
  have hsub : (denoteGraph pm initPM) 3348 =
      (denoteGraph { pm with nodes := pm.nodes.take 766 } initPM) 3348 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3348
      (pm.nodes.take 766) (pm.nodes.drop 766)
      (List.take_append_drop 766 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 766 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 765 ++ [n_pm_p21_105_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_105_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_105_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_105_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p21_105_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [3324, 708, 709], outs := [3348], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 765 } initPM 3324 = denoteGraph pm initPM 3324 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3324
      (pm.nodes.take 765) (pm.nodes.drop 765)
      (List.take_append_drop 765 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 765 } initPM 708 = denoteGraph pm initPM 708 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 708
      (pm.nodes.take 765) (pm.nodes.drop 765)
      (List.take_append_drop 765 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 765 } initPM 709 = denoteGraph pm initPM 709 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 709
      (pm.nodes.take 765) (pm.nodes.drop 765)
      (List.take_append_drop 765 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]

set_option maxHeartbeats 4000000 in
private theorem pm_eval_ag_596 (initPM : Store) :
    denoteGraph pm initPM 596 =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1529, denoteGraph pm initPM 1530,
         denoteGraph pm initPM 1531, denoteGraph pm initPM 1532] := by
  have hsub : (denoteGraph pm initPM) 596 =
      (denoteGraph { pm with nodes := pm.nodes.take 165 } initPM) 596 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 596
      (pm.nodes.take 165) (pm.nodes.drop 165)
      (List.take_append_drop 165 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 165 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 164 ++ [n_pm_p21_25_ag] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_25_ag] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_25_ag :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_25_ag []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  rw [show ((List.range 4).map (fun r => 1529 + r)) = [1529, 1530, 1531, 1532] from rfl]
  simp only [List.map_cons, List.map_nil]
  have h1529 : (denoteGraph { pm with nodes := pm.nodes.take 164 } initPM) 1529 =
      (denoteGraph pm initPM) 1529 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1529
      (pm.nodes.take 164) (pm.nodes.drop 164)
      (List.take_append_drop 164 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1530 : (denoteGraph { pm with nodes := pm.nodes.take 164 } initPM) 1530 =
      (denoteGraph pm initPM) 1530 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1530
      (pm.nodes.take 164) (pm.nodes.drop 164)
      (List.take_append_drop 164 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1531 : (denoteGraph { pm with nodes := pm.nodes.take 164 } initPM) 1531 =
      (denoteGraph pm initPM) 1531 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1531
      (pm.nodes.take 164) (pm.nodes.drop 164)
      (List.take_append_drop 164 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1532 : (denoteGraph { pm with nodes := pm.nodes.take 164 } initPM) 1532 =
      (denoteGraph pm initPM) 1532 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1532
      (pm.nodes.take 164) (pm.nodes.drop 164)
      (List.take_append_drop 164 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h1529, h1530, h1531, h1532]
  rfl

set_option maxHeartbeats 4000000 in
private theorem pm_eval_ag_631 (initPM : Store) :
    denoteGraph pm initPM 631 =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2085, denoteGraph pm initPM 2086,
         denoteGraph pm initPM 2087, denoteGraph pm initPM 2088] := by
  have hsub : (denoteGraph pm initPM) 631 =
      (denoteGraph { pm with nodes := pm.nodes.take 363 } initPM) 631 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 631
      (pm.nodes.take 363) (pm.nodes.drop 363)
      (List.take_append_drop 363 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 363 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 362 ++ [n_pm_p21_50_ag] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_50_ag] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_50_ag :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_50_ag []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  rw [show ((List.range 4).map (fun r => 2085 + r)) = [2085, 2086, 2087, 2088] from rfl]
  simp only [List.map_cons, List.map_nil]
  have h2085 : (denoteGraph { pm with nodes := pm.nodes.take 362 } initPM) 2085 =
      (denoteGraph pm initPM) 2085 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2085
      (pm.nodes.take 362) (pm.nodes.drop 362)
      (List.take_append_drop 362 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2086 : (denoteGraph { pm with nodes := pm.nodes.take 362 } initPM) 2086 =
      (denoteGraph pm initPM) 2086 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2086
      (pm.nodes.take 362) (pm.nodes.drop 362)
      (List.take_append_drop 362 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2087 : (denoteGraph { pm with nodes := pm.nodes.take 362 } initPM) 2087 =
      (denoteGraph pm initPM) 2087 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2087
      (pm.nodes.take 362) (pm.nodes.drop 362)
      (List.take_append_drop 362 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2088 : (denoteGraph { pm with nodes := pm.nodes.take 362 } initPM) 2088 =
      (denoteGraph pm initPM) 2088 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2088
      (pm.nodes.take 362) (pm.nodes.drop 362)
      (List.take_append_drop 362 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h2085, h2086, h2087, h2088]
  rfl

set_option maxHeartbeats 4000000 in
private theorem pm_eval_ag_710 (initPM : Store) :
    denoteGraph pm initPM 710 =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 3345, denoteGraph pm initPM 3346,
         denoteGraph pm initPM 3347, denoteGraph pm initPM 3348] := by
  have hsub : (denoteGraph pm initPM) 710 =
      (denoteGraph { pm with nodes := pm.nodes.take 767 } initPM) 710 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 710
      (pm.nodes.take 767) (pm.nodes.drop 767)
      (List.take_append_drop 767 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 767 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 766 ++ [n_pm_p21_105_ag] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p21_105_ag] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p21_105_ag :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p21_105_ag []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  rw [show ((List.range 4).map (fun r => 3345 + r)) = [3345, 3346, 3347, 3348] from rfl]
  simp only [List.map_cons, List.map_nil]
  have h3345 : (denoteGraph { pm with nodes := pm.nodes.take 766 } initPM) 3345 =
      (denoteGraph pm initPM) 3345 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3345
      (pm.nodes.take 766) (pm.nodes.drop 766)
      (List.take_append_drop 766 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h3346 : (denoteGraph { pm with nodes := pm.nodes.take 766 } initPM) 3346 =
      (denoteGraph pm initPM) 3346 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3346
      (pm.nodes.take 766) (pm.nodes.drop 766)
      (List.take_append_drop 766 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h3347 : (denoteGraph { pm with nodes := pm.nodes.take 766 } initPM) 3347 =
      (denoteGraph pm initPM) 3347 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3347
      (pm.nodes.take 766) (pm.nodes.drop 766)
      (List.take_append_drop 766 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h3348 : (denoteGraph { pm with nodes := pm.nodes.take 766 } initPM) 3348 =
      (denoteGraph pm initPM) 3348 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3348
      (pm.nodes.take 766) (pm.nodes.drop 766)
      (List.take_append_drop 766 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h3345, h3346, h3347, h3348]
  rfl

set_option maxHeartbeats 8000000 in
theorem prove_pattern_21 : pattern_21_stmt := by
  intro target ht
  cases ht with
  | goal_25 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_267_stmt :=
      prove_pattern_127 pattern_127_target.goal_267
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 1525).shape, (denoteGraph pm initPM 1526).shape,
         (denoteGraph pm initPM 1527).shape, (denoteGraph pm initPM 1528).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_267, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 1525).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1526).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1527).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1528).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 1525).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 1526).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 1527).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 1528).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 934).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_267] using hs
    have h_input_gather : denoteGraph sm initSM 934 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1525, denoteGraph pm initPM 1526,
         denoteGraph pm initPM 1527, denoteGraph pm initPM 1528] := by
      have hh := h_eq_rec
      simp only [goal_267, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_594 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_595 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 594 = initPM 594 := by
      have hh := h_init_W.2.2
      simpa [initGoal_594, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 595 = initPM 595 := by
      have hh := h_init_B.2.2
      simpa [initGoal_595, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 594 = initSM 594 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 594
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 595 = initSM 595 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 595
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 594 = initPM 594 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 594
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 595 = initPM 595 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 595
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 594 = denoteGraph pm initPM 594 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 595 = denoteGraph pm initPM 595 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_singleton_lift initSM initPM
      596 934 594 595 596
      1529 1530 1531 1532
      1525 1526 1527 1528
      (sm_eval_596 initSM)
      (pm_eval_ag_596 initPM)
      (pm_eval_1529 initPM) (pm_eval_1530 initPM)
      (pm_eval_1531 initPM) (pm_eval_1532 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      h_input_gather
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    show (denoteGraph sm initSM 596).shape = goal_25.tsShape ∧
      _ = goal_25.tpShapes ∧
      denoteGraph sm initSM 596 =
        reconstructWithDim goal_25.gatherDim pm.numRanks 0
          (goal_25.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_25] using hs1
    · simpa [goal_25, List.map_cons, List.map_nil] using hs2
    · simpa [goal_25, List.map_cons, List.map_nil] using hs3
  | goal_50 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_281_stmt :=
      prove_pattern_127 pattern_127_target.goal_281
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 2081).shape, (denoteGraph pm initPM 2082).shape,
         (denoteGraph pm initPM 2083).shape, (denoteGraph pm initPM 2084).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_281, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2081).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2082).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2083).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2084).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 2081).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 2082).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 2083).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 2084).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 977).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_281] using hs
    have h_input_gather : denoteGraph sm initSM 977 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2081, denoteGraph pm initPM 2082,
         denoteGraph pm initPM 2083, denoteGraph pm initPM 2084] := by
      have hh := h_eq_rec
      simp only [goal_281, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_629 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_630 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 629 = initPM 629 := by
      have hh := h_init_W.2.2
      simpa [initGoal_629, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 630 = initPM 630 := by
      have hh := h_init_B.2.2
      simpa [initGoal_630, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 629 = initSM 629 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 629
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 630 = initSM 630 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 630
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 629 = initPM 629 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 629
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 630 = initPM 630 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 630
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 629 = denoteGraph pm initPM 629 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 630 = denoteGraph pm initPM 630 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_singleton_lift initSM initPM
      631 977 629 630 631
      2085 2086 2087 2088
      2081 2082 2083 2084
      (sm_eval_631 initSM)
      (pm_eval_ag_631 initPM)
      (pm_eval_2085 initPM) (pm_eval_2086 initPM)
      (pm_eval_2087 initPM) (pm_eval_2088 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      h_input_gather
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    show (denoteGraph sm initSM 631).shape = goal_50.tsShape ∧
      _ = goal_50.tpShapes ∧
      denoteGraph sm initSM 631 =
        reconstructWithDim goal_50.gatherDim pm.numRanks 0
          (goal_50.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_50] using hs1
    · simpa [goal_50, List.map_cons, List.map_nil] using hs2
    · simpa [goal_50, List.map_cons, List.map_nil] using hs3
  | goal_105 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_104_stmt :=
      prove_pattern_44 pattern_44_target.goal_104
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 3321).shape, (denoteGraph pm initPM 3322).shape,
         (denoteGraph pm initPM 3323).shape, (denoteGraph pm initPM 3324).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_104, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 3321).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3322).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3323).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3324).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 3321).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 3322).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 3323).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 3324).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 707).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_104] using hs
    have h_input_gather : denoteGraph sm initSM 707 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 3321, denoteGraph pm initPM 3322,
         denoteGraph pm initPM 3323, denoteGraph pm initPM 3324] := by
      have hh := h_eq_rec
      simp only [goal_104, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_708 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_709 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 708 = initPM 708 := by
      have hh := h_init_W.2.2
      simpa [initGoal_708, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 709 = initPM 709 := by
      have hh := h_init_B.2.2
      simpa [initGoal_709, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 708 = initSM 708 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 708
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 709 = initSM 709 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 709
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 708 = initPM 708 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 708
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 709 = initPM 709 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 709
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 708 = denoteGraph pm initPM 708 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 709 = denoteGraph pm initPM 709 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_singleton_lift initSM initPM
      710 707 708 709 710
      3345 3346 3347 3348
      3321 3322 3323 3324
      (sm_eval_710 initSM)
      (pm_eval_ag_710 initPM)
      (pm_eval_3345 initPM) (pm_eval_3346 initPM)
      (pm_eval_3347 initPM) (pm_eval_3348 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      h_input_gather
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    show (denoteGraph sm initSM 710).shape = goal_105.tsShape ∧
      _ = goal_105.tpShapes ∧
      denoteGraph sm initSM 710 =
        reconstructWithDim goal_105.gatherDim pm.numRanks 0
          (goal_105.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_105] using hs1
    · simpa [goal_105, List.map_cons, List.map_nil] using hs2
    · simpa [goal_105, List.map_cons, List.map_nil] using hs3

end TrainVerify.Denote.GeneratedPatterns
