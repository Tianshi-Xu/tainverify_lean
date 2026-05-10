/- Auto-generated pattern proof file.
   Pattern: 5
   Hash: de5f5f99bf861ead
   Goals: 5, 30, 55, 75, 80, 100

   Structural pattern: every goal lifts a single-rank `FW_layernorm` over input
   shape `[1, 8, 32]` with weight/bias of shape `[32]` to four parallel
   `FW_layernorm`s over chunks of shape `[1, 2, 32]`, gathered along dim=1.

   The structural argument is identical for every goal; only the concrete tensor
   ids and the corresponding input-lineage prerequisite differ.  We factor the
   structural part into a single private lemma `layernorm_dim1_4_lift`
   parameterised over the relevant tids, and instantiate it once per goal with
   the right per-goal `*_eval` lemmas plus the input lineage (which is supplied
   by the prerequisite pattern proof).
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_127
import denote.gpt_ly4_segments.Pattern_128

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_5_goalIds : List Nat := [5, 30, 55, 75, 80, 100]
inductive pattern_5_target : Prop → Prop
  | goal_5   : pattern_5_target goal_5_stmt
  | goal_30  : pattern_5_target goal_30_stmt
  | goal_55  : pattern_5_target goal_55_stmt
  | goal_75  : pattern_5_target goal_75_stmt
  | goal_80  : pattern_5_target goal_80_stmt
  | goal_100 : pattern_5_target goal_100_stmt

def pattern_5_stmt : Prop :=
  ∀ {target : Prop}, pattern_5_target target → target

set_option maxRecDepth 32768

/-! ## Generic structural lemma -/

private theorem layernorm_dim1_4_lift
    (initSM initPM : Store)
    (smOutTid smInTid wTid bTid : Tid)
    (pmOut0 pmOut1 pmOut2 pmOut3 : Tid)
    (pmIn0 pmIn1 pmIn2 pmIn3 : Tid)
    (hsm_eval : denoteGraph sm initSM smOutTid =
      fw_layernorm (denoteGraph sm initSM smInTid)
                   (denoteGraph sm initSM wTid)
                   (denoteGraph sm initSM bTid))
    (hpm0_eval : denoteGraph pm initPM pmOut0 =
      fw_layernorm (denoteGraph pm initPM pmIn0)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hpm1_eval : denoteGraph pm initPM pmOut1 =
      fw_layernorm (denoteGraph pm initPM pmIn1)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hpm2_eval : denoteGraph pm initPM pmOut2 =
      fw_layernorm (denoteGraph pm initPM pmIn2)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hpm3_eval : denoteGraph pm initPM pmOut3 =
      fw_layernorm (denoteGraph pm initPM pmIn3)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hw_sm_pm : denoteGraph sm initSM wTid = denoteGraph pm initPM wTid)
    (hb_sm_pm : denoteGraph sm initSM bTid = denoteGraph pm initPM bTid)
    (hxshape : (denoteGraph sm initSM smInTid).shape = [1, 8, 32])
    (hxshape_pm0 : (denoteGraph pm initPM pmIn0).shape = [1, 2, 32])
    (hxshape_pm1 : (denoteGraph pm initPM pmIn1).shape = [1, 2, 32])
    (hxshape_pm2 : (denoteGraph pm initPM pmIn2).shape = [1, 2, 32])
    (hxshape_pm3 : (denoteGraph pm initPM pmIn3).shape = [1, 2, 32])
    (hinput_chunk0 : denoteGraph pm initPM pmIn0 =
      chunkPrimDimN 1 4 0 (denoteGraph sm initSM smInTid))
    (hinput_chunk1 : denoteGraph pm initPM pmIn1 =
      chunkPrimDimN 1 4 1 (denoteGraph sm initSM smInTid))
    (hinput_chunk2 : denoteGraph pm initPM pmIn2 =
      chunkPrimDimN 1 4 2 (denoteGraph sm initSM smInTid))
    (hinput_chunk3 : denoteGraph pm initPM pmIn3 =
      chunkPrimDimN 1 4 3 (denoteGraph sm initSM smInTid)) :
    (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] ∧
      ([(denoteGraph pm initPM pmOut0).shape,
        (denoteGraph pm initPM pmOut1).shape,
        (denoteGraph pm initPM pmOut2).shape,
        (denoteGraph pm initPM pmOut3).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]) ∧
      denoteGraph sm initSM smOutTid =
        allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
           denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm_eval]
    exact fw_layernorm_shape_1_8_32 _ _ _ hxshape
  · rw [hpm0_eval, hpm1_eval, hpm2_eval, hpm3_eval]
    have h0 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn0)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm0
    have h1 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn1)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm1
    have h2 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn2)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm2
    have h3 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn3)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm3
    rw [h0, h1, h2, h3]
  · rw [hsm_eval, hpm0_eval, hpm1_eval, hpm2_eval, hpm3_eval]
    rw [hinput_chunk0, hinput_chunk1, hinput_chunk2, hinput_chunk3]
    rw [← hw_sm_pm, ← hb_sm_pm]
    exact fw_layernorm_split_dim1_4_1_8_32 _ _ _ hxshape

/-! ## Chunk-of-allGather inverse for shape `[1, 2, 32]`

The structural lift requires us to convert the prerequisite
`denoteGraph sm initSM smInTid = allGatherPrimDimN 1 4 0 [pmIn0, ..., pmIn3]`
into per-piece chunk equations
`denoteGraph pm initPM pmIn_i = chunkPrimDimN 1 4 i (denoteGraph sm initSM smInTid)`.

We first establish the operator-level identity:
  `chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t_r`
when each `t_i` has shape `[1, 2, 32]`.
-/

private lemma valAt_ag1_1_2_32_pj (xs : List Tensor) (p j : Nat)
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
  -- Index: idx = p*32 + j where 0 ≤ idx < 256
  -- preIdx = idx / 256 = 0; remainder = idx; jFull = idx/32 = p; k = idx%32 = j
  -- r = jFull / 2 = p/2; jLocal = jFull % 2 = p%2
  have hd256 : (p * 32 + j) / 256 = 0 := by
    apply Nat.div_eq_of_lt; omega
  have hm256 : (p * 32 + j) % 256 = p * 32 + j := Nat.mod_eq_of_lt hidx_lt
  have hd32 : (p * 32 + j) / 32 = p := by omega
  have hm32 : (p * 32 + j) % 32 = j := by omega
  rw [hm256, hd32, hm32]
  congr 1
  rw [hd256]
  ring

private lemma chunk1_4_of_ag1_1_2_32 (xs : List Tensor) (r : Nat) (hr : r < 4)
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
    -- Decompose idx = p*32 + j with p<2, j<32.
    set p := idx / 32 with hpdef
    set j := idx % 32 with hjdef
    have hpb : p < 2 := by simp [hpdef]; omega
    have hjb : j < 32 := by simp [hjdef]; omega
    have hidx_eq : idx = p * 32 + j := by simp [hpdef, hjdef]; omega
    rw [hidx_eq]
    rw [chunk_dim1_4_1_8_32_valAt _ r p j hag_shape hr hpb hjb]
    -- Need: valAt (allGather xs) ((r*2+p)*32+j) = valAt xs[r] (p*32+j)
    have hrp_lt : r * 2 + p < 8 := by
      have : r * 2 ≤ 3 * 2 := Nat.mul_le_mul_right 2 (by omega); omega
    rw [valAt_ag1_1_2_32_pj xs (r * 2 + p) j hhead hrp_lt hjb]
    -- (r*2+p)/2 = r and (r*2+p)%2 = p
    have hd : (r * 2 + p) / 2 = r := by omega
    have hm : (r * 2 + p) % 2 = p := by omega
    rw [hd, hm]

private lemma chunk1_4_of_ag1_1_2_32_explicit (t0 t1 t2 t3 : Tensor) (r : Nat) (hr : r < 4)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) =
      ([t0, t1, t2, t3]).getD r (zeroTensor [1, 2, 32]) := by
  apply chunk1_4_of_ag1_1_2_32 _ r hr
  · simp [h0]
  · intro i hi
    match i, hi with
    | 0, _ => simpa [List.getD] using h0
    | 1, _ => simpa [List.getD] using h1
    | 2, _ => simpa [List.getD] using h2
    | 3, _ => simpa [List.getD] using h3

private lemma chunk1_4_of_ag1_1_2_32_idx0 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 0 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t0 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 0 (by omega) h0 h1 h2 h3]
  rfl

private lemma chunk1_4_of_ag1_1_2_32_idx1 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 1 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t1 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 1 (by omega) h0 h1 h2 h3]
  rfl

private lemma chunk1_4_of_ag1_1_2_32_idx2 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 2 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t2 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 2 (by omega) h0 h1 h2 h3]
  rfl

private lemma chunk1_4_of_ag1_1_2_32_idx3 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 3 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t3 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 3 (by omega) h0 h1 h2 h3]
  rfl

@[reducible] private def n_sm_lnorm_5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [903, 568, 569], outs := [570] }
@[reducible] private def n_pm_lnorm_5_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [1141, 568, 569], outs := [1145] }
@[reducible] private def n_pm_lnorm_5_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [1142, 568, 569], outs := [1146] }
@[reducible] private def n_pm_lnorm_5_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [1143, 568, 569], outs := [1147] }
@[reducible] private def n_pm_lnorm_5_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [1144, 568, 569], outs := [1148] }
@[reducible] private def n_sm_lnorm_30 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [946, 603, 604], outs := [605] }
@[reducible] private def n_pm_lnorm_30_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [1661, 603, 604], outs := [1665] }
@[reducible] private def n_pm_lnorm_30_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [1662, 603, 604], outs := [1666] }
@[reducible] private def n_pm_lnorm_30_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [1663, 603, 604], outs := [1667] }
@[reducible] private def n_pm_lnorm_30_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [1664, 603, 604], outs := [1668] }
@[reducible] private def n_sm_lnorm_55 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [989, 638, 639], outs := [640] }
@[reducible] private def n_pm_lnorm_55_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [2225, 638, 639], outs := [2229] }
@[reducible] private def n_pm_lnorm_55_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [2226, 638, 639], outs := [2230] }
@[reducible] private def n_pm_lnorm_55_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [2227, 638, 639], outs := [2231] }
@[reducible] private def n_pm_lnorm_55_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [2228, 638, 639], outs := [2232] }
@[reducible] private def n_sm_lnorm_75 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [1020, 664, 665], outs := [666] }
@[reducible] private def n_pm_lnorm_75_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [2637, 664, 665], outs := [2641] }
@[reducible] private def n_pm_lnorm_75_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [2638, 664, 665], outs := [2642] }
@[reducible] private def n_pm_lnorm_75_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [2639, 664, 665], outs := [2643] }
@[reducible] private def n_pm_lnorm_75_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [2640, 664, 665], outs := [2644] }
@[reducible] private def n_sm_lnorm_80 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [1032, 673, 674], outs := [675] }
@[reducible] private def n_pm_lnorm_80_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [2781, 673, 674], outs := [2785] }
@[reducible] private def n_pm_lnorm_80_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [2782, 673, 674], outs := [2786] }
@[reducible] private def n_pm_lnorm_80_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [2783, 673, 674], outs := [2787] }
@[reducible] private def n_pm_lnorm_80_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [2784, 673, 674], outs := [2788] }
@[reducible] private def n_sm_lnorm_100 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [1063, 699, 700], outs := [701] }
@[reducible] private def n_pm_lnorm_100_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_layernorm", ins := [3201, 699, 700], outs := [3205] }
@[reducible] private def n_pm_lnorm_100_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_layernorm", ins := [3202, 699, 700], outs := [3206] }
@[reducible] private def n_pm_lnorm_100_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_layernorm", ins := [3203, 699, 700], outs := [3207] }
@[reducible] private def n_pm_lnorm_100_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_layernorm", ins := [3204, 699, 700], outs := [3208] }


set_option maxHeartbeats 4000000 in
private theorem sm_eval_570 (initSM : Store) :
    denoteGraph sm initSM 570 = fw_layernorm (denoteGraph sm initSM 903) (denoteGraph sm initSM 568) (denoteGraph sm initSM 569) := by
  have hsub : (denoteGraph sm initSM) 570 =
      (denoteGraph { sm with nodes := sm.nodes.take 5 } initSM) 570 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 570
      (sm.nodes.take 5) (sm.nodes.drop 5)
      (List.take_append_drop 5 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 5 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 4 ++ [n_sm_lnorm_5] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_lnorm_5] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_lnorm_5 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_lnorm_5 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_lnorm_5 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [903, 568, 569], outs := [570], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 4 } initSM 903 = denoteGraph sm initSM 903 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 903
      (sm.nodes.take 4) (sm.nodes.drop 4)
      (List.take_append_drop 4 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 4 } initSM 568 = denoteGraph sm initSM 568 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 568
      (sm.nodes.take 4) (sm.nodes.drop 4)
      (List.take_append_drop 4 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 4 } initSM 569 = denoteGraph sm initSM 569 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 569
      (sm.nodes.take 4) (sm.nodes.drop 4)
      (List.take_append_drop 4 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1145 (initPM : Store) :
    denoteGraph pm initPM 1145 = fw_layernorm (denoteGraph pm initPM 1141) (denoteGraph pm initPM 568) (denoteGraph pm initPM 569) := by
  have hsub : (denoteGraph pm initPM) 1145 =
      (denoteGraph { pm with nodes := pm.nodes.take 34 } initPM) 1145 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1145
      (pm.nodes.take 34) (pm.nodes.drop 34)
      (List.take_append_drop 34 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 34 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 33 ++ [n_pm_lnorm_5_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_5_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_5_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_5_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_5_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [1141, 568, 569], outs := [1145], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 33 } initPM 1141 = denoteGraph pm initPM 1141 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1141
      (pm.nodes.take 33) (pm.nodes.drop 33)
      (List.take_append_drop 33 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 33 } initPM 568 = denoteGraph pm initPM 568 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 568
      (pm.nodes.take 33) (pm.nodes.drop 33)
      (List.take_append_drop 33 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 33 } initPM 569 = denoteGraph pm initPM 569 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 569
      (pm.nodes.take 33) (pm.nodes.drop 33)
      (List.take_append_drop 33 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1146 (initPM : Store) :
    denoteGraph pm initPM 1146 = fw_layernorm (denoteGraph pm initPM 1142) (denoteGraph pm initPM 568) (denoteGraph pm initPM 569) := by
  have hsub : (denoteGraph pm initPM) 1146 =
      (denoteGraph { pm with nodes := pm.nodes.take 35 } initPM) 1146 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1146
      (pm.nodes.take 35) (pm.nodes.drop 35)
      (List.take_append_drop 35 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 35 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 34 ++ [n_pm_lnorm_5_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_5_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_5_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_5_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_5_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [1142, 568, 569], outs := [1146], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 34 } initPM 1142 = denoteGraph pm initPM 1142 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1142
      (pm.nodes.take 34) (pm.nodes.drop 34)
      (List.take_append_drop 34 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 34 } initPM 568 = denoteGraph pm initPM 568 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 568
      (pm.nodes.take 34) (pm.nodes.drop 34)
      (List.take_append_drop 34 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 34 } initPM 569 = denoteGraph pm initPM 569 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 569
      (pm.nodes.take 34) (pm.nodes.drop 34)
      (List.take_append_drop 34 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1147 (initPM : Store) :
    denoteGraph pm initPM 1147 = fw_layernorm (denoteGraph pm initPM 1143) (denoteGraph pm initPM 568) (denoteGraph pm initPM 569) := by
  have hsub : (denoteGraph pm initPM) 1147 =
      (denoteGraph { pm with nodes := pm.nodes.take 36 } initPM) 1147 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1147
      (pm.nodes.take 36) (pm.nodes.drop 36)
      (List.take_append_drop 36 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 36 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 35 ++ [n_pm_lnorm_5_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_5_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_5_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_5_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_5_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [1143, 568, 569], outs := [1147], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 35 } initPM 1143 = denoteGraph pm initPM 1143 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1143
      (pm.nodes.take 35) (pm.nodes.drop 35)
      (List.take_append_drop 35 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 35 } initPM 568 = denoteGraph pm initPM 568 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 568
      (pm.nodes.take 35) (pm.nodes.drop 35)
      (List.take_append_drop 35 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 35 } initPM 569 = denoteGraph pm initPM 569 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 569
      (pm.nodes.take 35) (pm.nodes.drop 35)
      (List.take_append_drop 35 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1148 (initPM : Store) :
    denoteGraph pm initPM 1148 = fw_layernorm (denoteGraph pm initPM 1144) (denoteGraph pm initPM 568) (denoteGraph pm initPM 569) := by
  have hsub : (denoteGraph pm initPM) 1148 =
      (denoteGraph { pm with nodes := pm.nodes.take 37 } initPM) 1148 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1148
      (pm.nodes.take 37) (pm.nodes.drop 37)
      (List.take_append_drop 37 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 37 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 36 ++ [n_pm_lnorm_5_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_5_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_5_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_5_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_5_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [1144, 568, 569], outs := [1148], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 36 } initPM 1144 = denoteGraph pm initPM 1144 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1144
      (pm.nodes.take 36) (pm.nodes.drop 36)
      (List.take_append_drop 36 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 36 } initPM 568 = denoteGraph pm initPM 568 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 568
      (pm.nodes.take 36) (pm.nodes.drop 36)
      (List.take_append_drop 36 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 36 } initPM 569 = denoteGraph pm initPM 569 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 569
      (pm.nodes.take 36) (pm.nodes.drop 36)
      (List.take_append_drop 36 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem sm_eval_605 (initSM : Store) :
    denoteGraph sm initSM 605 = fw_layernorm (denoteGraph sm initSM 946) (denoteGraph sm initSM 603) (denoteGraph sm initSM 604) := by
  have hsub : (denoteGraph sm initSM) 605 =
      (denoteGraph { sm with nodes := sm.nodes.take 33 } initSM) 605 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 605
      (sm.nodes.take 33) (sm.nodes.drop 33)
      (List.take_append_drop 33 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 33 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 32 ++ [n_sm_lnorm_30] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_lnorm_30] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_lnorm_30 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_lnorm_30 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_lnorm_30 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [946, 603, 604], outs := [605], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 32 } initSM 946 = denoteGraph sm initSM 946 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 946
      (sm.nodes.take 32) (sm.nodes.drop 32)
      (List.take_append_drop 32 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 32 } initSM 603 = denoteGraph sm initSM 603 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 603
      (sm.nodes.take 32) (sm.nodes.drop 32)
      (List.take_append_drop 32 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 32 } initSM 604 = denoteGraph sm initSM 604 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 604
      (sm.nodes.take 32) (sm.nodes.drop 32)
      (List.take_append_drop 32 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1665 (initPM : Store) :
    denoteGraph pm initPM 1665 = fw_layernorm (denoteGraph pm initPM 1661) (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  have hsub : (denoteGraph pm initPM) 1665 =
      (denoteGraph { pm with nodes := pm.nodes.take 198 } initPM) 1665 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1665
      (pm.nodes.take 198) (pm.nodes.drop 198)
      (List.take_append_drop 198 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 198 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 197 ++ [n_pm_lnorm_30_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_30_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_30_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_30_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_30_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [1661, 603, 604], outs := [1665], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 197 } initPM 1661 = denoteGraph pm initPM 1661 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1661
      (pm.nodes.take 197) (pm.nodes.drop 197)
      (List.take_append_drop 197 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 197 } initPM 603 = denoteGraph pm initPM 603 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 603
      (pm.nodes.take 197) (pm.nodes.drop 197)
      (List.take_append_drop 197 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 197 } initPM 604 = denoteGraph pm initPM 604 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 604
      (pm.nodes.take 197) (pm.nodes.drop 197)
      (List.take_append_drop 197 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1666 (initPM : Store) :
    denoteGraph pm initPM 1666 = fw_layernorm (denoteGraph pm initPM 1662) (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  have hsub : (denoteGraph pm initPM) 1666 =
      (denoteGraph { pm with nodes := pm.nodes.take 199 } initPM) 1666 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1666
      (pm.nodes.take 199) (pm.nodes.drop 199)
      (List.take_append_drop 199 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 199 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 198 ++ [n_pm_lnorm_30_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_30_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_30_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_30_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_30_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [1662, 603, 604], outs := [1666], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 198 } initPM 1662 = denoteGraph pm initPM 1662 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1662
      (pm.nodes.take 198) (pm.nodes.drop 198)
      (List.take_append_drop 198 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 198 } initPM 603 = denoteGraph pm initPM 603 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 603
      (pm.nodes.take 198) (pm.nodes.drop 198)
      (List.take_append_drop 198 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 198 } initPM 604 = denoteGraph pm initPM 604 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 604
      (pm.nodes.take 198) (pm.nodes.drop 198)
      (List.take_append_drop 198 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1667 (initPM : Store) :
    denoteGraph pm initPM 1667 = fw_layernorm (denoteGraph pm initPM 1663) (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  have hsub : (denoteGraph pm initPM) 1667 =
      (denoteGraph { pm with nodes := pm.nodes.take 200 } initPM) 1667 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1667
      (pm.nodes.take 200) (pm.nodes.drop 200)
      (List.take_append_drop 200 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 200 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 199 ++ [n_pm_lnorm_30_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_30_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_30_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_30_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_30_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [1663, 603, 604], outs := [1667], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 199 } initPM 1663 = denoteGraph pm initPM 1663 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1663
      (pm.nodes.take 199) (pm.nodes.drop 199)
      (List.take_append_drop 199 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 199 } initPM 603 = denoteGraph pm initPM 603 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 603
      (pm.nodes.take 199) (pm.nodes.drop 199)
      (List.take_append_drop 199 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 199 } initPM 604 = denoteGraph pm initPM 604 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 604
      (pm.nodes.take 199) (pm.nodes.drop 199)
      (List.take_append_drop 199 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_1668 (initPM : Store) :
    denoteGraph pm initPM 1668 = fw_layernorm (denoteGraph pm initPM 1664) (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  have hsub : (denoteGraph pm initPM) 1668 =
      (denoteGraph { pm with nodes := pm.nodes.take 201 } initPM) 1668 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1668
      (pm.nodes.take 201) (pm.nodes.drop 201)
      (List.take_append_drop 201 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 201 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 200 ++ [n_pm_lnorm_30_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_30_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_30_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_30_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_30_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [1664, 603, 604], outs := [1668], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 200 } initPM 1664 = denoteGraph pm initPM 1664 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1664
      (pm.nodes.take 200) (pm.nodes.drop 200)
      (List.take_append_drop 200 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 200 } initPM 603 = denoteGraph pm initPM 603 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 603
      (pm.nodes.take 200) (pm.nodes.drop 200)
      (List.take_append_drop 200 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 200 } initPM 604 = denoteGraph pm initPM 604 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 604
      (pm.nodes.take 200) (pm.nodes.drop 200)
      (List.take_append_drop 200 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem sm_eval_640 (initSM : Store) :
    denoteGraph sm initSM 640 = fw_layernorm (denoteGraph sm initSM 989) (denoteGraph sm initSM 638) (denoteGraph sm initSM 639) := by
  have hsub : (denoteGraph sm initSM) 640 =
      (denoteGraph { sm with nodes := sm.nodes.take 61 } initSM) 640 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 640
      (sm.nodes.take 61) (sm.nodes.drop 61)
      (List.take_append_drop 61 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 61 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 60 ++ [n_sm_lnorm_55] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_lnorm_55] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_lnorm_55 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_lnorm_55 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_lnorm_55 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [989, 638, 639], outs := [640], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 60 } initSM 989 = denoteGraph sm initSM 989 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 989
      (sm.nodes.take 60) (sm.nodes.drop 60)
      (List.take_append_drop 60 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 60 } initSM 638 = denoteGraph sm initSM 638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 638
      (sm.nodes.take 60) (sm.nodes.drop 60)
      (List.take_append_drop 60 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 60 } initSM 639 = denoteGraph sm initSM 639 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 639
      (sm.nodes.take 60) (sm.nodes.drop 60)
      (List.take_append_drop 60 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2229 (initPM : Store) :
    denoteGraph pm initPM 2229 = fw_layernorm (denoteGraph pm initPM 2225) (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  have hsub : (denoteGraph pm initPM) 2229 =
      (denoteGraph { pm with nodes := pm.nodes.take 393 } initPM) 2229 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2229
      (pm.nodes.take 393) (pm.nodes.drop 393)
      (List.take_append_drop 393 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 393 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 392 ++ [n_pm_lnorm_55_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_55_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_55_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_55_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_55_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [2225, 638, 639], outs := [2229], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 392 } initPM 2225 = denoteGraph pm initPM 2225 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2225
      (pm.nodes.take 392) (pm.nodes.drop 392)
      (List.take_append_drop 392 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 392 } initPM 638 = denoteGraph pm initPM 638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 638
      (pm.nodes.take 392) (pm.nodes.drop 392)
      (List.take_append_drop 392 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 392 } initPM 639 = denoteGraph pm initPM 639 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 639
      (pm.nodes.take 392) (pm.nodes.drop 392)
      (List.take_append_drop 392 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2230 (initPM : Store) :
    denoteGraph pm initPM 2230 = fw_layernorm (denoteGraph pm initPM 2226) (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  have hsub : (denoteGraph pm initPM) 2230 =
      (denoteGraph { pm with nodes := pm.nodes.take 394 } initPM) 2230 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2230
      (pm.nodes.take 394) (pm.nodes.drop 394)
      (List.take_append_drop 394 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 394 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 393 ++ [n_pm_lnorm_55_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_55_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_55_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_55_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_55_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [2226, 638, 639], outs := [2230], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 393 } initPM 2226 = denoteGraph pm initPM 2226 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2226
      (pm.nodes.take 393) (pm.nodes.drop 393)
      (List.take_append_drop 393 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 393 } initPM 638 = denoteGraph pm initPM 638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 638
      (pm.nodes.take 393) (pm.nodes.drop 393)
      (List.take_append_drop 393 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 393 } initPM 639 = denoteGraph pm initPM 639 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 639
      (pm.nodes.take 393) (pm.nodes.drop 393)
      (List.take_append_drop 393 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2231 (initPM : Store) :
    denoteGraph pm initPM 2231 = fw_layernorm (denoteGraph pm initPM 2227) (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  have hsub : (denoteGraph pm initPM) 2231 =
      (denoteGraph { pm with nodes := pm.nodes.take 395 } initPM) 2231 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2231
      (pm.nodes.take 395) (pm.nodes.drop 395)
      (List.take_append_drop 395 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 395 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 394 ++ [n_pm_lnorm_55_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_55_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_55_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_55_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_55_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [2227, 638, 639], outs := [2231], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 394 } initPM 2227 = denoteGraph pm initPM 2227 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2227
      (pm.nodes.take 394) (pm.nodes.drop 394)
      (List.take_append_drop 394 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 394 } initPM 638 = denoteGraph pm initPM 638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 638
      (pm.nodes.take 394) (pm.nodes.drop 394)
      (List.take_append_drop 394 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 394 } initPM 639 = denoteGraph pm initPM 639 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 639
      (pm.nodes.take 394) (pm.nodes.drop 394)
      (List.take_append_drop 394 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2232 (initPM : Store) :
    denoteGraph pm initPM 2232 = fw_layernorm (denoteGraph pm initPM 2228) (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  have hsub : (denoteGraph pm initPM) 2232 =
      (denoteGraph { pm with nodes := pm.nodes.take 396 } initPM) 2232 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2232
      (pm.nodes.take 396) (pm.nodes.drop 396)
      (List.take_append_drop 396 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 396 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 395 ++ [n_pm_lnorm_55_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_55_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_55_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_55_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_55_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [2228, 638, 639], outs := [2232], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 395 } initPM 2228 = denoteGraph pm initPM 2228 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2228
      (pm.nodes.take 395) (pm.nodes.drop 395)
      (List.take_append_drop 395 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 395 } initPM 638 = denoteGraph pm initPM 638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 638
      (pm.nodes.take 395) (pm.nodes.drop 395)
      (List.take_append_drop 395 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 395 } initPM 639 = denoteGraph pm initPM 639 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 639
      (pm.nodes.take 395) (pm.nodes.drop 395)
      (List.take_append_drop 395 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem sm_eval_666 (initSM : Store) :
    denoteGraph sm initSM 666 = fw_layernorm (denoteGraph sm initSM 1020) (denoteGraph sm initSM 664) (denoteGraph sm initSM 665) := by
  have hsub : (denoteGraph sm initSM) 666 =
      (denoteGraph { sm with nodes := sm.nodes.take 83 } initSM) 666 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 666
      (sm.nodes.take 83) (sm.nodes.drop 83)
      (List.take_append_drop 83 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 83 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 82 ++ [n_sm_lnorm_75] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_lnorm_75] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_lnorm_75 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_lnorm_75 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_lnorm_75 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [1020, 664, 665], outs := [666], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 82 } initSM 1020 = denoteGraph sm initSM 1020 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1020
      (sm.nodes.take 82) (sm.nodes.drop 82)
      (List.take_append_drop 82 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 82 } initSM 664 = denoteGraph sm initSM 664 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 664
      (sm.nodes.take 82) (sm.nodes.drop 82)
      (List.take_append_drop 82 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 82 } initSM 665 = denoteGraph sm initSM 665 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 665
      (sm.nodes.take 82) (sm.nodes.drop 82)
      (List.take_append_drop 82 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2641 (initPM : Store) :
    denoteGraph pm initPM 2641 = fw_layernorm (denoteGraph pm initPM 2637) (denoteGraph pm initPM 664) (denoteGraph pm initPM 665) := by
  have hsub : (denoteGraph pm initPM) 2641 =
      (denoteGraph { pm with nodes := pm.nodes.take 533 } initPM) 2641 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2641
      (pm.nodes.take 533) (pm.nodes.drop 533)
      (List.take_append_drop 533 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 533 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 532 ++ [n_pm_lnorm_75_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_75_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_75_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_75_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_75_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [2637, 664, 665], outs := [2641], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 532 } initPM 2637 = denoteGraph pm initPM 2637 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2637
      (pm.nodes.take 532) (pm.nodes.drop 532)
      (List.take_append_drop 532 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 532 } initPM 664 = denoteGraph pm initPM 664 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 664
      (pm.nodes.take 532) (pm.nodes.drop 532)
      (List.take_append_drop 532 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 532 } initPM 665 = denoteGraph pm initPM 665 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 665
      (pm.nodes.take 532) (pm.nodes.drop 532)
      (List.take_append_drop 532 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2642 (initPM : Store) :
    denoteGraph pm initPM 2642 = fw_layernorm (denoteGraph pm initPM 2638) (denoteGraph pm initPM 664) (denoteGraph pm initPM 665) := by
  have hsub : (denoteGraph pm initPM) 2642 =
      (denoteGraph { pm with nodes := pm.nodes.take 534 } initPM) 2642 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2642
      (pm.nodes.take 534) (pm.nodes.drop 534)
      (List.take_append_drop 534 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 534 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 533 ++ [n_pm_lnorm_75_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_75_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_75_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_75_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_75_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [2638, 664, 665], outs := [2642], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 533 } initPM 2638 = denoteGraph pm initPM 2638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2638
      (pm.nodes.take 533) (pm.nodes.drop 533)
      (List.take_append_drop 533 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 533 } initPM 664 = denoteGraph pm initPM 664 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 664
      (pm.nodes.take 533) (pm.nodes.drop 533)
      (List.take_append_drop 533 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 533 } initPM 665 = denoteGraph pm initPM 665 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 665
      (pm.nodes.take 533) (pm.nodes.drop 533)
      (List.take_append_drop 533 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2643 (initPM : Store) :
    denoteGraph pm initPM 2643 = fw_layernorm (denoteGraph pm initPM 2639) (denoteGraph pm initPM 664) (denoteGraph pm initPM 665) := by
  have hsub : (denoteGraph pm initPM) 2643 =
      (denoteGraph { pm with nodes := pm.nodes.take 535 } initPM) 2643 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2643
      (pm.nodes.take 535) (pm.nodes.drop 535)
      (List.take_append_drop 535 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 535 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 534 ++ [n_pm_lnorm_75_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_75_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_75_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_75_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_75_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [2639, 664, 665], outs := [2643], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 534 } initPM 2639 = denoteGraph pm initPM 2639 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2639
      (pm.nodes.take 534) (pm.nodes.drop 534)
      (List.take_append_drop 534 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 534 } initPM 664 = denoteGraph pm initPM 664 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 664
      (pm.nodes.take 534) (pm.nodes.drop 534)
      (List.take_append_drop 534 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 534 } initPM 665 = denoteGraph pm initPM 665 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 665
      (pm.nodes.take 534) (pm.nodes.drop 534)
      (List.take_append_drop 534 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2644 (initPM : Store) :
    denoteGraph pm initPM 2644 = fw_layernorm (denoteGraph pm initPM 2640) (denoteGraph pm initPM 664) (denoteGraph pm initPM 665) := by
  have hsub : (denoteGraph pm initPM) 2644 =
      (denoteGraph { pm with nodes := pm.nodes.take 536 } initPM) 2644 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2644
      (pm.nodes.take 536) (pm.nodes.drop 536)
      (List.take_append_drop 536 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 536 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 535 ++ [n_pm_lnorm_75_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_75_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_75_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_75_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_75_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [2640, 664, 665], outs := [2644], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 535 } initPM 2640 = denoteGraph pm initPM 2640 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2640
      (pm.nodes.take 535) (pm.nodes.drop 535)
      (List.take_append_drop 535 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 535 } initPM 664 = denoteGraph pm initPM 664 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 664
      (pm.nodes.take 535) (pm.nodes.drop 535)
      (List.take_append_drop 535 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 535 } initPM 665 = denoteGraph pm initPM 665 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 665
      (pm.nodes.take 535) (pm.nodes.drop 535)
      (List.take_append_drop 535 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem sm_eval_675 (initSM : Store) :
    denoteGraph sm initSM 675 = fw_layernorm (denoteGraph sm initSM 1032) (denoteGraph sm initSM 673) (denoteGraph sm initSM 674) := by
  have hsub : (denoteGraph sm initSM) 675 =
      (denoteGraph { sm with nodes := sm.nodes.take 89 } initSM) 675 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 675
      (sm.nodes.take 89) (sm.nodes.drop 89)
      (List.take_append_drop 89 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 89 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 88 ++ [n_sm_lnorm_80] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_lnorm_80] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_lnorm_80 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_lnorm_80 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_lnorm_80 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [1032, 673, 674], outs := [675], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 88 } initSM 1032 = denoteGraph sm initSM 1032 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1032
      (sm.nodes.take 88) (sm.nodes.drop 88)
      (List.take_append_drop 88 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 88 } initSM 673 = denoteGraph sm initSM 673 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 673
      (sm.nodes.take 88) (sm.nodes.drop 88)
      (List.take_append_drop 88 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 88 } initSM 674 = denoteGraph sm initSM 674 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 674
      (sm.nodes.take 88) (sm.nodes.drop 88)
      (List.take_append_drop 88 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2785 (initPM : Store) :
    denoteGraph pm initPM 2785 = fw_layernorm (denoteGraph pm initPM 2781) (denoteGraph pm initPM 673) (denoteGraph pm initPM 674) := by
  have hsub : (denoteGraph pm initPM) 2785 =
      (denoteGraph { pm with nodes := pm.nodes.take 575 } initPM) 2785 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2785
      (pm.nodes.take 575) (pm.nodes.drop 575)
      (List.take_append_drop 575 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 575 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 574 ++ [n_pm_lnorm_80_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_80_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_80_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_80_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_80_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [2781, 673, 674], outs := [2785], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 574 } initPM 2781 = denoteGraph pm initPM 2781 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2781
      (pm.nodes.take 574) (pm.nodes.drop 574)
      (List.take_append_drop 574 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 574 } initPM 673 = denoteGraph pm initPM 673 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 673
      (pm.nodes.take 574) (pm.nodes.drop 574)
      (List.take_append_drop 574 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 574 } initPM 674 = denoteGraph pm initPM 674 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 674
      (pm.nodes.take 574) (pm.nodes.drop 574)
      (List.take_append_drop 574 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2786 (initPM : Store) :
    denoteGraph pm initPM 2786 = fw_layernorm (denoteGraph pm initPM 2782) (denoteGraph pm initPM 673) (denoteGraph pm initPM 674) := by
  have hsub : (denoteGraph pm initPM) 2786 =
      (denoteGraph { pm with nodes := pm.nodes.take 576 } initPM) 2786 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2786
      (pm.nodes.take 576) (pm.nodes.drop 576)
      (List.take_append_drop 576 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 576 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 575 ++ [n_pm_lnorm_80_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_80_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_80_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_80_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_80_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [2782, 673, 674], outs := [2786], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 575 } initPM 2782 = denoteGraph pm initPM 2782 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2782
      (pm.nodes.take 575) (pm.nodes.drop 575)
      (List.take_append_drop 575 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 575 } initPM 673 = denoteGraph pm initPM 673 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 673
      (pm.nodes.take 575) (pm.nodes.drop 575)
      (List.take_append_drop 575 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 575 } initPM 674 = denoteGraph pm initPM 674 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 674
      (pm.nodes.take 575) (pm.nodes.drop 575)
      (List.take_append_drop 575 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2787 (initPM : Store) :
    denoteGraph pm initPM 2787 = fw_layernorm (denoteGraph pm initPM 2783) (denoteGraph pm initPM 673) (denoteGraph pm initPM 674) := by
  have hsub : (denoteGraph pm initPM) 2787 =
      (denoteGraph { pm with nodes := pm.nodes.take 577 } initPM) 2787 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2787
      (pm.nodes.take 577) (pm.nodes.drop 577)
      (List.take_append_drop 577 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 577 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 576 ++ [n_pm_lnorm_80_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_80_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_80_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_80_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_80_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [2783, 673, 674], outs := [2787], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 576 } initPM 2783 = denoteGraph pm initPM 2783 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2783
      (pm.nodes.take 576) (pm.nodes.drop 576)
      (List.take_append_drop 576 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 576 } initPM 673 = denoteGraph pm initPM 673 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 673
      (pm.nodes.take 576) (pm.nodes.drop 576)
      (List.take_append_drop 576 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 576 } initPM 674 = denoteGraph pm initPM 674 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 674
      (pm.nodes.take 576) (pm.nodes.drop 576)
      (List.take_append_drop 576 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_2788 (initPM : Store) :
    denoteGraph pm initPM 2788 = fw_layernorm (denoteGraph pm initPM 2784) (denoteGraph pm initPM 673) (denoteGraph pm initPM 674) := by
  have hsub : (denoteGraph pm initPM) 2788 =
      (denoteGraph { pm with nodes := pm.nodes.take 578 } initPM) 2788 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2788
      (pm.nodes.take 578) (pm.nodes.drop 578)
      (List.take_append_drop 578 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 578 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 577 ++ [n_pm_lnorm_80_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_80_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_80_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_80_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_80_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [2784, 673, 674], outs := [2788], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 577 } initPM 2784 = denoteGraph pm initPM 2784 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2784
      (pm.nodes.take 577) (pm.nodes.drop 577)
      (List.take_append_drop 577 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 577 } initPM 673 = denoteGraph pm initPM 673 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 673
      (pm.nodes.take 577) (pm.nodes.drop 577)
      (List.take_append_drop 577 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 577 } initPM 674 = denoteGraph pm initPM 674 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 674
      (pm.nodes.take 577) (pm.nodes.drop 577)
      (List.take_append_drop 577 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem sm_eval_701 (initSM : Store) :
    denoteGraph sm initSM 701 = fw_layernorm (denoteGraph sm initSM 1063) (denoteGraph sm initSM 699) (denoteGraph sm initSM 700) := by
  have hsub : (denoteGraph sm initSM) 701 =
      (denoteGraph { sm with nodes := sm.nodes.take 111 } initSM) 701 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 701
      (sm.nodes.take 111) (sm.nodes.drop 111)
      (List.take_append_drop 111 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 111 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 110 ++ [n_sm_lnorm_100] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_lnorm_100] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_lnorm_100 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_lnorm_100 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_lnorm_100 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [1063, 699, 700], outs := [701], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hX : denoteGraph { sm with nodes := sm.nodes.take 110 } initSM 1063 = denoteGraph sm initSM 1063 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1063
      (sm.nodes.take 110) (sm.nodes.drop 110)
      (List.take_append_drop 110 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { sm with nodes := sm.nodes.take 110 } initSM 699 = denoteGraph sm initSM 699 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 699
      (sm.nodes.take 110) (sm.nodes.drop 110)
      (List.take_append_drop 110 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { sm with nodes := sm.nodes.take 110 } initSM 700 = denoteGraph sm initSM 700 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 700
      (sm.nodes.take 110) (sm.nodes.drop 110)
      (List.take_append_drop 110 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hX, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_3205 (initPM : Store) :
    denoteGraph pm initPM 3205 = fw_layernorm (denoteGraph pm initPM 3201) (denoteGraph pm initPM 699) (denoteGraph pm initPM 700) := by
  have hsub : (denoteGraph pm initPM) 3205 =
      (denoteGraph { pm with nodes := pm.nodes.take 725 } initPM) 3205 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3205
      (pm.nodes.take 725) (pm.nodes.drop 725)
      (List.take_append_drop 725 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 725 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 724 ++ [n_pm_lnorm_100_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_100_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_100_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_100_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_100_0 =
      ({ rank := 0, op := "OpName.FW_layernorm", ins := [3201, 699, 700], outs := [3205], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 724 } initPM 3201 = denoteGraph pm initPM 3201 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3201
      (pm.nodes.take 724) (pm.nodes.drop 724)
      (List.take_append_drop 724 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 724 } initPM 699 = denoteGraph pm initPM 699 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 699
      (pm.nodes.take 724) (pm.nodes.drop 724)
      (List.take_append_drop 724 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 724 } initPM 700 = denoteGraph pm initPM 700 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 700
      (pm.nodes.take 724) (pm.nodes.drop 724)
      (List.take_append_drop 724 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_3206 (initPM : Store) :
    denoteGraph pm initPM 3206 = fw_layernorm (denoteGraph pm initPM 3202) (denoteGraph pm initPM 699) (denoteGraph pm initPM 700) := by
  have hsub : (denoteGraph pm initPM) 3206 =
      (denoteGraph { pm with nodes := pm.nodes.take 726 } initPM) 3206 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3206
      (pm.nodes.take 726) (pm.nodes.drop 726)
      (List.take_append_drop 726 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 726 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 725 ++ [n_pm_lnorm_100_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_100_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_100_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_100_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_100_1 =
      ({ rank := 1, op := "OpName.FW_layernorm", ins := [3202, 699, 700], outs := [3206], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 725 } initPM 3202 = denoteGraph pm initPM 3202 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3202
      (pm.nodes.take 725) (pm.nodes.drop 725)
      (List.take_append_drop 725 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 725 } initPM 699 = denoteGraph pm initPM 699 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 699
      (pm.nodes.take 725) (pm.nodes.drop 725)
      (List.take_append_drop 725 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 725 } initPM 700 = denoteGraph pm initPM 700 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 700
      (pm.nodes.take 725) (pm.nodes.drop 725)
      (List.take_append_drop 725 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_3207 (initPM : Store) :
    denoteGraph pm initPM 3207 = fw_layernorm (denoteGraph pm initPM 3203) (denoteGraph pm initPM 699) (denoteGraph pm initPM 700) := by
  have hsub : (denoteGraph pm initPM) 3207 =
      (denoteGraph { pm with nodes := pm.nodes.take 727 } initPM) 3207 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3207
      (pm.nodes.take 727) (pm.nodes.drop 727)
      (List.take_append_drop 727 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 727 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 726 ++ [n_pm_lnorm_100_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_100_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_100_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_100_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_100_2 =
      ({ rank := 2, op := "OpName.FW_layernorm", ins := [3203, 699, 700], outs := [3207], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 726 } initPM 3203 = denoteGraph pm initPM 3203 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3203
      (pm.nodes.take 726) (pm.nodes.drop 726)
      (List.take_append_drop 726 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 726 } initPM 699 = denoteGraph pm initPM 699 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 699
      (pm.nodes.take 726) (pm.nodes.drop 726)
      (List.take_append_drop 726 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 726 } initPM 700 = denoteGraph pm initPM 700 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 700
      (pm.nodes.take 726) (pm.nodes.drop 726)
      (List.take_append_drop 726 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 4000000 in
private theorem pm_eval_3208 (initPM : Store) :
    denoteGraph pm initPM 3208 = fw_layernorm (denoteGraph pm initPM 3204) (denoteGraph pm initPM 699) (denoteGraph pm initPM 700) := by
  have hsub : (denoteGraph pm initPM) 3208 =
      (denoteGraph { pm with nodes := pm.nodes.take 728 } initPM) 3208 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3208
      (pm.nodes.take 728) (pm.nodes.drop 728)
      (List.take_append_drop 728 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 728 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 727 ++ [n_pm_lnorm_100_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_lnorm_100_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_lnorm_100_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_lnorm_100_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_lnorm_100_3 =
      ({ rank := 3, op := "OpName.FW_layernorm", ins := [3204, 699, 700], outs := [3208], params := [] } : NodeDecl) from rfl,
      applyNode_fw_layernorm_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 727 } initPM 3204 = denoteGraph pm initPM 3204 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3204
      (pm.nodes.take 727) (pm.nodes.drop 727)
      (List.take_append_drop 727 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph { pm with nodes := pm.nodes.take 727 } initPM 699 = denoteGraph pm initPM 699 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 699
      (pm.nodes.take 727) (pm.nodes.drop 727)
      (List.take_append_drop 727 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph { pm with nodes := pm.nodes.take 727 } initPM 700 = denoteGraph pm initPM 700 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 700
      (pm.nodes.take 727) (pm.nodes.drop 727)
      (List.take_append_drop 727 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hI, hW, hB]


set_option maxHeartbeats 8000000 in
theorem prove_pattern_5 : pattern_5_stmt := by
  intro target ht
  cases ht with
  | goal_5 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_257_stmt :=
      prove_pattern_127 pattern_127_target.goal_257
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 1141).shape, (denoteGraph pm initPM 1142).shape,
         (denoteGraph pm initPM 1143).shape, (denoteGraph pm initPM 1144).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_257, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 1141).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1142).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1143).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1144).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 1141).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 1142).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 1143).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 1144).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 903).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_257] using hs
    have h_input_gather : denoteGraph sm initSM 903 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1141, denoteGraph pm initPM 1142,
         denoteGraph pm initPM 1143, denoteGraph pm initPM 1144] := by
      have hh := h_eq_rec
      simp only [goal_257, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have hinput_chunk0 : denoteGraph pm initPM 1141 =
        chunkPrimDimN 1 4 0 (denoteGraph sm initSM 903) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk1 : denoteGraph pm initPM 1142 =
        chunkPrimDimN 1 4 1 (denoteGraph sm initSM 903) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk2 : denoteGraph pm initPM 1143 =
        chunkPrimDimN 1 4 2 (denoteGraph sm initSM 903) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk3 : denoteGraph pm initPM 1144 =
        chunkPrimDimN 1 4 3 (denoteGraph sm initSM 903) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have h_init_W : InitGoalHolds pm.numRanks initGoal_568 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_569 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 568 = initPM 568 := by
      have hh := h_init_W.2.2
      simpa [initGoal_568, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 569 = initPM 569 := by
      have hh := h_init_B.2.2
      simpa [initGoal_569, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 568 = initSM 568 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 568
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 569 = initSM 569 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 569
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 568 = initPM 568 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 568
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 569 = initPM 569 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 569
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 568 = denoteGraph pm initPM 568 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 569 = denoteGraph pm initPM 569 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_lift initSM initPM
      570 903 568 569 1145 1146 1147 1148 1141 1142 1143 1144
      (sm_eval_570 initSM)
      (pm_eval_1145 initPM) (pm_eval_1146 initPM)
      (pm_eval_1147 initPM) (pm_eval_1148 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      hinput_chunk0 hinput_chunk1 hinput_chunk2 hinput_chunk3
    show (denoteGraph sm initSM 570).shape = goal_5.tsShape ∧
      _ = goal_5.tpShapes ∧
      denoteGraph sm initSM 570 =
        reconstructWithDim goal_5.gatherDim pm.numRanks 0
          (goal_5.tps.map (fun p => denoteGraph pm initPM p.tid))
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_5] using hs1
    · simpa [goal_5, List.map_cons, List.map_nil] using hs2
    · simp only [goal_5, List.map_cons, List.map_nil]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · exact hs3
      · have h_out_split :
            (denoteGraph pm initPM 1145).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 1146).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 1147).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 1148).shape = [1, 2, 32] := by
          have hh := hs2
          rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
          exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
        rw [h_out_split.1]
        intro hbad; cases hbad

  | goal_30 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_271_stmt :=
      prove_pattern_127 pattern_127_target.goal_271
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 1661).shape, (denoteGraph pm initPM 1662).shape,
         (denoteGraph pm initPM 1663).shape, (denoteGraph pm initPM 1664).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_271, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 1661).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1662).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1663).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1664).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 1661).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 1662).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 1663).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 1664).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 946).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_271] using hs
    have h_input_gather : denoteGraph sm initSM 946 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1661, denoteGraph pm initPM 1662,
         denoteGraph pm initPM 1663, denoteGraph pm initPM 1664] := by
      have hh := h_eq_rec
      simp only [goal_271, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have hinput_chunk0 : denoteGraph pm initPM 1661 =
        chunkPrimDimN 1 4 0 (denoteGraph sm initSM 946) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk1 : denoteGraph pm initPM 1662 =
        chunkPrimDimN 1 4 1 (denoteGraph sm initSM 946) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk2 : denoteGraph pm initPM 1663 =
        chunkPrimDimN 1 4 2 (denoteGraph sm initSM 946) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk3 : denoteGraph pm initPM 1664 =
        chunkPrimDimN 1 4 3 (denoteGraph sm initSM 946) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have h_init_W : InitGoalHolds pm.numRanks initGoal_603 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_604 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 603 = initPM 603 := by
      have hh := h_init_W.2.2
      simpa [initGoal_603, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 604 = initPM 604 := by
      have hh := h_init_B.2.2
      simpa [initGoal_604, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 603 = initSM 603 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 603
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 604 = initSM 604 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 604
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 603 = initPM 603 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 603
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 604 = initPM 604 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 604
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 603 = denoteGraph pm initPM 603 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 604 = denoteGraph pm initPM 604 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_lift initSM initPM
      605 946 603 604 1665 1666 1667 1668 1661 1662 1663 1664
      (sm_eval_605 initSM)
      (pm_eval_1665 initPM) (pm_eval_1666 initPM)
      (pm_eval_1667 initPM) (pm_eval_1668 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      hinput_chunk0 hinput_chunk1 hinput_chunk2 hinput_chunk3
    show (denoteGraph sm initSM 605).shape = goal_30.tsShape ∧
      _ = goal_30.tpShapes ∧
      denoteGraph sm initSM 605 =
        reconstructWithDim goal_30.gatherDim pm.numRanks 0
          (goal_30.tps.map (fun p => denoteGraph pm initPM p.tid))
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_30] using hs1
    · simpa [goal_30, List.map_cons, List.map_nil] using hs2
    · simp only [goal_30, List.map_cons, List.map_nil]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · exact hs3
      · have h_out_split :
            (denoteGraph pm initPM 1665).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 1666).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 1667).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 1668).shape = [1, 2, 32] := by
          have hh := hs2
          rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
          exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
        rw [h_out_split.1]
        intro hbad; cases hbad

  | goal_55 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_285_stmt :=
      prove_pattern_128 pattern_128_target.goal_285
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 2225).shape, (denoteGraph pm initPM 2226).shape,
         (denoteGraph pm initPM 2227).shape, (denoteGraph pm initPM 2228).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_285, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2225).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2226).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2227).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2228).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 2225).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 2226).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 2227).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 2228).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 989).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_285] using hs
    have h_input_gather : denoteGraph sm initSM 989 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2225, denoteGraph pm initPM 2226,
         denoteGraph pm initPM 2227, denoteGraph pm initPM 2228] := by
      have hh := h_eq_rec
      simp only [goal_285, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have hinput_chunk0 : denoteGraph pm initPM 2225 =
        chunkPrimDimN 1 4 0 (denoteGraph sm initSM 989) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk1 : denoteGraph pm initPM 2226 =
        chunkPrimDimN 1 4 1 (denoteGraph sm initSM 989) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk2 : denoteGraph pm initPM 2227 =
        chunkPrimDimN 1 4 2 (denoteGraph sm initSM 989) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk3 : denoteGraph pm initPM 2228 =
        chunkPrimDimN 1 4 3 (denoteGraph sm initSM 989) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have h_init_W : InitGoalHolds pm.numRanks initGoal_638 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_639 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 638 = initPM 638 := by
      have hh := h_init_W.2.2
      simpa [initGoal_638, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 639 = initPM 639 := by
      have hh := h_init_B.2.2
      simpa [initGoal_639, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 638 = initSM 638 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 638
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 639 = initSM 639 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 639
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 638 = initPM 638 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 638
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 639 = initPM 639 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 639
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 638 = denoteGraph pm initPM 638 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 639 = denoteGraph pm initPM 639 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_lift initSM initPM
      640 989 638 639 2229 2230 2231 2232 2225 2226 2227 2228
      (sm_eval_640 initSM)
      (pm_eval_2229 initPM) (pm_eval_2230 initPM)
      (pm_eval_2231 initPM) (pm_eval_2232 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      hinput_chunk0 hinput_chunk1 hinput_chunk2 hinput_chunk3
    show (denoteGraph sm initSM 640).shape = goal_55.tsShape ∧
      _ = goal_55.tpShapes ∧
      denoteGraph sm initSM 640 =
        reconstructWithDim goal_55.gatherDim pm.numRanks 0
          (goal_55.tps.map (fun p => denoteGraph pm initPM p.tid))
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_55] using hs1
    · simpa [goal_55, List.map_cons, List.map_nil] using hs2
    · simp only [goal_55, List.map_cons, List.map_nil]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · exact hs3
      · have h_out_split :
            (denoteGraph pm initPM 2229).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2230).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2231).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2232).shape = [1, 2, 32] := by
          have hh := hs2
          rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
          exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
        rw [h_out_split.1]
        intro hbad; cases hbad

  | goal_75 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_295_stmt :=
      prove_pattern_128 pattern_128_target.goal_295
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 2637).shape, (denoteGraph pm initPM 2638).shape,
         (denoteGraph pm initPM 2639).shape, (denoteGraph pm initPM 2640).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_295, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2637).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2638).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2639).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2640).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 2637).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 2638).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 2639).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 2640).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 1020).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_295] using hs
    have h_input_gather : denoteGraph sm initSM 1020 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2637, denoteGraph pm initPM 2638,
         denoteGraph pm initPM 2639, denoteGraph pm initPM 2640] := by
      have hh := h_eq_rec
      simp only [goal_295, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have hinput_chunk0 : denoteGraph pm initPM 2637 =
        chunkPrimDimN 1 4 0 (denoteGraph sm initSM 1020) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk1 : denoteGraph pm initPM 2638 =
        chunkPrimDimN 1 4 1 (denoteGraph sm initSM 1020) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk2 : denoteGraph pm initPM 2639 =
        chunkPrimDimN 1 4 2 (denoteGraph sm initSM 1020) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk3 : denoteGraph pm initPM 2640 =
        chunkPrimDimN 1 4 3 (denoteGraph sm initSM 1020) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have h_init_W : InitGoalHolds pm.numRanks initGoal_664 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_665 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 664 = initPM 664 := by
      have hh := h_init_W.2.2
      simpa [initGoal_664, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 665 = initPM 665 := by
      have hh := h_init_B.2.2
      simpa [initGoal_665, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 664 = initSM 664 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 664
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 665 = initSM 665 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 665
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 664 = initPM 664 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 664
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 665 = initPM 665 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 665
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 664 = denoteGraph pm initPM 664 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 665 = denoteGraph pm initPM 665 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_lift initSM initPM
      666 1020 664 665 2641 2642 2643 2644 2637 2638 2639 2640
      (sm_eval_666 initSM)
      (pm_eval_2641 initPM) (pm_eval_2642 initPM)
      (pm_eval_2643 initPM) (pm_eval_2644 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      hinput_chunk0 hinput_chunk1 hinput_chunk2 hinput_chunk3
    show (denoteGraph sm initSM 666).shape = goal_75.tsShape ∧
      _ = goal_75.tpShapes ∧
      denoteGraph sm initSM 666 =
        reconstructWithDim goal_75.gatherDim pm.numRanks 0
          (goal_75.tps.map (fun p => denoteGraph pm initPM p.tid))
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_75] using hs1
    · simpa [goal_75, List.map_cons, List.map_nil] using hs2
    · simp only [goal_75, List.map_cons, List.map_nil]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · exact hs3
      · have h_out_split :
            (denoteGraph pm initPM 2641).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2642).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2643).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2644).shape = [1, 2, 32] := by
          have hh := hs2
          rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
          exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
        rw [h_out_split.1]
        intro hbad; cases hbad

  | goal_80 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_299_stmt :=
      prove_pattern_128 pattern_128_target.goal_299
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 2781).shape, (denoteGraph pm initPM 2782).shape,
         (denoteGraph pm initPM 2783).shape, (denoteGraph pm initPM 2784).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_299, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2781).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2782).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2783).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2784).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 2781).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 2782).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 2783).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 2784).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 1032).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_299] using hs
    have h_input_gather : denoteGraph sm initSM 1032 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2781, denoteGraph pm initPM 2782,
         denoteGraph pm initPM 2783, denoteGraph pm initPM 2784] := by
      have hh := h_eq_rec
      simp only [goal_299, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have hinput_chunk0 : denoteGraph pm initPM 2781 =
        chunkPrimDimN 1 4 0 (denoteGraph sm initSM 1032) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk1 : denoteGraph pm initPM 2782 =
        chunkPrimDimN 1 4 1 (denoteGraph sm initSM 1032) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk2 : denoteGraph pm initPM 2783 =
        chunkPrimDimN 1 4 2 (denoteGraph sm initSM 1032) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk3 : denoteGraph pm initPM 2784 =
        chunkPrimDimN 1 4 3 (denoteGraph sm initSM 1032) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have h_init_W : InitGoalHolds pm.numRanks initGoal_673 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_674 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 673 = initPM 673 := by
      have hh := h_init_W.2.2
      simpa [initGoal_673, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 674 = initPM 674 := by
      have hh := h_init_B.2.2
      simpa [initGoal_674, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 673 = initSM 673 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 673
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 674 = initSM 674 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 674
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 673 = initPM 673 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 673
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 674 = initPM 674 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 674
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 673 = denoteGraph pm initPM 673 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 674 = denoteGraph pm initPM 674 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_lift initSM initPM
      675 1032 673 674 2785 2786 2787 2788 2781 2782 2783 2784
      (sm_eval_675 initSM)
      (pm_eval_2785 initPM) (pm_eval_2786 initPM)
      (pm_eval_2787 initPM) (pm_eval_2788 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      hinput_chunk0 hinput_chunk1 hinput_chunk2 hinput_chunk3
    show (denoteGraph sm initSM 675).shape = goal_80.tsShape ∧
      _ = goal_80.tpShapes ∧
      denoteGraph sm initSM 675 =
        reconstructWithDim goal_80.gatherDim pm.numRanks 0
          (goal_80.tps.map (fun p => denoteGraph pm initPM p.tid))
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_80] using hs1
    · simpa [goal_80, List.map_cons, List.map_nil] using hs2
    · simp only [goal_80, List.map_cons, List.map_nil]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · exact hs3
      · have h_out_split :
            (denoteGraph pm initPM 2785).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2786).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2787).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 2788).shape = [1, 2, 32] := by
          have hh := hs2
          rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
          exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
        rw [h_out_split.1]
        intro hbad; cases hbad

  | goal_100 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_309_stmt :=
      prove_pattern_128 pattern_128_target.goal_309
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    have h_pm_shapes' :
        [(denoteGraph pm initPM 3201).shape, (denoteGraph pm initPM 3202).shape,
         (denoteGraph pm initPM 3203).shape, (denoteGraph pm initPM 3204).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_309, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 3201).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3202).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3203).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3204).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 3201).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 3202).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 3203).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 3204).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_xshape : (denoteGraph sm initSM 1063).shape = [1, 8, 32] := by
      have hs := h_sm_shape; simpa [goal_309] using hs
    have h_input_gather : denoteGraph sm initSM 1063 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 3201, denoteGraph pm initPM 3202,
         denoteGraph pm initPM 3203, denoteGraph pm initPM 3204] := by
      have hh := h_eq_rec
      simp only [goal_309, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    have hinput_chunk0 : denoteGraph pm initPM 3201 =
        chunkPrimDimN 1 4 0 (denoteGraph sm initSM 1063) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk1 : denoteGraph pm initPM 3202 =
        chunkPrimDimN 1 4 1 (denoteGraph sm initSM 1063) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk2 : denoteGraph pm initPM 3203 =
        chunkPrimDimN 1 4 2 (denoteGraph sm initSM 1063) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have hinput_chunk3 : denoteGraph pm initPM 3204 =
        chunkPrimDimN 1 4 3 (denoteGraph sm initSM 1063) := by
      rw [h_input_gather, chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape]
    have h_init_W : InitGoalHolds pm.numRanks initGoal_699 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_700 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 699 = initPM 699 := by
      have hh := h_init_W.2.2
      simpa [initGoal_699, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM 700 = initPM 700 := by
      have hh := h_init_B.2.2
      simpa [initGoal_700, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 699 = initSM 699 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 699
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM 700 = initSM 700 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 700
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 699 = initPM 699 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 699
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM 700 = initPM 700 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 700
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 699 = denoteGraph pm initPM 699 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM 700 = denoteGraph pm initPM 700 := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := layernorm_dim1_4_lift initSM initPM
      701 1063 699 700 3205 3206 3207 3208 3201 3202 3203 3204
      (sm_eval_701 initSM)
      (pm_eval_3205 initPM) (pm_eval_3206 initPM)
      (pm_eval_3207 initPM) (pm_eval_3208 initPM)
      hW_sm_pm hB_sm_pm h_xshape hI0_shape hI1_shape hI2_shape hI3_shape
      hinput_chunk0 hinput_chunk1 hinput_chunk2 hinput_chunk3
    show (denoteGraph sm initSM 701).shape = goal_100.tsShape ∧
      _ = goal_100.tpShapes ∧
      denoteGraph sm initSM 701 =
        reconstructWithDim goal_100.gatherDim pm.numRanks 0
          (goal_100.tps.map (fun p => denoteGraph pm initPM p.tid))
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_100] using hs1
    · simpa [goal_100, List.map_cons, List.map_nil] using hs2
    · simp only [goal_100, List.map_cons, List.map_nil]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · exact hs3
      · have h_out_split :
            (denoteGraph pm initPM 3205).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 3206).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 3207).shape = [1, 2, 32] ∧
            (denoteGraph pm initPM 3208).shape = [1, 2, 32] := by
          have hh := hs2
          rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
          exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
        rw [h_out_split.1]
        intro hbad; cases hbad


end TrainVerify.Denote.GeneratedPatterns
