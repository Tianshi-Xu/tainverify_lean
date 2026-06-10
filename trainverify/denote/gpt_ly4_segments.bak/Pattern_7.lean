/- Auto-generated pattern proof file.
   Pattern: 7
   Hash: b9a1e6b010ffbff2
   Goals: 8, 56, 57
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_131
import denote.gpt_ly4_segments.Pattern_139
import denote.gpt_ly4_segments.Pattern_140

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_7_goalIds : List Nat := [8, 56, 57]
inductive pattern_7_target : Prop → Prop
  | goal_8 : pattern_7_target goal_8_stmt
  | goal_56 : pattern_7_target goal_56_stmt
  | goal_57 : pattern_7_target goal_57_stmt

def pattern_7_stmt : Prop :=
  ∀ {target : Prop}, pattern_7_target target → target

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## Helper: value extraction for `fw_linear` applied to 3D input. -/

private lemma fw_linear_3d_valAt_1_8_32
    (x w : Tensor) (o : Nat)
    (hx : x.shape = [1, 8, 32]) (hw : w.shape = [o, 32]) (ho : 0 < o)
    (idx : Nat) (hidx : idx < 8 * o) :
    valAt (fw_linear x w) idx =
      ∑ j ∈ Finset.range 32,
        valAt x (idx / o * 32 + j) * valAt w (idx % o * 32 + j) := by
  have hfw_shape : (fw_linear x w).shape = [1, 8, o] :=
    fw_linear_3d_shape 1 8 32 o x w hx hw
  have hso_pos : 0 < 8 * o := Nat.mul_pos (by omega) ho
  have hso_ne : (8 * o : Nat) ≠ 0 := Nat.ne_of_gt hso_pos
  have ho_ne : (o : Nat) ≠ 0 := Nat.ne_of_gt ho
  have hidx_div : idx / (8 * o) = 0 := Nat.div_eq_of_lt hidx
  have hidx_mod : idx % (8 * o) = idx := Nat.mod_eq_of_lt hidx
  conv_lhs => simp only [fw_linear, hx, hw]
  have hprod : idx < prodShape [1, 8, o] := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte, hidx_div, hidx_mod,
             Nat.zero_mul, Nat.zero_add]

/-! ## Helper: value extraction for `allGatherPrimDimN` along dim 2 of `[1,8,8]` shards. -/

private lemma allGather_dim2_valAt_1_8_8_4 (xs : List Tensor)
    (hh : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 8])
    (idx : Nat) (hidx : idx < 256) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
      valAt (xs.getD (idx % 32 / 8) (zeroTensor [1, 8, 8]))
        (idx / 32 * 8 + idx % 32 % 8) := by
  have hag_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 32] := by
    have := allGatherPrimDimN_shape 2 4 xs [1, 8, 8] hh
    simpa [List.set, List.getD] using this
  have hidx_lt_prod : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hag_shape]; simpa [prodShape] using hidx
  have h0 : valAt (allGatherPrimDimN 2 4 0 xs) idx =
      (allGatherPrimDimN 2 4 0 xs).val ⟨idx, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  -- Pre-compute list operations on [1,8,8].
  have hgetD2 : (([1, 8, 8] : List Nat).getD 2 0) = 8 := rfl
  have hdrop3 : List.foldl (fun (a b : Nat) => a * b)
      1 (List.drop (2 + 1) ([1, 8, 8] : List Nat)) = 1 := by
    simp [List.drop, List.foldl]
  have h32_ne : (32 : Nat) ≠ 0 := by decide
  have h1_ne : (1 : Nat) ≠ 0 := by decide
  have h8_ne : (8 : Nat) ≠ 0 := by decide
  simp only [allGatherPrimDimN, Tensor.mkShape, hh, hgetD2, hdrop3,
    if_neg h32_ne, if_neg h1_ne, if_neg h8_ne, Nat.mul_one, Nat.div_one, Nat.mod_one,
    Nat.add_zero]

/-! ## Helper: value extraction for `allGatherPrimDimN` along dim 0 of `[8,32]` shards (specific). -/

private lemma allGather_dim0_valAt_8_32_4 (xs : List Tensor) (hxs_len : xs.length = 4)
    (hh : (xs.head?.map (fun t => t.shape)).getD [] = [8, 32])
    (hxs_shape : ∀ w ∈ xs, w.shape = [8, 32])
    (col j : Nat) (hcol : col < 32) (hj : j < 32) :
    valAt (allGatherPrimDimN 0 4 0 xs) (col * 32 + j) =
      valAt (xs.getD (col / 8) (zeroTensor [8, 32])) (col % 8 * 32 + j) := by
  have hgetD : ∀ r, r < 4 → (xs.getD r (zeroTensor [8, 32])).shape = [8, 32] := by
    intro r hr
    rw [List.getD_eq_getElem?_getD]
    have hl : r < xs.length := by omega
    rw [List.getElem?_eq_getElem hl]
    simp only [Option.getD_some]
    exact hxs_shape _ (List.getElem_mem _)
  have hcol_idx : col * 32 + j = (col / 8 * 8 + col % 8) * 32 + j := by
    have h := Nat.div_add_mod col 8; omega
  rw [hcol_idx]
  exact allGatherPrimDimN0_valAt 4 8 32 xs (by omega) (by omega) (by omega) hh hgetD
    (col / 8) (by exact Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by omega))
    (col % 8) (Nat.mod_lt _ (by omega)) j hj

/-! ## Core column-parallel weight-split lemma. -/

private lemma fw_linear_weight_split (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 32])
    (hws_len : ws.length = 4)
    (hws_shape : ∀ w ∈ ws, w.shape = [8, 32]) :
    fw_linear x (allGatherPrimDimN 0 4 0 ws) =
      allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w)) := by
  have hws_head : (ws.head?.map (fun t => t.shape)).getD [] = [8, 32] := by
    cases hws : ws with
    | nil => simp [hws] at hws_len
    | cons w0 _ => simp [hws_shape w0 (by simp [hws])]
  have hws_getD_shape : ∀ r, r < 4 →
      (ws.getD r (zeroTensor [8, 32])).shape = [8, 32] := by
    intro r hr
    rw [List.getD_eq_getElem?_getD]
    have hl : r < ws.length := by omega
    rw [List.getElem?_eq_getElem hl]
    simp only [Option.getD_some]
    exact hws_shape _ (List.getElem_mem _)
  have hwfull_shape : (allGatherPrimDimN 0 4 0 ws).shape = [32, 32] := by
    have := allGatherPrimDimN_shape 0 4 ws [8, 32] hws_head
    simpa [List.set, List.getD] using this
  have hmap_head : ((ws.map (fun w => fw_linear x w)).head?.map (fun t => t.shape)).getD [] =
      [1, 8, 8] := by
    cases hws : ws with
    | nil => simp [hws] at hws_len
    | cons w0 _ =>
        have hw0 : w0.shape = [8, 32] := hws_shape w0 (by simp [hws])
        simp
        exact fw_linear_3d_shape 1 8 32 8 x w0 hx hw0
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 0 4 0 ws)).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 32 32 x _ hx hwfull_shape
  have hRHS_shape : (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))).shape = [1, 8, 32] := by
    have := allGatherPrimDimN_shape 2 4 (ws.map (fun w => fw_linear x w)) [1, 8, 8] hmap_head
    simpa [List.set, List.getD] using this
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx' : idx < 256 := by simpa [prodShape] using hidx
  -- Use the LHS valAt helper (with `o = 32`).
  rw [fw_linear_3d_valAt_1_8_32 x _ 32 hx hwfull_shape (by omega) idx (by omega)]
  -- Use the RHS valAt helper.
  rw [allGather_dim2_valAt_1_8_8_4 _ hmap_head idx hidx']
  -- Replace `(ws.map fwl).getD r _` with `fw_linear x (ws.getD r _)`.
  set r0 := idx % 32 / 8 with hr0_def
  have hr0_lt : r0 < 4 := by
    change idx % 32 / 8 < 4
    apply Nat.div_lt_iff_lt_mul (by omega) |>.mpr
    have := Nat.mod_lt idx (show 0 < 32 from by omega); omega
  have hgetD_map : (ws.map (fun w => fw_linear x w)).getD r0 (zeroTensor [1, 8, 8]) =
      fw_linear x (ws.getD r0 (zeroTensor [8, 32])) := by
    rw [List.getD_eq_getElem?_getD]
    have hl : r0 < (ws.map (fun w => fw_linear x w)).length := by
      rw [List.length_map]; omega
    rw [List.getElem?_eq_getElem hl]
    simp only [Option.getD_some, List.getElem_map]
    rw [List.getD_eq_getElem?_getD]
    have hl' : r0 < ws.length := by omega
    rw [List.getElem?_eq_getElem hl']
    simp only [Option.getD_some]
  rw [hgetD_map]
  have hwsr0_shape : (ws.getD r0 (zeroTensor [8, 32])).shape = [8, 32] := hws_getD_shape r0 hr0_lt
  -- Use the LHS valAt helper again on the piece (`o = 8`).
  have hpiece_idx_lt : idx / 32 * 8 + idx % 32 % 8 < 8 * 8 := by
    have h1 : idx / 32 < 8 := by
      apply Nat.div_lt_iff_lt_mul (by omega) |>.mpr; omega
    have h2 : idx % 32 % 8 < 8 := Nat.mod_lt _ (by omega)
    omega
  rw [fw_linear_3d_valAt_1_8_32 x _ 8 hx hwsr0_shape (by omega)
      (idx / 32 * 8 + idx % 32 % 8) hpiece_idx_lt]
  -- Now both sides are sums over Finset.range 32. Rewrite the LHS access into ws[r0].
  apply Finset.sum_congr rfl
  intro j hj
  have hj_lt : j < 32 := Finset.mem_range.mp hj
  -- Use allGather_dim0_valAt_8_32_4 to split LHS access along `idx % 32`.
  -- LHS summand: valAt x (idx/32*32 + j) * valAt (allGather_dim0 ws) (idx%32 * 32 + j).
  -- RHS summand: valAt x ((idx/32*8+idx%32%8) / 8 * 32 + j) * valAt (ws.getD r0 _) ((idx/32*8+idx%32%8) % 8 * 32 + j).
  have hcol_lt : idx % 32 < 32 := Nat.mod_lt _ (by omega)
  -- Show indices into x are equal: idx/32*32 = (idx/32*8+idx%32%8)/8 * 32.
  have hxidx_eq : idx / 32 * 32 + j = (idx / 32 * 8 + idx % 32 % 8) / 8 * 32 + j := by
    have hmod_lt : idx % 32 % 8 < 8 := Nat.mod_lt _ (by omega)
    have : (idx / 32 * 8 + idx % 32 % 8) / 8 = idx / 32 := by
      rw [show idx / 32 * 8 + idx % 32 % 8 = idx % 32 % 8 + 8 * (idx / 32) from by ring,
          Nat.add_mul_div_left _ _ (by omega : 0 < 8),
          Nat.div_eq_of_lt hmod_lt]
      omega
    rw [this]
  -- Show indices into the weight are equal: valAt (allGather) (col*32+j) = valAt (ws.getD r0 _) (col%8 * 32 + j).
  rw [allGather_dim0_valAt_8_32_4 ws hws_len hws_head hws_shape (idx % 32) j hcol_lt hj_lt]
  -- Now show idx % 32 % 8 = (idx/32*8 + idx%32%8) % 8.
  have hcol_mod_eq : (idx / 32 * 8 + idx % 32 % 8) % 8 = idx % 32 % 8 := by
    rw [show idx / 32 * 8 + idx % 32 % 8 = idx % 32 % 8 + idx / 32 * 8 from by ring,
        Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
  rw [hcol_mod_eq, ← hxidx_eq]

/-! ## SM evaluation lemmas. -/

-- SM positions: 8 (576), 62 (642), 63 (644)
@[reducible] private def sm_n8 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [926, 575], outs := [576] }
@[reducible] private def sm_n62 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1004, 641], outs := [642] }
@[reducible] private def sm_n63 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1008, 643], outs := [644] }

private theorem sm_eval_576 (initSM : Store) :
    denoteGraph sm initSM 576 =
      fw_linear (denoteGraph sm initSM 926) (initSM 575) := by
  have hsub : (denoteGraph sm initSM) 576 =
      (denoteGraph { sm with nodes := sm.nodes.take 9 } initSM) 576 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 576
      (sm.nodes.take 9) (sm.nodes.drop 9)
      (List.take_append_drop 9 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 9 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 8 ++ [sm_n8] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n8] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n8 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n8 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h926 : (denoteGraph { sm with nodes := sm.nodes.take 8 } initSM) 926 =
      (denoteGraph sm initSM) 926 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 926
      (sm.nodes.take 8) (sm.nodes.drop 8)
      (List.take_append_drop 8 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h575 : (denoteGraph { sm with nodes := sm.nodes.take 8 } initSM) 575 = initSM 575 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs sm (sm.nodes.take 8) initSM 575
      (by set_option maxRecDepth 20000 in decide)
  rw [h926, h575]

private theorem sm_eval_642 (initSM : Store) :
    denoteGraph sm initSM 642 =
      fw_linear (denoteGraph sm initSM 1004) (initSM 641) := by
  have hsub : (denoteGraph sm initSM) 642 =
      (denoteGraph { sm with nodes := sm.nodes.take 63 } initSM) 642 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 642
      (sm.nodes.take 63) (sm.nodes.drop 63)
      (List.take_append_drop 63 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 63 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 62 ++ [sm_n62] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n62] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n62 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n62 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h1004 : (denoteGraph { sm with nodes := sm.nodes.take 62 } initSM) 1004 =
      (denoteGraph sm initSM) 1004 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1004
      (sm.nodes.take 62) (sm.nodes.drop 62)
      (List.take_append_drop 62 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h641 : (denoteGraph { sm with nodes := sm.nodes.take 62 } initSM) 641 = initSM 641 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs sm (sm.nodes.take 62) initSM 641
      (by set_option maxRecDepth 20000 in decide)
  rw [h1004, h641]

private theorem sm_eval_644 (initSM : Store) :
    denoteGraph sm initSM 644 =
      fw_linear (denoteGraph sm initSM 1008) (initSM 643) := by
  have hsub : (denoteGraph sm initSM) 644 =
      (denoteGraph { sm with nodes := sm.nodes.take 64 } initSM) 644 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 644
      (sm.nodes.take 64) (sm.nodes.drop 64)
      (List.take_append_drop 64 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 64 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 63 ++ [sm_n63] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n63] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n63 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n63 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h1008 : (denoteGraph { sm with nodes := sm.nodes.take 63 } initSM) 1008 =
      (denoteGraph sm initSM) 1008 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1008
      (sm.nodes.take 63) (sm.nodes.drop 63)
      (List.take_append_drop 63 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h643 : (denoteGraph { sm with nodes := sm.nodes.take 63 } initSM) 643 = initSM 643 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs sm (sm.nodes.take 63) initSM 643
      (by set_option maxRecDepth 20000 in decide)
  rw [h1008, h643]

/-! ## PM evaluation lemmas. -/

@[reducible] private def pm_n50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [917, 1229], outs := [1233] }
@[reducible] private def pm_n51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [917, 1230], outs := [1234] }
@[reducible] private def pm_n52 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [917, 1231], outs := [1235] }
@[reducible] private def pm_n53 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [917, 1232], outs := [1236] }
@[reducible] private def pm_n56 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := ((List.range 4).map (fun r => 1233 + r)), outs := [576], params := [2] }

@[reducible] private def pm_n406 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [999, 2257], outs := [2261] }
@[reducible] private def pm_n407 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [999, 2258], outs := [2262] }
@[reducible] private def pm_n408 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [999, 2259], outs := [2263] }
@[reducible] private def pm_n409 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [999, 2260], outs := [2264] }
@[reducible] private def pm_n410 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1000, 2285], outs := [2289] }
@[reducible] private def pm_n411 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [1000, 2286], outs := [2290] }
@[reducible] private def pm_n412 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [1000, 2287], outs := [2291] }
@[reducible] private def pm_n413 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [1000, 2288], outs := [2292] }
@[reducible] private def pm_n415 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := ((List.range 4).map (fun r => 2261 + r)), outs := [642], params := [2] }
@[reducible] private def pm_n416 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := ((List.range 4).map (fun r => 2289 + r)), outs := [644], params := [2] }

/- Helper: prove `denoteGraph pm initPM tid = fw_linear (denoteGraph pm initPM srcW) (initPM srcX)`
   for a fw_linear node at position `pos+1` (with `pos` = take amount, the node at index `pos`).
   This is structured so the `decide` calls are kept small. -/

/-- Per-piece PM eval for goal_8 / 576: position 50 (1233). -/
private theorem pm_eval_1233 (initPM : Store) :
    denoteGraph pm initPM 1233 = fw_linear (denoteGraph pm initPM 917) (initPM 1229) := by
  have hsub : (denoteGraph pm initPM) 1233 =
      (denoteGraph { pm with nodes := pm.nodes.take 51 } initPM) 1233 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1233
      (pm.nodes.take 51) (pm.nodes.drop 51)
      (List.take_append_drop 51 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 51 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 50 ++ [pm_n50] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n50] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n50 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n50 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h917 : (denoteGraph { pm with nodes := pm.nodes.take 50 } initPM) 917 =
      (denoteGraph pm initPM) 917 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 917
      (pm.nodes.take 50) (pm.nodes.drop 50)
      (List.take_append_drop 50 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1229 : (denoteGraph { pm with nodes := pm.nodes.take 50 } initPM) 1229 = initPM 1229 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 50) initPM 1229
      (by set_option maxRecDepth 20000 in decide)
  rw [h917, h1229]

private theorem pm_eval_1234 (initPM : Store) :
    denoteGraph pm initPM 1234 = fw_linear (denoteGraph pm initPM 917) (initPM 1230) := by
  have hsub : (denoteGraph pm initPM) 1234 =
      (denoteGraph { pm with nodes := pm.nodes.take 52 } initPM) 1234 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1234
      (pm.nodes.take 52) (pm.nodes.drop 52)
      (List.take_append_drop 52 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 52 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 51 ++ [pm_n51] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n51] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n51 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n51 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h917 : (denoteGraph { pm with nodes := pm.nodes.take 51 } initPM) 917 =
      (denoteGraph pm initPM) 917 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 917
      (pm.nodes.take 51) (pm.nodes.drop 51)
      (List.take_append_drop 51 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1230 : (denoteGraph { pm with nodes := pm.nodes.take 51 } initPM) 1230 = initPM 1230 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 51) initPM 1230
      (by set_option maxRecDepth 20000 in decide)
  rw [h917, h1230]

private theorem pm_eval_1235 (initPM : Store) :
    denoteGraph pm initPM 1235 = fw_linear (denoteGraph pm initPM 917) (initPM 1231) := by
  have hsub : (denoteGraph pm initPM) 1235 =
      (denoteGraph { pm with nodes := pm.nodes.take 53 } initPM) 1235 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1235
      (pm.nodes.take 53) (pm.nodes.drop 53)
      (List.take_append_drop 53 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 53 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 52 ++ [pm_n52] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n52] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n52 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n52 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h917 : (denoteGraph { pm with nodes := pm.nodes.take 52 } initPM) 917 =
      (denoteGraph pm initPM) 917 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 917
      (pm.nodes.take 52) (pm.nodes.drop 52)
      (List.take_append_drop 52 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1231 : (denoteGraph { pm with nodes := pm.nodes.take 52 } initPM) 1231 = initPM 1231 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 52) initPM 1231
      (by set_option maxRecDepth 20000 in decide)
  rw [h917, h1231]

private theorem pm_eval_1236 (initPM : Store) :
    denoteGraph pm initPM 1236 = fw_linear (denoteGraph pm initPM 917) (initPM 1232) := by
  have hsub : (denoteGraph pm initPM) 1236 =
      (denoteGraph { pm with nodes := pm.nodes.take 54 } initPM) 1236 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1236
      (pm.nodes.take 54) (pm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 54 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 53 ++ [pm_n53] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n53] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n53 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n53 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h917 : (denoteGraph { pm with nodes := pm.nodes.take 53 } initPM) 917 =
      (denoteGraph pm initPM) 917 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 917
      (pm.nodes.take 53) (pm.nodes.drop 53)
      (List.take_append_drop 53 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1232 : (denoteGraph { pm with nodes := pm.nodes.take 53 } initPM) 1232 = initPM 1232 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 53) initPM 1232
      (by set_option maxRecDepth 20000 in decide)
  rw [h917, h1232]

private theorem pm_eval_576 (initPM : Store) :
    denoteGraph pm initPM 576 =
      allGatherPrimDimN 2 4 0
        [denoteGraph pm initPM 1233, denoteGraph pm initPM 1234,
         denoteGraph pm initPM 1235, denoteGraph pm initPM 1236] := by
  have hsub : (denoteGraph pm initPM) 576 =
      (denoteGraph { pm with nodes := pm.nodes.take 57 } initPM) 576 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 576
      (pm.nodes.take 57) (pm.nodes.drop 57)
      (List.take_append_drop 57 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 57 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 56 ++ [pm_n56] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n56] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n56 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n56 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  rw [show ((List.range 4).map (fun r => 1233 + r)) = [1233, 1234, 1235, 1236] from rfl]
  simp only [List.map_cons, List.map_nil]
  have h1233 : (denoteGraph { pm with nodes := pm.nodes.take 56 } initPM) 1233 =
      (denoteGraph pm initPM) 1233 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1233
      (pm.nodes.take 56) (pm.nodes.drop 56)
      (List.take_append_drop 56 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1234 : (denoteGraph { pm with nodes := pm.nodes.take 56 } initPM) 1234 =
      (denoteGraph pm initPM) 1234 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1234
      (pm.nodes.take 56) (pm.nodes.drop 56)
      (List.take_append_drop 56 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1235 : (denoteGraph { pm with nodes := pm.nodes.take 56 } initPM) 1235 =
      (denoteGraph pm initPM) 1235 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1235
      (pm.nodes.take 56) (pm.nodes.drop 56)
      (List.take_append_drop 56 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h1236 : (denoteGraph { pm with nodes := pm.nodes.take 56 } initPM) 1236 =
      (denoteGraph pm initPM) 1236 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1236
      (pm.nodes.take 56) (pm.nodes.drop 56)
      (List.take_append_drop 56 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h1233, h1234, h1235, h1236]
  rfl

private theorem pm_eval_2261 (initPM : Store) :
    denoteGraph pm initPM 2261 = fw_linear (denoteGraph pm initPM 999) (initPM 2257) := by
  have hsub : (denoteGraph pm initPM) 2261 =
      (denoteGraph { pm with nodes := pm.nodes.take 407 } initPM) 2261 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2261
      (pm.nodes.take 407) (pm.nodes.drop 407)
      (List.take_append_drop 407 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 407 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 406 ++ [pm_n406] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n406] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n406 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n406 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h999 : (denoteGraph { pm with nodes := pm.nodes.take 406 } initPM) 999 =
      (denoteGraph pm initPM) 999 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 999
      (pm.nodes.take 406) (pm.nodes.drop 406)
      (List.take_append_drop 406 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2257 : (denoteGraph { pm with nodes := pm.nodes.take 406 } initPM) 2257 = initPM 2257 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 406) initPM 2257
      (by set_option maxRecDepth 20000 in decide)
  rw [h999, h2257]

private theorem pm_eval_2262 (initPM : Store) :
    denoteGraph pm initPM 2262 = fw_linear (denoteGraph pm initPM 999) (initPM 2258) := by
  have hsub : (denoteGraph pm initPM) 2262 =
      (denoteGraph { pm with nodes := pm.nodes.take 408 } initPM) 2262 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2262
      (pm.nodes.take 408) (pm.nodes.drop 408)
      (List.take_append_drop 408 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 408 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 407 ++ [pm_n407] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n407] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n407 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n407 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h999 : (denoteGraph { pm with nodes := pm.nodes.take 407 } initPM) 999 =
      (denoteGraph pm initPM) 999 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 999
      (pm.nodes.take 407) (pm.nodes.drop 407)
      (List.take_append_drop 407 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2258 : (denoteGraph { pm with nodes := pm.nodes.take 407 } initPM) 2258 = initPM 2258 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 407) initPM 2258
      (by set_option maxRecDepth 20000 in decide)
  rw [h999, h2258]

private theorem pm_eval_2263 (initPM : Store) :
    denoteGraph pm initPM 2263 = fw_linear (denoteGraph pm initPM 999) (initPM 2259) := by
  have hsub : (denoteGraph pm initPM) 2263 =
      (denoteGraph { pm with nodes := pm.nodes.take 409 } initPM) 2263 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2263
      (pm.nodes.take 409) (pm.nodes.drop 409)
      (List.take_append_drop 409 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 409 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 408 ++ [pm_n408] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n408] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n408 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n408 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h999 : (denoteGraph { pm with nodes := pm.nodes.take 408 } initPM) 999 =
      (denoteGraph pm initPM) 999 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 999
      (pm.nodes.take 408) (pm.nodes.drop 408)
      (List.take_append_drop 408 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2259 : (denoteGraph { pm with nodes := pm.nodes.take 408 } initPM) 2259 = initPM 2259 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 408) initPM 2259
      (by set_option maxRecDepth 20000 in decide)
  rw [h999, h2259]

private theorem pm_eval_2264 (initPM : Store) :
    denoteGraph pm initPM 2264 = fw_linear (denoteGraph pm initPM 999) (initPM 2260) := by
  have hsub : (denoteGraph pm initPM) 2264 =
      (denoteGraph { pm with nodes := pm.nodes.take 410 } initPM) 2264 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2264
      (pm.nodes.take 410) (pm.nodes.drop 410)
      (List.take_append_drop 410 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 410 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 409 ++ [pm_n409] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n409] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n409 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n409 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h999 : (denoteGraph { pm with nodes := pm.nodes.take 409 } initPM) 999 =
      (denoteGraph pm initPM) 999 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 999
      (pm.nodes.take 409) (pm.nodes.drop 409)
      (List.take_append_drop 409 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2260 : (denoteGraph { pm with nodes := pm.nodes.take 409 } initPM) 2260 = initPM 2260 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 409) initPM 2260
      (by set_option maxRecDepth 20000 in decide)
  rw [h999, h2260]

private theorem pm_eval_2289 (initPM : Store) :
    denoteGraph pm initPM 2289 = fw_linear (denoteGraph pm initPM 1000) (initPM 2285) := by
  have hsub : (denoteGraph pm initPM) 2289 =
      (denoteGraph { pm with nodes := pm.nodes.take 411 } initPM) 2289 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2289
      (pm.nodes.take 411) (pm.nodes.drop 411)
      (List.take_append_drop 411 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 411 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 410 ++ [pm_n410] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n410] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n410 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n410 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h1000 : (denoteGraph { pm with nodes := pm.nodes.take 410 } initPM) 1000 =
      (denoteGraph pm initPM) 1000 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1000
      (pm.nodes.take 410) (pm.nodes.drop 410)
      (List.take_append_drop 410 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2285 : (denoteGraph { pm with nodes := pm.nodes.take 410 } initPM) 2285 = initPM 2285 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 410) initPM 2285
      (by set_option maxRecDepth 20000 in decide)
  rw [h1000, h2285]

private theorem pm_eval_2290 (initPM : Store) :
    denoteGraph pm initPM 2290 = fw_linear (denoteGraph pm initPM 1000) (initPM 2286) := by
  have hsub : (denoteGraph pm initPM) 2290 =
      (denoteGraph { pm with nodes := pm.nodes.take 412 } initPM) 2290 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2290
      (pm.nodes.take 412) (pm.nodes.drop 412)
      (List.take_append_drop 412 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 412 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 411 ++ [pm_n411] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n411] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n411 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n411 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h1000 : (denoteGraph { pm with nodes := pm.nodes.take 411 } initPM) 1000 =
      (denoteGraph pm initPM) 1000 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1000
      (pm.nodes.take 411) (pm.nodes.drop 411)
      (List.take_append_drop 411 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2286 : (denoteGraph { pm with nodes := pm.nodes.take 411 } initPM) 2286 = initPM 2286 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 411) initPM 2286
      (by set_option maxRecDepth 20000 in decide)
  rw [h1000, h2286]

private theorem pm_eval_2291 (initPM : Store) :
    denoteGraph pm initPM 2291 = fw_linear (denoteGraph pm initPM 1000) (initPM 2287) := by
  have hsub : (denoteGraph pm initPM) 2291 =
      (denoteGraph { pm with nodes := pm.nodes.take 413 } initPM) 2291 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2291
      (pm.nodes.take 413) (pm.nodes.drop 413)
      (List.take_append_drop 413 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 413 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 412 ++ [pm_n412] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n412] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n412 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n412 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h1000 : (denoteGraph { pm with nodes := pm.nodes.take 412 } initPM) 1000 =
      (denoteGraph pm initPM) 1000 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1000
      (pm.nodes.take 412) (pm.nodes.drop 412)
      (List.take_append_drop 412 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2287 : (denoteGraph { pm with nodes := pm.nodes.take 412 } initPM) 2287 = initPM 2287 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 412) initPM 2287
      (by set_option maxRecDepth 20000 in decide)
  rw [h1000, h2287]

private theorem pm_eval_2292 (initPM : Store) :
    denoteGraph pm initPM 2292 = fw_linear (denoteGraph pm initPM 1000) (initPM 2288) := by
  have hsub : (denoteGraph pm initPM) 2292 =
      (denoteGraph { pm with nodes := pm.nodes.take 414 } initPM) 2292 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2292
      (pm.nodes.take 414) (pm.nodes.drop 414)
      (List.take_append_drop 414 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 414 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 413 ++ [pm_n413] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n413] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n413 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n413 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_linear_out]
  have h1000 : (denoteGraph { pm with nodes := pm.nodes.take 413 } initPM) 1000 =
      (denoteGraph pm initPM) 1000 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1000
      (pm.nodes.take 413) (pm.nodes.drop 413)
      (List.take_append_drop 413 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2288 : (denoteGraph { pm with nodes := pm.nodes.take 413 } initPM) 2288 = initPM 2288 :=
    denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 413) initPM 2288
      (by set_option maxRecDepth 20000 in decide)
  rw [h1000, h2288]

private theorem pm_eval_642 (initPM : Store) :
    denoteGraph pm initPM 642 =
      allGatherPrimDimN 2 4 0
        [denoteGraph pm initPM 2261, denoteGraph pm initPM 2262,
         denoteGraph pm initPM 2263, denoteGraph pm initPM 2264] := by
  have hsub : (denoteGraph pm initPM) 642 =
      (denoteGraph { pm with nodes := pm.nodes.take 416 } initPM) 642 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 642
      (pm.nodes.take 416) (pm.nodes.drop 416)
      (List.take_append_drop 416 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 416 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 415 ++ [pm_n415] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n415] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n415 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n415 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  rw [show ((List.range 4).map (fun r => 2261 + r)) = [2261, 2262, 2263, 2264] from rfl]
  simp only [List.map_cons, List.map_nil]
  have h2261 : (denoteGraph { pm with nodes := pm.nodes.take 415 } initPM) 2261 =
      (denoteGraph pm initPM) 2261 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2261
      (pm.nodes.take 415) (pm.nodes.drop 415)
      (List.take_append_drop 415 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2262 : (denoteGraph { pm with nodes := pm.nodes.take 415 } initPM) 2262 =
      (denoteGraph pm initPM) 2262 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2262
      (pm.nodes.take 415) (pm.nodes.drop 415)
      (List.take_append_drop 415 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2263 : (denoteGraph { pm with nodes := pm.nodes.take 415 } initPM) 2263 =
      (denoteGraph pm initPM) 2263 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2263
      (pm.nodes.take 415) (pm.nodes.drop 415)
      (List.take_append_drop 415 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2264 : (denoteGraph { pm with nodes := pm.nodes.take 415 } initPM) 2264 =
      (denoteGraph pm initPM) 2264 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2264
      (pm.nodes.take 415) (pm.nodes.drop 415)
      (List.take_append_drop 415 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h2261, h2262, h2263, h2264]
  rfl

private theorem pm_eval_644 (initPM : Store) :
    denoteGraph pm initPM 644 =
      allGatherPrimDimN 2 4 0
        [denoteGraph pm initPM 2289, denoteGraph pm initPM 2290,
         denoteGraph pm initPM 2291, denoteGraph pm initPM 2292] := by
  have hsub : (denoteGraph pm initPM) 644 =
      (denoteGraph { pm with nodes := pm.nodes.take 417 } initPM) 644 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 644
      (pm.nodes.take 417) (pm.nodes.drop 417)
      (List.take_append_drop 417 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 417 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 416 ++ [pm_n416] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n416] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n416 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n416 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  rw [show ((List.range 4).map (fun r => 2289 + r)) = [2289, 2290, 2291, 2292] from rfl]
  simp only [List.map_cons, List.map_nil]
  have h2289 : (denoteGraph { pm with nodes := pm.nodes.take 416 } initPM) 2289 =
      (denoteGraph pm initPM) 2289 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2289
      (pm.nodes.take 416) (pm.nodes.drop 416)
      (List.take_append_drop 416 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2290 : (denoteGraph { pm with nodes := pm.nodes.take 416 } initPM) 2290 =
      (denoteGraph pm initPM) 2290 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2290
      (pm.nodes.take 416) (pm.nodes.drop 416)
      (List.take_append_drop 416 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2291 : (denoteGraph { pm with nodes := pm.nodes.take 416 } initPM) 2291 =
      (denoteGraph pm initPM) 2291 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2291
      (pm.nodes.take 416) (pm.nodes.drop 416)
      (List.take_append_drop 416 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h2292 : (denoteGraph { pm with nodes := pm.nodes.take 416 } initPM) 2292 =
      (denoteGraph pm initPM) 2292 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2292
      (pm.nodes.take 416) (pm.nodes.drop 416)
      (List.take_append_drop 416 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h2289, h2290, h2291, h2292]
  rfl

/-! ## Main theorem. -/

theorem prove_pattern_7 : pattern_7_stmt := by
  intro target h
  cases h
  all_goals (
    intro initSM initPM hSmInit hPmInit hInitGoals)
  -- Bridge patterns provide SM 926 = PM 917, SM 1004 = PM 999, SM 1008 = PM 1000.
  all_goals (
    have h265 := prove_pattern_131 (target := goal_265_stmt) .goal_265
    have h289 := prove_pattern_139 (target := goal_289_stmt) .goal_289
    have h291 := prove_pattern_140 (target := goal_291_stmt) .goal_291
    have hg265 := h265 initSM initPM hSmInit hPmInit hInitGoals
    have hg289 := h289 initSM initPM hSmInit hPmInit hInitGoals
    have hg291 := h291 initSM initPM hSmInit hPmInit hInitGoals
    have hSM926_eq_PM917 : denoteGraph sm initSM 926 = denoteGraph pm initPM 917 := by
      have hh := hg265.2.2
      simp only [goal_265, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    have hSM1004_eq_PM999 : denoteGraph sm initSM 1004 = denoteGraph pm initPM 999 := by
      have hh := hg289.2.2
      simp only [goal_289, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    have hSM1008_eq_PM1000 : denoteGraph sm initSM 1008 = denoteGraph pm initPM 1000 := by
      have hh := hg291.2.2
      simp only [goal_291, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    -- Shape facts for SM/PM 917/999/1000.
    have h917_shape : (denoteGraph pm initPM 917).shape = [1, 8, 32] := by
      have hh := hg265.2.1
      simp only [goal_265, List.map_cons, List.map_nil, List.cons.injEq] at hh
      exact hh.1
    have h999_shape : (denoteGraph pm initPM 999).shape = [1, 8, 32] := by
      have hh := hg289.2.1
      simp only [goal_289, List.map_cons, List.map_nil, List.cons.injEq] at hh
      exact hh.1
    have h1000_shape : (denoteGraph pm initPM 1000).shape = [1, 8, 32] := by
      have hh := hg291.2.1
      simp only [goal_291, List.map_cons, List.map_nil, List.cons.injEq] at hh
      exact hh.1)
  -- Goal 8: ts=576, single tp=576.
  · -- initGoal_575 unpacking
    have hInit575 : InitGoalHolds pm.numRanks initGoal_575 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    obtain ⟨hSh575_sm, hSh575_pm, hRec575⟩ := hInit575
    have h575_sm_sh : (initSM 575).shape = [32, 32] := by
      simpa [initGoal_575] using hSh575_sm
    have h575_pm_shapes : ∀ p ∈ initGoal_575.tps, (initPM p.tid).shape = [8, 32] := by
      have hh := hSh575_pm
      simp only [initGoal_575, List.map_cons, List.map_nil, List.cons.injEq] at hh
      intro p hp
      simp [initGoal_575] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp_all
    have h1229_sh : (initPM 1229).shape = [8, 32] := h575_pm_shapes { rank := 0, tid := 1229 } (by simp [initGoal_575])
    have h1230_sh : (initPM 1230).shape = [8, 32] := h575_pm_shapes { rank := 1, tid := 1230 } (by simp [initGoal_575])
    have h1231_sh : (initPM 1231).shape = [8, 32] := h575_pm_shapes { rank := 2, tid := 1231 } (by simp [initGoal_575])
    have h1232_sh : (initPM 1232).shape = [8, 32] := h575_pm_shapes { rank := 3, tid := 1232 } (by simp [initGoal_575])
    -- initSM 575 = allGather_dim0 [initPM 1229, ..., 1232].
    have h575_eq : initSM 575 = allGatherPrimDimN 0 4 0
        [initPM 1229, initPM 1230, initPM 1231, initPM 1232] := by
      have hh := hRec575
      simp only [initGoal_575, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [h1229_sh]; decide)]
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 576).shape = [1, 8, 32]
      rw [sm_eval_576]
      rw [hSM926_eq_PM917]
      rw [h575_eq]
      have hws_head : (([initPM 1229, initPM 1230, initPM 1231, initPM 1232].head?.map
          (fun t => t.shape)).getD []) = [8, 32] := by simp [h1229_sh]
      have hws_full_shape : (allGatherPrimDimN 0 4 0
          [initPM 1229, initPM 1230, initPM 1231, initPM 1232]).shape = [32, 32] := by
        rw [allGatherPrimDimN_shape 0 4 _ _ hws_head]
        simp [List.set, List.getD]
      rw [fw_linear_3d_shape 1 8 32 32 _ _ h917_shape hws_full_shape]
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 576 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 32]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_576, pm_eval_1233, pm_eval_1234, pm_eval_1235, pm_eval_1236]
      have hf_sh : ∀ w : Tensor, w.shape = [8, 32] →
          (fw_linear (denoteGraph pm initPM 917) w).shape = [1, 8, 8] := by
        intro w hw; rw [fw_linear_3d_shape 1 8 32 8 _ _ h917_shape hw]
      have hhead : (([fw_linear (denoteGraph pm initPM 917) (initPM 1229),
          fw_linear (denoteGraph pm initPM 917) (initPM 1230),
          fw_linear (denoteGraph pm initPM 917) (initPM 1231),
          fw_linear (denoteGraph pm initPM 917) (initPM 1232)].head?.map
          (fun t => t.shape)).getD []) = [1, 8, 8] := by
        simp [hf_sh _ h1229_sh]
      rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
      simp [List.set, List.getD]
    · show denoteGraph sm initSM 576 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 576 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_576, pm_eval_576]
      rw [pm_eval_1233, pm_eval_1234, pm_eval_1235, pm_eval_1236]
      rw [hSM926_eq_PM917, h575_eq]
      have hws_shape : ∀ w ∈ [initPM 1229, initPM 1230, initPM 1231, initPM 1232],
          w.shape = [8, 32] := by
        intro w hw
        simp at hw
        rcases hw with rfl | rfl | rfl | rfl <;> assumption
      have := fw_linear_weight_split (denoteGraph pm initPM 917)
        [initPM 1229, initPM 1230, initPM 1231, initPM 1232]
        h917_shape (by simp) hws_shape
      simp at this
      exact this
  -- Goal 56: ts=642, single tp=642.
  · have hInit641 : InitGoalHolds pm.numRanks initGoal_641 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    obtain ⟨hSh641_sm, hSh641_pm, hRec641⟩ := hInit641
    have h641_sm_sh : (initSM 641).shape = [32, 32] := by
      simpa [initGoal_641] using hSh641_sm
    have h641_pm_shapes : ∀ p ∈ initGoal_641.tps, (initPM p.tid).shape = [8, 32] := by
      have hh := hSh641_pm
      simp only [initGoal_641, List.map_cons, List.map_nil, List.cons.injEq] at hh
      intro p hp
      simp [initGoal_641] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp_all
    have h2257_sh : (initPM 2257).shape = [8, 32] := h641_pm_shapes { rank := 0, tid := 2257 } (by simp [initGoal_641])
    have h2258_sh : (initPM 2258).shape = [8, 32] := h641_pm_shapes { rank := 1, tid := 2258 } (by simp [initGoal_641])
    have h2259_sh : (initPM 2259).shape = [8, 32] := h641_pm_shapes { rank := 2, tid := 2259 } (by simp [initGoal_641])
    have h2260_sh : (initPM 2260).shape = [8, 32] := h641_pm_shapes { rank := 3, tid := 2260 } (by simp [initGoal_641])
    have h641_eq : initSM 641 = allGatherPrimDimN 0 4 0
        [initPM 2257, initPM 2258, initPM 2259, initPM 2260] := by
      have hh := hRec641
      simp only [initGoal_641, List.map_cons, List.map_nil] at hh
      rw [hh]; rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [h2257_sh]; decide)]
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 642).shape = [1, 8, 32]
      rw [sm_eval_642, hSM1004_eq_PM999, h641_eq]
      have hws_head : (([initPM 2257, initPM 2258, initPM 2259, initPM 2260].head?.map
          (fun t => t.shape)).getD []) = [8, 32] := by simp [h2257_sh]
      have hws_full_shape : (allGatherPrimDimN 0 4 0
          [initPM 2257, initPM 2258, initPM 2259, initPM 2260]).shape = [32, 32] := by
        rw [allGatherPrimDimN_shape 0 4 _ _ hws_head]
        simp [List.set, List.getD]
      rw [fw_linear_3d_shape 1 8 32 32 _ _ h999_shape hws_full_shape]
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 642 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 32]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_642, pm_eval_2261, pm_eval_2262, pm_eval_2263, pm_eval_2264]
      have hf_sh : ∀ w : Tensor, w.shape = [8, 32] →
          (fw_linear (denoteGraph pm initPM 999) w).shape = [1, 8, 8] := by
        intro w hw; rw [fw_linear_3d_shape 1 8 32 8 _ _ h999_shape hw]
      have hhead : (([fw_linear (denoteGraph pm initPM 999) (initPM 2257),
          fw_linear (denoteGraph pm initPM 999) (initPM 2258),
          fw_linear (denoteGraph pm initPM 999) (initPM 2259),
          fw_linear (denoteGraph pm initPM 999) (initPM 2260)].head?.map
          (fun t => t.shape)).getD []) = [1, 8, 8] := by
        simp [hf_sh _ h2257_sh]
      rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
      simp [List.set, List.getD]
    · show denoteGraph sm initSM 642 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 642 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_642, pm_eval_642]
      rw [pm_eval_2261, pm_eval_2262, pm_eval_2263, pm_eval_2264]
      rw [hSM1004_eq_PM999, h641_eq]
      have hws_shape : ∀ w ∈ [initPM 2257, initPM 2258, initPM 2259, initPM 2260],
          w.shape = [8, 32] := by
        intro w hw
        simp at hw
        rcases hw with rfl | rfl | rfl | rfl <;> assumption
      have := fw_linear_weight_split (denoteGraph pm initPM 999)
        [initPM 2257, initPM 2258, initPM 2259, initPM 2260]
        h999_shape (by simp) hws_shape
      simp at this
      exact this
  -- Goal 57: ts=644, single tp=644.
  · have hInit643 : InitGoalHolds pm.numRanks initGoal_643 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    obtain ⟨hSh643_sm, hSh643_pm, hRec643⟩ := hInit643
    have h643_sm_sh : (initSM 643).shape = [32, 32] := by
      simpa [initGoal_643] using hSh643_sm
    have h643_pm_shapes : ∀ p ∈ initGoal_643.tps, (initPM p.tid).shape = [8, 32] := by
      have hh := hSh643_pm
      simp only [initGoal_643, List.map_cons, List.map_nil, List.cons.injEq] at hh
      intro p hp
      simp [initGoal_643] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp_all
    have h2285_sh : (initPM 2285).shape = [8, 32] := h643_pm_shapes { rank := 0, tid := 2285 } (by simp [initGoal_643])
    have h2286_sh : (initPM 2286).shape = [8, 32] := h643_pm_shapes { rank := 1, tid := 2286 } (by simp [initGoal_643])
    have h2287_sh : (initPM 2287).shape = [8, 32] := h643_pm_shapes { rank := 2, tid := 2287 } (by simp [initGoal_643])
    have h2288_sh : (initPM 2288).shape = [8, 32] := h643_pm_shapes { rank := 3, tid := 2288 } (by simp [initGoal_643])
    have h643_eq : initSM 643 = allGatherPrimDimN 0 4 0
        [initPM 2285, initPM 2286, initPM 2287, initPM 2288] := by
      have hh := hRec643
      simp only [initGoal_643, List.map_cons, List.map_nil] at hh
      rw [hh]; rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [h2285_sh]; decide)]
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 644).shape = [1, 8, 32]
      rw [sm_eval_644, hSM1008_eq_PM1000, h643_eq]
      have hws_head : (([initPM 2285, initPM 2286, initPM 2287, initPM 2288].head?.map
          (fun t => t.shape)).getD []) = [8, 32] := by simp [h2285_sh]
      have hws_full_shape : (allGatherPrimDimN 0 4 0
          [initPM 2285, initPM 2286, initPM 2287, initPM 2288]).shape = [32, 32] := by
        rw [allGatherPrimDimN_shape 0 4 _ _ hws_head]
        simp [List.set, List.getD]
      rw [fw_linear_3d_shape 1 8 32 32 _ _ h1000_shape hws_full_shape]
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 644 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 32]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_644, pm_eval_2289, pm_eval_2290, pm_eval_2291, pm_eval_2292]
      have hf_sh : ∀ w : Tensor, w.shape = [8, 32] →
          (fw_linear (denoteGraph pm initPM 1000) w).shape = [1, 8, 8] := by
        intro w hw; rw [fw_linear_3d_shape 1 8 32 8 _ _ h1000_shape hw]
      have hhead : (([fw_linear (denoteGraph pm initPM 1000) (initPM 2285),
          fw_linear (denoteGraph pm initPM 1000) (initPM 2286),
          fw_linear (denoteGraph pm initPM 1000) (initPM 2287),
          fw_linear (denoteGraph pm initPM 1000) (initPM 2288)].head?.map
          (fun t => t.shape)).getD []) = [1, 8, 8] := by
        simp [hf_sh _ h2285_sh]
      rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
      simp [List.set, List.getD]
    · show denoteGraph sm initSM 644 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 644 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_644, pm_eval_644]
      rw [pm_eval_2289, pm_eval_2290, pm_eval_2291, pm_eval_2292]
      rw [hSM1008_eq_PM1000, h643_eq]
      have hws_shape : ∀ w ∈ [initPM 2285, initPM 2286, initPM 2287, initPM 2288],
          w.shape = [8, 32] := by
        intro w hw
        simp at hw
        rcases hw with rfl | rfl | rfl | rfl <;> assumption
      have := fw_linear_weight_split (denoteGraph pm initPM 1000)
        [initPM 2285, initPM 2286, initPM 2287, initPM 2288]
        h1000_shape (by simp) hws_shape
      simp at this
      exact this

end TrainVerify.Denote.GeneratedPatterns
