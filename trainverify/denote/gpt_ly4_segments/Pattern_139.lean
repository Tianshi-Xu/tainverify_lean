/- Auto-generated pattern proof file.
   Pattern: 139
   Hash: bf5f66fa5be72f0a
   Goals: 289
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_139_goalIds : List Nat := [289]
inductive pattern_139_target : Prop → Prop
  | goal_289 : pattern_139_target goal_289_stmt

def pattern_139_stmt : Prop :=
  ∀ {target : Prop}, pattern_139_target target → target

set_option maxRecDepth 32768

/-! ## `FW_multiref` first-output helper for `params := [3]`.
    Analogous to the existing `applyNode_fw_multiref2_first_out`. -/
private theorem applyNode_fw_multiref3_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2, t3], params := [3] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl,
      evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3].zip (List.replicate 3 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ## Per-goal NodeDecls. -/

@[reducible] private def n_sm_p139_289 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [640], outs := [1004, 1008, 1012], params := [3] }
@[reducible] private def n_pm_p139_289_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [2229], outs := [3607, 3609, 2313], params := [3] }
@[reducible] private def n_pm_p139_289_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [2230], outs := [3617, 3619, 2314], params := [3] }
@[reducible] private def n_pm_p139_289_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_multiref", ins := [2231], outs := [3627, 3629, 2315], params := [3] }
@[reducible] private def n_pm_p139_289_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_multiref", ins := [2232], outs := [3637, 3639, 2316], params := [3] }
@[reducible] private def n_pm_p139_289_ag : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [3607, 3617, 3627, 3637], outs := [999], params := [1] }

/-! ## SM eval: tid 1004 = SM[640] (because FW_multiref's first output is identity). -/

set_option maxHeartbeats 4000000 in
private theorem sm_eval_1004 (initSM : Store) :
    denoteGraph sm initSM 1004 = denoteGraph sm initSM 640 := by
  have hsub : (denoteGraph sm initSM) 1004 =
      (denoteGraph { sm with nodes := sm.nodes.take 62 } initSM) 1004 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1004
      (sm.nodes.take 62) (sm.nodes.drop 62)
      (List.take_append_drop 62 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 62 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 61 ++ [n_sm_p139_289] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [n_sm_p139_289] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n_sm_p139_289 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm n_sm_p139_289 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_sm_p139_289 =
      ({ rank := 0, op := "OpName.FW_multiref", ins := [640],
         outs := [1004, 1008, 1012], params := [3] } : NodeDecl) from rfl,
      applyNode_fw_multiref3_first_out]
  -- Now need: denoteGraph (sm with take 61) initSM 640 = denoteGraph sm initSM 640.
  have hX : denoteGraph { sm with nodes := sm.nodes.take 61 } initSM 640 =
      denoteGraph sm initSM 640 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 640
      (sm.nodes.take 61) (sm.nodes.drop 61)
      (List.take_append_drop 61 _).symm
      (by set_option maxRecDepth 20000 in decide)
  exact hX

/-! ## PM eval: rank r FW_multiref first output. -/

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3607 (initPM : Store) :
    denoteGraph pm initPM 3607 = denoteGraph pm initPM 2229 := by
  have hsub : (denoteGraph pm initPM) 3607 =
      (denoteGraph { pm with nodes := pm.nodes.take 397 } initPM) 3607 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3607
      (pm.nodes.take 397) (pm.nodes.drop 397)
      (List.take_append_drop 397 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 397 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 396 ++ [n_pm_p139_289_0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p139_289_0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p139_289_0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p139_289_0 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p139_289_0 =
      ({ rank := 0, op := "OpName.FW_multiref", ins := [2229],
         outs := [3607, 3609, 2313], params := [3] } : NodeDecl) from rfl,
      applyNode_fw_multiref3_first_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 396 } initPM 2229 =
      denoteGraph pm initPM 2229 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2229
      (pm.nodes.take 396) (pm.nodes.drop 396)
      (List.take_append_drop 396 _).symm
      (by set_option maxRecDepth 20000 in decide)
  exact hI

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3617 (initPM : Store) :
    denoteGraph pm initPM 3617 = denoteGraph pm initPM 2230 := by
  have hsub : (denoteGraph pm initPM) 3617 =
      (denoteGraph { pm with nodes := pm.nodes.take 398 } initPM) 3617 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3617
      (pm.nodes.take 398) (pm.nodes.drop 398)
      (List.take_append_drop 398 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 398 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 397 ++ [n_pm_p139_289_1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p139_289_1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p139_289_1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p139_289_1 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p139_289_1 =
      ({ rank := 1, op := "OpName.FW_multiref", ins := [2230],
         outs := [3617, 3619, 2314], params := [3] } : NodeDecl) from rfl,
      applyNode_fw_multiref3_first_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 397 } initPM 2230 =
      denoteGraph pm initPM 2230 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2230
      (pm.nodes.take 397) (pm.nodes.drop 397)
      (List.take_append_drop 397 _).symm
      (by set_option maxRecDepth 20000 in decide)
  exact hI

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3627 (initPM : Store) :
    denoteGraph pm initPM 3627 = denoteGraph pm initPM 2231 := by
  have hsub : (denoteGraph pm initPM) 3627 =
      (denoteGraph { pm with nodes := pm.nodes.take 399 } initPM) 3627 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3627
      (pm.nodes.take 399) (pm.nodes.drop 399)
      (List.take_append_drop 399 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 399 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 398 ++ [n_pm_p139_289_2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p139_289_2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p139_289_2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p139_289_2 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p139_289_2 =
      ({ rank := 2, op := "OpName.FW_multiref", ins := [2231],
         outs := [3627, 3629, 2315], params := [3] } : NodeDecl) from rfl,
      applyNode_fw_multiref3_first_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 398 } initPM 2231 =
      denoteGraph pm initPM 2231 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2231
      (pm.nodes.take 398) (pm.nodes.drop 398)
      (List.take_append_drop 398 _).symm
      (by set_option maxRecDepth 20000 in decide)
  exact hI

set_option maxHeartbeats 4000000 in
private theorem pm_eval_3637 (initPM : Store) :
    denoteGraph pm initPM 3637 = denoteGraph pm initPM 2232 := by
  have hsub : (denoteGraph pm initPM) 3637 =
      (denoteGraph { pm with nodes := pm.nodes.take 400 } initPM) 3637 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3637
      (pm.nodes.take 400) (pm.nodes.drop 400)
      (List.take_append_drop 400 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 400 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 399 ++ [n_pm_p139_289_3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p139_289_3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p139_289_3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p139_289_3 []]
  rw [denoteGraph_nodes_nil]
  rw [show n_pm_p139_289_3 =
      ({ rank := 3, op := "OpName.FW_multiref", ins := [2232],
         outs := [3637, 3639, 2316], params := [3] } : NodeDecl) from rfl,
      applyNode_fw_multiref3_first_out]
  have hI : denoteGraph { pm with nodes := pm.nodes.take 399 } initPM 2232 =
      denoteGraph pm initPM 2232 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2232
      (pm.nodes.take 399) (pm.nodes.drop 399)
      (List.take_append_drop 399 _).symm
      (by set_option maxRecDepth 20000 in decide)
  exact hI

/-! ## PM eval: tid 999 = AllGatherPrim of [3607, 3617, 3627, 3637]. -/

set_option maxHeartbeats 4000000 in
private theorem pm_eval_ag_999 (initPM : Store) :
    denoteGraph pm initPM 999 =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 3607, denoteGraph pm initPM 3617,
         denoteGraph pm initPM 3627, denoteGraph pm initPM 3637] := by
  have hsub : (denoteGraph pm initPM) 999 =
      (denoteGraph { pm with nodes := pm.nodes.take 404 } initPM) 999 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 999
      (pm.nodes.take 404) (pm.nodes.drop 404)
      (List.take_append_drop 404 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 404 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 403 ++ [n_pm_p139_289_ag] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [n_pm_p139_289_ag] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n_pm_p139_289_ag :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm n_pm_p139_289_ag []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_allGatherPrimDimN_out]
  simp only [List.map_cons, List.map_nil]
  have h3607 : (denoteGraph { pm with nodes := pm.nodes.take 403 } initPM) 3607 =
      (denoteGraph pm initPM) 3607 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3607
      (pm.nodes.take 403) (pm.nodes.drop 403)
      (List.take_append_drop 403 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h3617 : (denoteGraph { pm with nodes := pm.nodes.take 403 } initPM) 3617 =
      (denoteGraph pm initPM) 3617 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3617
      (pm.nodes.take 403) (pm.nodes.drop 403)
      (List.take_append_drop 403 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h3627 : (denoteGraph { pm with nodes := pm.nodes.take 403 } initPM) 3627 =
      (denoteGraph pm initPM) 3627 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3627
      (pm.nodes.take 403) (pm.nodes.drop 403)
      (List.take_append_drop 403 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  have h3637 : (denoteGraph { pm with nodes := pm.nodes.take 403 } initPM) 3637 =
      (denoteGraph pm initPM) 3637 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3637
      (pm.nodes.take 403) (pm.nodes.drop 403)
      (List.take_append_drop 403 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [h3607, h3617, h3627, h3637]
  rfl

set_option maxHeartbeats 8000000 in
theorem prove_pattern_139 : pattern_139_stmt := by
  intro target ht
  cases ht with
  | goal_289 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    -- Acquire lineage of SM[640] from goal_55.
    have hL : goal_55_stmt :=
      prove_pattern_5 pattern_5_target.goal_55
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm640_shape, h_pm_shapes, h_eq_rec⟩ := hLtr
    -- h_pm_shapes: shapes of [pm 2229, ..., pm 2232] are [[1,2,32], ...].
    have h_pm_shapes' :
        [(denoteGraph pm initPM 2229).shape, (denoteGraph pm initPM 2230).shape,
         (denoteGraph pm initPM 2231).shape, (denoteGraph pm initPM 2232).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := h_pm_shapes
      simpa [goal_55, List.map_cons, List.map_nil] using hs
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2229).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2230).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2231).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2232).shape = [1, 2, 32] := by
      have hh := h_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hI0_shape : (denoteGraph pm initPM 2229).shape = [1, 2, 32] := h_pm_shapes_split.1
    have hI1_shape : (denoteGraph pm initPM 2230).shape = [1, 2, 32] := h_pm_shapes_split.2.1
    have hI2_shape : (denoteGraph pm initPM 2231).shape = [1, 2, 32] := h_pm_shapes_split.2.2.1
    have hI3_shape : (denoteGraph pm initPM 2232).shape = [1, 2, 32] := h_pm_shapes_split.2.2.2
    have h_sm640_eq : (denoteGraph sm initSM 640).shape = [1, 8, 32] := by
      have hs := h_sm640_shape; simpa [goal_55] using hs
    -- SM[640] = allGather [pm 2229, pm 2230, pm 2231, pm 2232].
    have h_input_gather : denoteGraph sm initSM 640 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2229, denoteGraph pm initPM 2230,
         denoteGraph pm initPM 2231, denoteGraph pm initPM 2232] := by
      have hh := h_eq_rec
      simp only [goal_55, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hI0_shape]
        intro hbad; cases hbad
    -- SM[1004] eval (= SM[640] since multiref-first = id).
    have h_sm1004 : denoteGraph sm initSM 1004 = denoteGraph sm initSM 640 :=
      sm_eval_1004 initSM
    -- PM[3607..3637] eval (= corresponding PM[2229..2232]).
    have h_pm3607 : denoteGraph pm initPM 3607 = denoteGraph pm initPM 2229 :=
      pm_eval_3607 initPM
    have h_pm3617 : denoteGraph pm initPM 3617 = denoteGraph pm initPM 2230 :=
      pm_eval_3617 initPM
    have h_pm3627 : denoteGraph pm initPM 3627 = denoteGraph pm initPM 2231 :=
      pm_eval_3627 initPM
    have h_pm3637 : denoteGraph pm initPM 3637 = denoteGraph pm initPM 2232 :=
      pm_eval_3637 initPM
    -- PM[999] = allGather [pm 3607, pm 3617, pm 3627, pm 3637].
    have h_pm999 : denoteGraph pm initPM 999 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2229, denoteGraph pm initPM 2230,
         denoteGraph pm initPM 2231, denoteGraph pm initPM 2232] := by
      rw [pm_eval_ag_999 initPM, h_pm3607, h_pm3617, h_pm3627, h_pm3637]
    -- Output shape of PM[999].
    have hhead_pieces :
        (([denoteGraph pm initPM 2229, denoteGraph pm initPM 2230,
           denoteGraph pm initPM 2231, denoteGraph pm initPM 2232]
           : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
      simp [hI0_shape]
    have hpm999_shape : (denoteGraph pm initPM 999).shape = [1, 8, 32] := by
      rw [h_pm999, allGatherPrimDimN_shape 1 4 _ _ hhead_pieces]
      simp [List.set, List.getD]
    have hsm1004_shape : (denoteGraph sm initSM 1004).shape = [1, 8, 32] := by
      rw [h_sm1004]; exact h_sm640_eq
    -- Assemble goal_289 conclusion.
    show (denoteGraph sm initSM 1004).shape = goal_289.tsShape ∧
      _ = goal_289.tpShapes ∧
      denoteGraph sm initSM 1004 =
        reconstructWithDim goal_289.gatherDim pm.numRanks 0
          (goal_289.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_289] using hsm1004_shape
    · simpa [goal_289, List.map_cons, List.map_nil] using hpm999_shape
    · simp only [goal_289, List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [h_sm1004, h_input_gather, ← h_pm999]

end TrainVerify.Denote.GeneratedPatterns
