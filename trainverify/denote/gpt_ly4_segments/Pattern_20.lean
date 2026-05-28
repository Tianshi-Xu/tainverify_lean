/- Auto-generated pattern proof file.
   Pattern: 20
   Hash: 6413053af5c9da02
   Goals: 24
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_19
import denote.gpt_ly4_segments.Pattern_128

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_20_goalIds : List Nat := [24]
inductive pattern_20_target : Prop → Prop
  | goal_24 : pattern_20_target goal_24_stmt

def pattern_20_stmt : Prop :=
  ∀ {target : Prop}, pattern_20_target target → target

set_option maxRecDepth 200000

@[reducible] private def g24_pf0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [1501, 1477], outs := [1505] }
@[reducible] private def g24_pf1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [1502, 1478], outs := [1506] }
@[reducible] private def g24_pf2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_add", ins := [1503, 1479], outs := [1507] }
@[reducible] private def g24_pf3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_add", ins := [1504, 1480], outs := [1508] }

private theorem sm_eval_593 (initSM : Store) :
    denoteGraph sm initSM 593 =
      elemwiseAdd (denoteGraph sm initSM 907) (denoteGraph sm initSM 592) := by
  have hsub : (denoteGraph sm initSM) 593 =
      (denoteGraph { sm with nodes := sm.nodes.take 25 } initSM) 593 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 593
      (sm.nodes.take 25) (sm.nodes.drop 25)
      (List.take_append_drop 25 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 25 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 24 ++
        [{ rank := 0, op := "OpName.FW_add", ins := [907, 592], outs := [593] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_add", ins := [907, 592], outs := [593] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 24 } initSM)
      { rank := 0, op := "OpName.FW_add", ins := [907, 592], outs := [593] }) 593 = _
  rw [applyNode_fw_add2_out]
  have ha : (denoteGraph { sm with nodes := sm.nodes.take 24 } initSM) 907 =
      denoteGraph sm initSM 907 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 907
      (sm.nodes.take 24) (sm.nodes.drop 24)
      (List.take_append_drop 24 _).symm
      (by set_option maxRecDepth 50000 in decide)
  have hb : (denoteGraph { sm with nodes := sm.nodes.take 24 } initSM) 592 =
      denoteGraph sm initSM 592 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 592
      (sm.nodes.take 24) (sm.nodes.drop 24)
      (List.take_append_drop 24 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [ha, hb]

private theorem pm_eval_1505 (initPM : Store) :
    denoteGraph pm initPM 1505 =
      elemwiseAdd (denoteGraph pm initPM 1501) (denoteGraph pm initPM 1477) := by
  have hsub : (denoteGraph pm initPM) 1505 =
      (denoteGraph { pm with nodes := pm.nodes.take 149 } initPM) 1505 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1505
      (pm.nodes.take 149) (pm.nodes.drop 149)
      (List.take_append_drop 149 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 149 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 148 ++ [g24_pf0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g24_pf0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g24_pf0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g24_pf0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 148 } initPM) g24_pf0) 1505 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 148 } initPM 1501 =
      denoteGraph pm initPM 1501 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1501
      (pm.nodes.take 148) (pm.nodes.drop 148)
      (List.take_append_drop 148 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 148 } initPM 1477 =
      denoteGraph pm initPM 1477 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1477
      (pm.nodes.take 148) (pm.nodes.drop 148)
      (List.take_append_drop 148 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_1506 (initPM : Store) :
    denoteGraph pm initPM 1506 =
      elemwiseAdd (denoteGraph pm initPM 1502) (denoteGraph pm initPM 1478) := by
  have hsub : (denoteGraph pm initPM) 1506 =
      (denoteGraph { pm with nodes := pm.nodes.take 150 } initPM) 1506 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1506
      (pm.nodes.take 150) (pm.nodes.drop 150)
      (List.take_append_drop 150 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 150 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 149 ++ [g24_pf1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g24_pf1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g24_pf1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g24_pf1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 149 } initPM) g24_pf1) 1506 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 149 } initPM 1502 =
      denoteGraph pm initPM 1502 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1502
      (pm.nodes.take 149) (pm.nodes.drop 149)
      (List.take_append_drop 149 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 149 } initPM 1478 =
      denoteGraph pm initPM 1478 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1478
      (pm.nodes.take 149) (pm.nodes.drop 149)
      (List.take_append_drop 149 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_1507 (initPM : Store) :
    denoteGraph pm initPM 1507 =
      elemwiseAdd (denoteGraph pm initPM 1503) (denoteGraph pm initPM 1479) := by
  have hsub : (denoteGraph pm initPM) 1507 =
      (denoteGraph { pm with nodes := pm.nodes.take 151 } initPM) 1507 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1507
      (pm.nodes.take 151) (pm.nodes.drop 151)
      (List.take_append_drop 151 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 151 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 150 ++ [g24_pf2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g24_pf2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g24_pf2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g24_pf2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 150 } initPM) g24_pf2) 1507 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 150 } initPM 1503 =
      denoteGraph pm initPM 1503 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1503
      (pm.nodes.take 150) (pm.nodes.drop 150)
      (List.take_append_drop 150 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 150 } initPM 1479 =
      denoteGraph pm initPM 1479 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1479
      (pm.nodes.take 150) (pm.nodes.drop 150)
      (List.take_append_drop 150 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_1508 (initPM : Store) :
    denoteGraph pm initPM 1508 =
      elemwiseAdd (denoteGraph pm initPM 1504) (denoteGraph pm initPM 1480) := by
  have hsub : (denoteGraph pm initPM) 1508 =
      (denoteGraph { pm with nodes := pm.nodes.take 152 } initPM) 1508 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1508
      (pm.nodes.take 152) (pm.nodes.drop 152)
      (List.take_append_drop 152 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 152 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 151 ++ [g24_pf3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g24_pf3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g24_pf3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g24_pf3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 151 } initPM) g24_pf3) 1508 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 151 } initPM 1504 =
      denoteGraph pm initPM 1504 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1504
      (pm.nodes.take 151) (pm.nodes.drop 151)
      (List.take_append_drop 151 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 151 } initPM 1480 =
      denoteGraph pm initPM 1480 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1480
      (pm.nodes.take 151) (pm.nodes.drop 151)
      (List.take_append_drop 151 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

theorem prove_pattern_20 : pattern_20_stmt := by
  intro target h
  cases h with
  | goal_24 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      -- Pull two prereq lineage facts.
      have hGoalA : goal_23_stmt := prove_pattern_19 pattern_19_target.goal_23
      have hGoalB : goal_259_stmt := prove_pattern_128 pattern_128_target.goal_259
      have hA := hGoalA initSM initPM hSmInit hPmInit hInitGoals
      have hB := hGoalB initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hA_sm_shape, hA_pm_shapes, hA_eq_rec⟩ := hA
      obtain ⟨hB_sm_shape, hB_pm_shapes, hB_eq_rec⟩ := hB
      -- sm 592 as allGather of pm pieces [1477..1480]
      have hA_eq : denoteGraph sm initSM 592 = allGatherPrimDimN 2 4 0
          [denoteGraph pm initPM 1477, denoteGraph pm initPM 1478,
           denoteGraph pm initPM 1479, denoteGraph pm initPM 1480] := by
        have hh := hA_eq_rec
        change denoteGraph sm initSM 592 =
          reconstructWithDim 2 pm.numRanks 0
            ([({ rank := 0, tid := 1477 } : Piece), { rank := 1, tid := 1478 },
              { rank := 2, tid := 1479 }, { rank := 3, tid := 1480 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 1477).shape = [1, 8, 8] by
          have hs := hA_pm_shapes
          change [(denoteGraph pm initPM 1477).shape, (denoteGraph pm initPM 1478).shape,
            (denoteGraph pm initPM 1479).shape, (denoteGraph pm initPM 1480).shape] =
            [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      -- sm 907 as allGather of pm pieces [1501..1504]
      have hB_eq : denoteGraph sm initSM 907 = allGatherPrimDimN 2 4 0
          [denoteGraph pm initPM 1501, denoteGraph pm initPM 1502,
           denoteGraph pm initPM 1503, denoteGraph pm initPM 1504] := by
        have hh := hB_eq_rec
        change denoteGraph sm initSM 907 =
          reconstructWithDim 2 pm.numRanks 0
            ([({ rank := 0, tid := 1501 } : Piece), { rank := 1, tid := 1502 },
              { rank := 2, tid := 1503 }, { rank := 3, tid := 1504 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 1501).shape = [1, 8, 8] by
          have hs := hB_pm_shapes
          change [(denoteGraph pm initPM 1501).shape, (denoteGraph pm initPM 1502).shape,
            (denoteGraph pm initPM 1503).shape, (denoteGraph pm initPM 1504).shape] =
            [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      -- Shape facts for sm tensors
      have hA_sm_shape' : (denoteGraph sm initSM 592).shape = [1, 8, 32] := by
        simpa [goal_23] using hA_sm_shape
      have hB_sm_shape' : (denoteGraph sm initSM 907).shape = [1, 8, 32] := by
        simpa [goal_259] using hB_sm_shape
      -- Shape facts for pm pieces
      have ⟨ha0_shape, ha1_shape, ha2_shape, ha3_shape⟩ :
          (denoteGraph pm initPM 1477).shape = [1, 8, 8] ∧
          (denoteGraph pm initPM 1478).shape = [1, 8, 8] ∧
          (denoteGraph pm initPM 1479).shape = [1, 8, 8] ∧
          (denoteGraph pm initPM 1480).shape = [1, 8, 8] := by
        have hs := hA_pm_shapes
        change [(denoteGraph pm initPM 1477).shape, (denoteGraph pm initPM 1478).shape,
          (denoteGraph pm initPM 1479).shape, (denoteGraph pm initPM 1480).shape] =
          [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have ⟨hb0_shape, hb1_shape, hb2_shape, hb3_shape⟩ :
          (denoteGraph pm initPM 1501).shape = [1, 8, 8] ∧
          (denoteGraph pm initPM 1502).shape = [1, 8, 8] ∧
          (denoteGraph pm initPM 1503).shape = [1, 8, 8] ∧
          (denoteGraph pm initPM 1504).shape = [1, 8, 8] := by
        have hs := hB_pm_shapes
        change [(denoteGraph pm initPM 1501).shape, (denoteGraph pm initPM 1502).shape,
          (denoteGraph pm initPM 1503).shape, (denoteGraph pm initPM 1504).shape] =
          [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      -- Shape facts for resulting per-shard adds.
      have hpf0_shape : (elemwiseAdd (denoteGraph pm initPM 1501)
          (denoteGraph pm initPM 1477)).shape = [1, 8, 8] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] hb0_shape ha0_shape
      have hpf1_shape : (elemwiseAdd (denoteGraph pm initPM 1502)
          (denoteGraph pm initPM 1478)).shape = [1, 8, 8] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] hb1_shape ha1_shape
      have hpf2_shape : (elemwiseAdd (denoteGraph pm initPM 1503)
          (denoteGraph pm initPM 1479)).shape = [1, 8, 8] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] hb2_shape ha2_shape
      have hpf3_shape : (elemwiseAdd (denoteGraph pm initPM 1504)
          (denoteGraph pm initPM 1480)).shape = [1, 8, 8] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] hb3_shape ha3_shape
      change (denoteGraph sm initSM 593).shape = [1, 8, 32] ∧
        List.map (fun t => t.shape)
          ([({ rank := 0, tid := 1505 } : Piece), { rank := 1, tid := 1506 },
            { rank := 2, tid := 1507 }, { rank := 3, tid := 1508 }].map
            (fun p => denoteGraph pm initPM p.tid)) =
          [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]] ∧
        denoteGraph sm initSM 593 =
          reconstructWithDim 2 pm.numRanks 0
            ([({ rank := 0, tid := 1505 } : Piece), { rank := 1, tid := 1506 },
              { rank := 2, tid := 1507 }, { rank := 3, tid := 1508 }].map
              (fun p => denoteGraph pm initPM p.tid))
      refine ⟨?_, ?_, ?_⟩
      · rw [sm_eval_593]
        exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 32] hB_sm_shape' hA_sm_shape'
      · simp only [List.map_cons, List.map_nil]
        rw [pm_eval_1505 initPM, pm_eval_1506 initPM, pm_eval_1507 initPM, pm_eval_1508 initPM]
        simp only [List.cons.injEq, and_true]
        exact ⟨hpf0_shape, hpf1_shape, hpf2_shape, hpf3_shape⟩
      · simp only [List.map_cons, List.map_nil]
        rw [sm_eval_593]
        rw [pm_eval_1505 initPM, pm_eval_1506 initPM, pm_eval_1507 initPM, pm_eval_1508 initPM]
        rw [hA_eq, hB_eq]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        · exact fw_add_dim2_pre_sharded_4_1_8_8
            (denoteGraph pm initPM 1501) (denoteGraph pm initPM 1502)
            (denoteGraph pm initPM 1503) (denoteGraph pm initPM 1504)
            (denoteGraph pm initPM 1477) (denoteGraph pm initPM 1478)
            (denoteGraph pm initPM 1479) (denoteGraph pm initPM 1480)
            hb0_shape hb1_shape hb2_shape hb3_shape
            ha0_shape ha1_shape ha2_shape ha3_shape
        · rw [show (elemwiseAdd (denoteGraph pm initPM 1501)
              (denoteGraph pm initPM 1477)).shape = [1, 8, 8] from hpf0_shape]
          intro hbad
          cases hbad

end TrainVerify.Denote.GeneratedPatterns
