/- Auto-generated pattern proof file.
   Pattern: 22
   Hash: 0565fea697fd9ce8
   Goals: 27
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_19

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_22_goalIds : List Nat := [27]
inductive pattern_22_target : Prop → Prop
  | goal_27 : pattern_22_target goal_27_stmt

def pattern_22_stmt : Prop :=
  ∀ {target : Prop}, pattern_22_target target → target

set_option maxRecDepth 32768

@[reducible] private def g27_sg : NodeDecl :=
  { rank := 0, op := "OpName.FW_gelu", ins := [598], outs := [599] }
@[reducible] private def g27_pg0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_gelu", ins := [1561], outs := [1585] }
@[reducible] private def g27_pg1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_gelu", ins := [1562], outs := [1586] }
@[reducible] private def g27_pg2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_gelu", ins := [1563], outs := [1587] }
@[reducible] private def g27_pg3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_gelu", ins := [1564], outs := [1588] }

set_option maxHeartbeats 4000000 in
-- Bumped to handle decide over pm.nodes.drop ~170 nodes (concrete graph kernel reduction).
private theorem sm_eval_599 (initSM : Store) :
    denoteGraph sm initSM 599 = fw_gelu (denoteGraph sm initSM 598) := by
  have hsub : (denoteGraph sm initSM) 599 =
      (denoteGraph { sm with nodes := sm.nodes.take 29 } initSM) 599 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 599
      (sm.nodes.take 29) (sm.nodes.drop 29)
      (List.take_append_drop 29 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 29 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 28 ++ [g27_sg] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [g27_sg] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := g27_sg :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm g27_sg []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 28 } initSM) g27_sg) 599 = _
  rw [applyNode_fw_gelu_out]
  have hx : denoteGraph { sm with nodes := sm.nodes.take 28 } initSM 598 =
      denoteGraph sm initSM 598 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 598
      (sm.nodes.take 28) (sm.nodes.drop 28)
      (List.take_append_drop 28 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hx]

set_option maxHeartbeats 4000000 in
-- Bumped to handle decide over pm.nodes.drop ~170 nodes (concrete graph kernel reduction).
private theorem pm_eval_1585 (initPM : Store) :
    denoteGraph pm initPM 1585 = fw_gelu (denoteGraph pm initPM 1561) := by
  have hsub : (denoteGraph pm initPM) 1585 =
      (denoteGraph { pm with nodes := pm.nodes.take 170 } initPM) 1585 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1585
      (pm.nodes.take 170) (pm.nodes.drop 170)
      (List.take_append_drop 170 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 170 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 169 ++ [g27_pg0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g27_pg0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g27_pg0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g27_pg0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 169 } initPM) g27_pg0) 1585 = _
  rw [applyNode_fw_gelu_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 169 } initPM 1561 =
      denoteGraph pm initPM 1561 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1561
      (pm.nodes.take 169) (pm.nodes.drop 169)
      (List.take_append_drop 169 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hx]

set_option maxHeartbeats 4000000 in
-- Bumped to handle decide over pm.nodes.drop ~170 nodes (concrete graph kernel reduction).
private theorem pm_eval_1586 (initPM : Store) :
    denoteGraph pm initPM 1586 = fw_gelu (denoteGraph pm initPM 1562) := by
  have hsub : (denoteGraph pm initPM) 1586 =
      (denoteGraph { pm with nodes := pm.nodes.take 171 } initPM) 1586 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1586
      (pm.nodes.take 171) (pm.nodes.drop 171)
      (List.take_append_drop 171 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 171 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 170 ++ [g27_pg1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g27_pg1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g27_pg1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g27_pg1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 170 } initPM) g27_pg1) 1586 = _
  rw [applyNode_fw_gelu_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 170 } initPM 1562 =
      denoteGraph pm initPM 1562 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1562
      (pm.nodes.take 170) (pm.nodes.drop 170)
      (List.take_append_drop 170 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hx]

set_option maxHeartbeats 4000000 in
-- Bumped to handle decide over pm.nodes.drop ~170 nodes (concrete graph kernel reduction).
private theorem pm_eval_1587 (initPM : Store) :
    denoteGraph pm initPM 1587 = fw_gelu (denoteGraph pm initPM 1563) := by
  have hsub : (denoteGraph pm initPM) 1587 =
      (denoteGraph { pm with nodes := pm.nodes.take 172 } initPM) 1587 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1587
      (pm.nodes.take 172) (pm.nodes.drop 172)
      (List.take_append_drop 172 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 172 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 171 ++ [g27_pg2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g27_pg2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g27_pg2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g27_pg2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 171 } initPM) g27_pg2) 1587 = _
  rw [applyNode_fw_gelu_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 171 } initPM 1563 =
      denoteGraph pm initPM 1563 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1563
      (pm.nodes.take 171) (pm.nodes.drop 171)
      (List.take_append_drop 171 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hx]

set_option maxHeartbeats 4000000 in
-- Bumped to handle decide over pm.nodes.drop ~170 nodes (concrete graph kernel reduction).
private theorem pm_eval_1588 (initPM : Store) :
    denoteGraph pm initPM 1588 = fw_gelu (denoteGraph pm initPM 1564) := by
  have hsub : (denoteGraph pm initPM) 1588 =
      (denoteGraph { pm with nodes := pm.nodes.take 173 } initPM) 1588 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1588
      (pm.nodes.take 173) (pm.nodes.drop 173)
      (List.take_append_drop 173 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 173 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 172 ++ [g27_pg3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g27_pg3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g27_pg3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g27_pg3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 172 } initPM) g27_pg3) 1588 = _
  rw [applyNode_fw_gelu_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 172 } initPM 1564 =
      denoteGraph pm initPM 1564 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1564
      (pm.nodes.take 172) (pm.nodes.drop 172)
      (List.take_append_drop 172 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hx]

set_option maxHeartbeats 8000000 in
-- Bumped: main theorem assembles five large pm/sm eval rewrites + reconstruction.
theorem prove_pattern_22 : pattern_22_stmt := by
  intro target h
  cases h with
  | goal_27 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      -- Upstream: goal_26 (via Pattern_19) supplies the gather equation for SM 598.
      have hGoal26 : goal_26_stmt := prove_pattern_19 pattern_19_target.goal_26
      have hX := hGoal26 initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨h598_sm_shape, h598_pm_shapes, h598_eq_rec⟩ := hX
      -- Convert lineage equation to a plain allGatherPrimDimN equation.
      have h598_eq : denoteGraph sm initSM 598 = allGatherPrimDimN 2 4 0
          [denoteGraph pm initPM 1561, denoteGraph pm initPM 1562,
           denoteGraph pm initPM 1563, denoteGraph pm initPM 1564] := by
        have hh := h598_eq_rec
        change denoteGraph sm initSM 598 =
          reconstructWithDim 2 pm.numRanks 0
            ([({ rank := 0, tid := 1561 } : Piece), { rank := 1, tid := 1562 },
              { rank := 2, tid := 1563 }, { rank := 3, tid := 1564 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 1561).shape = [1, 8, 32] by
          have hs := h598_pm_shapes
          change [(denoteGraph pm initPM 1561).shape, (denoteGraph pm initPM 1562).shape,
            (denoteGraph pm initPM 1563).shape, (denoteGraph pm initPM 1564).shape] =
            [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      have h598_sm_shape' : (denoteGraph sm initSM 598).shape = [1, 8, 128] := by
        simpa [goal_26] using h598_sm_shape
      have ⟨ha0_shape, ha1_shape, ha2_shape, ha3_shape⟩ :
          (denoteGraph pm initPM 1561).shape = [1, 8, 32] ∧
          (denoteGraph pm initPM 1562).shape = [1, 8, 32] ∧
          (denoteGraph pm initPM 1563).shape = [1, 8, 32] ∧
          (denoteGraph pm initPM 1564).shape = [1, 8, 32] := by
        have hs := h598_pm_shapes
        change [(denoteGraph pm initPM 1561).shape, (denoteGraph pm initPM 1562).shape,
          (denoteGraph pm initPM 1563).shape, (denoteGraph pm initPM 1564).shape] =
          [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      -- Shapes of fw_gelu pieces (still [1,8,32] each)
      have hg0_shape : (fw_gelu (denoteGraph pm initPM 1561)).shape = [1, 8, 32] := by
        rw [fw_gelu_shape]; exact ha0_shape
      have hg1_shape : (fw_gelu (denoteGraph pm initPM 1562)).shape = [1, 8, 32] := by
        rw [fw_gelu_shape]; exact ha1_shape
      have hg2_shape : (fw_gelu (denoteGraph pm initPM 1563)).shape = [1, 8, 32] := by
        rw [fw_gelu_shape]; exact ha2_shape
      have hg3_shape : (fw_gelu (denoteGraph pm initPM 1564)).shape = [1, 8, 32] := by
        rw [fw_gelu_shape]; exact ha3_shape
      -- Precompute the three pieces as standalone equalities to avoid heavy
      -- rewriting inside the final refine bullets (which forces whnf on the
      -- unfolded goal type and can blow heartbeats).
      have h599 := sm_eval_599 initSM
      have h1585 := pm_eval_1585 initPM
      have h1586 := pm_eval_1586 initPM
      have h1587 := pm_eval_1587 initPM
      have h1588 := pm_eval_1588 initPM
      have h_p1 : (denoteGraph sm initSM 599).shape = [1, 8, 128] := by
        rw [h599, fw_gelu_shape]; exact h598_sm_shape'
      have h_p2 :
          [(denoteGraph pm initPM 1585).shape, (denoteGraph pm initPM 1586).shape,
           (denoteGraph pm initPM 1587).shape, (denoteGraph pm initPM 1588).shape] =
          [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]] := by
        rw [h1585, h1586, h1587, h1588]
        rw [fw_gelu_shape, fw_gelu_shape, fw_gelu_shape, fw_gelu_shape]
        rw [ha0_shape, ha1_shape, ha2_shape, ha3_shape]
      have h_p3 : denoteGraph sm initSM 599 =
          reconstructWithDim 2 4 0
            [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
             denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] := by
        rw [h599, h598_eq, h1585, h1586, h1587, h1588]
        rw [reconstructWithDim_cons_cons_nonscalar]
        · exact fw_gelu_dim2_pieces_4_1_8_32_to_1_8_128
            (denoteGraph pm initPM 1561) (denoteGraph pm initPM 1562)
            (denoteGraph pm initPM 1563) (denoteGraph pm initPM 1564)
            ha0_shape ha1_shape ha2_shape ha3_shape
        · rw [hg0_shape]; intro hbad; cases hbad
      change (denoteGraph sm initSM 599).shape = [1, 8, 128] ∧
        List.map (fun t => t.shape)
          ([({ rank := 0, tid := 1585 } : Piece), { rank := 1, tid := 1586 },
            { rank := 2, tid := 1587 }, { rank := 3, tid := 1588 }].map
            (fun p => denoteGraph pm initPM p.tid)) =
          [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]] ∧
        denoteGraph sm initSM 599 =
          reconstructWithDim 2 pm.numRanks 0
            ([({ rank := 0, tid := 1585 } : Piece), { rank := 1, tid := 1586 },
              { rank := 2, tid := 1587 }, { rank := 3, tid := 1588 }].map
              (fun p => denoteGraph pm initPM p.tid))
      refine ⟨h_p1, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil]; exact h_p2
      · simp only [List.map_cons, List.map_nil, show pm.numRanks = 4 from rfl]
        exact h_p3

end TrainVerify.Denote.GeneratedPatterns
