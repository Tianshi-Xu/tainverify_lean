/- Full Pattern_22-idiom proof of `goal_342_stmt` (BW_gelu, dim-2, 4-shard).

   Mirrors `denote/gpt_ly4_segments/Pattern_22.lean` exactly, but for the binary
   backward-gelu op. goal_342's two direct inputs are:
     * x    = goal_26  (sm tid 1638, pm tids 3577..3580)
     * grad = goal_343 (sm tid 2081, pm tids 3613..3616)
   Both inputs are currently UNPROVEN in the DAG, so we introduce TWO TEMPORARY
   axiom stubs (the only allowed escape hatches). When the DAG is filled in, these
   get replaced by the real `prove_goal_26_*` / `prove_goal_343_*`.
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

-- ===== TEMPORARY input stubs (the ONLY axioms; replace with real proofs later) =====
axiom stub_goal_26  : goal_26_stmt
axiom stub_goal_343 : goal_343_stmt

set_option maxRecDepth 32768

-- sm producing node (sm.nodes idx 655): BW_gelu ins [grad=2081, x=1638] -> 2080
@[reducible] private def g342_sg : NodeDecl :=
  { rank := 0, op := "OpName.BW_gelu", ins := [2081, 1638], outs := [2080] }
-- pm producing nodes (pm.nodes idx 4364..4367)
@[reducible] private def g342_pg0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_gelu", ins := [3613, 3577], outs := [3591] }
@[reducible] private def g342_pg1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_gelu", ins := [3614, 3578], outs := [3594] }
@[reducible] private def g342_pg2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_gelu", ins := [3615, 3579], outs := [3597] }
@[reducible] private def g342_pg3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_gelu", ins := [3616, 3580], outs := [3600] }

set_option maxHeartbeats 16000000 in
private theorem sm_eval_2080 (initSM : Store) :
    denoteGraph sm initSM 2080 =
      bw_gelu (denoteGraph sm initSM 2081) (denoteGraph sm initSM 1638) := by
  have hsub : (denoteGraph sm initSM) 2080 =
      (denoteGraph { sm with nodes := sm.nodes.take 656 } initSM) 2080 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 2080
      (sm.nodes.take 656) (sm.nodes.drop 656)
      (List.take_append_drop 656 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 656 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 655 ++ [g342_sg] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [g342_sg] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := g342_sg :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm g342_sg []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 655 } initSM) g342_sg) 2080 = _
  rw [applyNode_bw_gelu_out]
  have hgrad : denoteGraph { sm with nodes := sm.nodes.take 655 } initSM 2081 =
      denoteGraph sm initSM 2081 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 2081
      (sm.nodes.take 655) (sm.nodes.drop 655)
      (List.take_append_drop 655 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hx : denoteGraph { sm with nodes := sm.nodes.take 655 } initSM 1638 =
      denoteGraph sm initSM 1638 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1638
      (sm.nodes.take 655) (sm.nodes.drop 655)
      (List.take_append_drop 655 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hgrad, hx]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3591 (initPM : Store) :
    denoteGraph pm initPM 3591 =
      bw_gelu (denoteGraph pm initPM 3613) (denoteGraph pm initPM 3577) := by
  have hsub : (denoteGraph pm initPM) 3591 =
      (denoteGraph { pm with nodes := pm.nodes.take 4365 } initPM) 3591 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3591
      (pm.nodes.take 4365) (pm.nodes.drop 4365)
      (List.take_append_drop 4365 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 4365 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 4364 ++ [g342_pg0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g342_pg0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g342_pg0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g342_pg0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 4364 } initPM) g342_pg0) 3591 = _
  rw [applyNode_bw_gelu_out]
  have hgrad : denoteGraph { pm with nodes := pm.nodes.take 4364 } initPM 3613 =
      denoteGraph pm initPM 3613 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3613
      (pm.nodes.take 4364) (pm.nodes.drop 4364)
      (List.take_append_drop 4364 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hx : denoteGraph { pm with nodes := pm.nodes.take 4364 } initPM 3577 =
      denoteGraph pm initPM 3577 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3577
      (pm.nodes.take 4364) (pm.nodes.drop 4364)
      (List.take_append_drop 4364 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hgrad, hx]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3594 (initPM : Store) :
    denoteGraph pm initPM 3594 =
      bw_gelu (denoteGraph pm initPM 3614) (denoteGraph pm initPM 3578) := by
  have hsub : (denoteGraph pm initPM) 3594 =
      (denoteGraph { pm with nodes := pm.nodes.take 4366 } initPM) 3594 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3594
      (pm.nodes.take 4366) (pm.nodes.drop 4366)
      (List.take_append_drop 4366 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 4366 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 4365 ++ [g342_pg1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g342_pg1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g342_pg1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g342_pg1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 4365 } initPM) g342_pg1) 3594 = _
  rw [applyNode_bw_gelu_out]
  have hgrad : denoteGraph { pm with nodes := pm.nodes.take 4365 } initPM 3614 =
      denoteGraph pm initPM 3614 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3614
      (pm.nodes.take 4365) (pm.nodes.drop 4365)
      (List.take_append_drop 4365 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hx : denoteGraph { pm with nodes := pm.nodes.take 4365 } initPM 3578 =
      denoteGraph pm initPM 3578 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3578
      (pm.nodes.take 4365) (pm.nodes.drop 4365)
      (List.take_append_drop 4365 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hgrad, hx]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3597 (initPM : Store) :
    denoteGraph pm initPM 3597 =
      bw_gelu (denoteGraph pm initPM 3615) (denoteGraph pm initPM 3579) := by
  have hsub : (denoteGraph pm initPM) 3597 =
      (denoteGraph { pm with nodes := pm.nodes.take 4367 } initPM) 3597 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3597
      (pm.nodes.take 4367) (pm.nodes.drop 4367)
      (List.take_append_drop 4367 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 4367 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 4366 ++ [g342_pg2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g342_pg2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g342_pg2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g342_pg2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 4366 } initPM) g342_pg2) 3597 = _
  rw [applyNode_bw_gelu_out]
  have hgrad : denoteGraph { pm with nodes := pm.nodes.take 4366 } initPM 3615 =
      denoteGraph pm initPM 3615 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3615
      (pm.nodes.take 4366) (pm.nodes.drop 4366)
      (List.take_append_drop 4366 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hx : denoteGraph { pm with nodes := pm.nodes.take 4366 } initPM 3579 =
      denoteGraph pm initPM 3579 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3579
      (pm.nodes.take 4366) (pm.nodes.drop 4366)
      (List.take_append_drop 4366 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hgrad, hx]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3600 (initPM : Store) :
    denoteGraph pm initPM 3600 =
      bw_gelu (denoteGraph pm initPM 3616) (denoteGraph pm initPM 3580) := by
  have hsub : (denoteGraph pm initPM) 3600 =
      (denoteGraph { pm with nodes := pm.nodes.take 4368 } initPM) 3600 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3600
      (pm.nodes.take 4368) (pm.nodes.drop 4368)
      (List.take_append_drop 4368 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 4368 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 4367 ++ [g342_pg3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g342_pg3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g342_pg3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g342_pg3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 4367 } initPM) g342_pg3) 3600 = _
  rw [applyNode_bw_gelu_out]
  have hgrad : denoteGraph { pm with nodes := pm.nodes.take 4367 } initPM 3616 =
      denoteGraph pm initPM 3616 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3616
      (pm.nodes.take 4367) (pm.nodes.drop 4367)
      (List.take_append_drop 4367 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hx : denoteGraph { pm with nodes := pm.nodes.take 4367 } initPM 3580 =
      denoteGraph pm initPM 3580 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3580
      (pm.nodes.take 4367) (pm.nodes.drop 4367)
      (List.take_append_drop 4367 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hgrad, hx]

set_option maxHeartbeats 8000000 in
theorem prove_goal_342_full : goal_342_stmt := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Upstream x-input: goal_26 supplies the gather equation for SM 1638.
  have hX := stub_goal_26 initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨_h1638_sm_shape, h1638_pm_shapes, h1638_eq_rec⟩ := hX
  -- Upstream grad-input: goal_343 supplies the gather equation for SM 2081.
  have hG := stub_goal_343 initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨_h2081_sm_shape, h2081_pm_shapes, h2081_eq_rec⟩ := hG
  -- ---- x-input pm-shapes ----
  have ⟨hx0_shape, hx1_shape, hx2_shape, hx3_shape⟩ :
      (denoteGraph pm initPM 3577).shape = [1, 1024, 768] ∧
      (denoteGraph pm initPM 3578).shape = [1, 1024, 768] ∧
      (denoteGraph pm initPM 3579).shape = [1, 1024, 768] ∧
      (denoteGraph pm initPM 3580).shape = [1, 1024, 768] := by
    have hs := h1638_pm_shapes
    change [(denoteGraph pm initPM 3577).shape, (denoteGraph pm initPM 3578).shape,
      (denoteGraph pm initPM 3579).shape, (denoteGraph pm initPM 3580).shape] =
      [[1, 1024, 768], [1, 1024, 768], [1, 1024, 768], [1, 1024, 768]] at hs
    simp only [List.cons.injEq, and_true] at hs
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  -- ---- grad-input pm-shapes ----
  have ⟨hg0_shape, hg1_shape, hg2_shape, hg3_shape⟩ :
      (denoteGraph pm initPM 3613).shape = [1, 1024, 768] ∧
      (denoteGraph pm initPM 3614).shape = [1, 1024, 768] ∧
      (denoteGraph pm initPM 3615).shape = [1, 1024, 768] ∧
      (denoteGraph pm initPM 3616).shape = [1, 1024, 768] := by
    have hs := h2081_pm_shapes
    change [(denoteGraph pm initPM 3613).shape, (denoteGraph pm initPM 3614).shape,
      (denoteGraph pm initPM 3615).shape, (denoteGraph pm initPM 3616).shape] =
      [[1, 1024, 768], [1, 1024, 768], [1, 1024, 768], [1, 1024, 768]] at hs
    simp only [List.cons.injEq, and_true] at hs
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  -- ---- convert x-input lineage eq to a plain allGatherPrimDimN equation ----
  have hx_eq : denoteGraph sm initSM 1638 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 3577, denoteGraph pm initPM 3578,
       denoteGraph pm initPM 3579, denoteGraph pm initPM 3580] := by
    have hh := h1638_eq_rec
    change denoteGraph sm initSM 1638 =
      reconstructWithDim 2 pm.numRanks 0
        ([({ rank := 0, tid := 3577 } : Piece), { rank := 1, tid := 3578 },
          { rank := 2, tid := 3579 }, { rank := 3, tid := 3580 }].map
          (fun p => denoteGraph pm initPM p.tid)) at hh
    simp only [List.map_cons, List.map_nil] at hh
    rw [hh, show pm.numRanks = 4 from rfl, reconstructWithDim_cons_cons_nonscalar]
    rw [hx0_shape]; intro hbad; cases hbad
  -- ---- convert grad-input lineage eq to a plain allGatherPrimDimN equation ----
  have hg_eq : denoteGraph sm initSM 2081 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 3613, denoteGraph pm initPM 3614,
       denoteGraph pm initPM 3615, denoteGraph pm initPM 3616] := by
    have hh := h2081_eq_rec
    change denoteGraph sm initSM 2081 =
      reconstructWithDim 2 pm.numRanks 0
        ([({ rank := 0, tid := 3613 } : Piece), { rank := 1, tid := 3614 },
          { rank := 2, tid := 3615 }, { rank := 3, tid := 3616 }].map
          (fun p => denoteGraph pm initPM p.tid)) at hh
    simp only [List.map_cons, List.map_nil] at hh
    rw [hh, show pm.numRanks = 4 from rfl, reconstructWithDim_cons_cons_nonscalar]
    rw [hg0_shape]; intro hbad; cases hbad
  -- ---- piece evaluations ----
  have h2080 := sm_eval_2080 initSM
  have h3591 := pm_eval_3591 initPM
  have h3594 := pm_eval_3594 initPM
  have h3597 := pm_eval_3597 initPM
  have h3600 := pm_eval_3600 initPM
  -- pm output piece shapes (bw_gelu g x has shape x.shape)
  have hp0_shape : (denoteGraph pm initPM 3591).shape = [1, 1024, 768] := by
    rw [h3591, bw_gelu_shape]; exact hx0_shape
  have hp1_shape : (denoteGraph pm initPM 3594).shape = [1, 1024, 768] := by
    rw [h3594, bw_gelu_shape]; exact hx1_shape
  have hp2_shape : (denoteGraph pm initPM 3597).shape = [1, 1024, 768] := by
    rw [h3597, bw_gelu_shape]; exact hx2_shape
  have hp3_shape : (denoteGraph pm initPM 3600).shape = [1, 1024, 768] := by
    rw [h3600, bw_gelu_shape]; exact hx3_shape
  -- sm output shape
  have h_p1 : (denoteGraph sm initSM 2080).shape = [1, 1024, 3072] := by
    rw [h2080, hx_eq, bw_gelu_shape]
    have hhead :
        (([denoteGraph pm initPM 3577, denoteGraph pm initPM 3578,
            denoteGraph pm initPM 3579, denoteGraph pm initPM 3580] : List Tensor).head?.map
          (fun t => t.shape)).getD [] = [1, 1024, 768] := by simp [hx0_shape]
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]; simp [List.set, List.getD]
  -- pm output shapes list
  have h_p2 :
      [(denoteGraph pm initPM 3591).shape, (denoteGraph pm initPM 3594).shape,
       (denoteGraph pm initPM 3597).shape, (denoteGraph pm initPM 3600).shape] =
      [[1, 1024, 768], [1, 1024, 768], [1, 1024, 768], [1, 1024, 768]] := by
    rw [hp0_shape, hp1_shape, hp2_shape, hp3_shape]
  -- the reconstruction equation
  have h_p3 : denoteGraph sm initSM 2080 =
      reconstructWithDim 2 4 0
        [denoteGraph pm initPM 3591, denoteGraph pm initPM 3594,
         denoteGraph pm initPM 3597, denoteGraph pm initPM 3600] := by
    rw [h2080, hx_eq, hg_eq, h3591, h3594, h3597, h3600]
    rw [reconstructWithDim_cons_cons_nonscalar]
    · exact bw_gelu_dim2_pieces_4_1_1024_768_to_1_1024_3072
        (denoteGraph pm initPM 3613) (denoteGraph pm initPM 3614)
        (denoteGraph pm initPM 3615) (denoteGraph pm initPM 3616)
        (denoteGraph pm initPM 3577) (denoteGraph pm initPM 3578)
        (denoteGraph pm initPM 3579) (denoteGraph pm initPM 3580)
        hg0_shape hg1_shape hg2_shape hg3_shape
        hx0_shape hx1_shape hx2_shape hx3_shape
    · rw [show (bw_gelu (denoteGraph pm initPM 3613) (denoteGraph pm initPM 3577)).shape
            = [1, 1024, 768] by rw [bw_gelu_shape]; exact hx0_shape]
      intro hbad; cases hbad
  change (denoteGraph sm initSM 2080).shape = [1, 1024, 3072] ∧
    List.map (fun t => t.shape)
      ([({ rank := 0, tid := 3591 } : Piece), { rank := 1, tid := 3594 },
        { rank := 2, tid := 3597 }, { rank := 3, tid := 3600 }].map
        (fun p => denoteGraph pm initPM p.tid)) =
      [[1, 1024, 768], [1, 1024, 768], [1, 1024, 768], [1, 1024, 768]] ∧
    denoteGraph sm initSM 2080 =
      reconstructWithDim 2 pm.numRanks 0
        ([({ rank := 0, tid := 3591 } : Piece), { rank := 1, tid := 3594 },
          { rank := 2, tid := 3597 }, { rank := 3, tid := 3600 }].map
          (fun p => denoteGraph pm initPM p.tid))
  refine ⟨h_p1, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]; exact h_p2
  · simp only [List.map_cons, List.map_nil, show pm.numRanks = 4 from rfl]
    exact h_p3

#print axioms prove_goal_342_full

end TrainVerify.Denote.GeneratedPatterns
