/- Auto-generated pattern proof file.
   Pattern: 2
   Hash: d17205b18ceed4c3
   Goals: 2
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_2_goalIds : List Nat := [2]
inductive pattern_2_target : Prop → Prop
  | goal_2 : pattern_2_target goal_2_stmt

def pattern_2_stmt : Prop :=
  ∀ {target : Prop}, pattern_2_target target → target

set_option maxRecDepth 4096

/-! ## SM helper

`sm.nodes[0]` is the only SM node that writes tid 564. -/

private theorem sm_eval_564 (initSM : Store) :
    denoteGraph sm initSM 564 = fw_embedding (initSM 714) (initSM 563) := by
  set hd : NodeDecl :=
    { rank := 0, op := "OpName.FW_embedding", ins := [714, 563], outs := [564] }
  have hsub : (denoteGraph sm initSM) 564 =
      (denoteGraph { sm with nodes := sm.nodes.take 1 } initSM) 564 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 564
      (sm.nodes.take 1) (sm.nodes.drop 1)
      (List.take_append_drop 1 _).symm
      (by set_option maxRecDepth 4096 in decide)
  rw [hsub]
  have hsm1 : ({ sm with nodes := sm.nodes.take 1 } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := hd :: [] } := rfl
  rw [hsm1, denoteGraph_cons_eq sm hd []]
  change (applyNode sm initSM hd) 564 = _
  exact applyNode_fw_embedding_out _ initSM 0 714 563 564

/-! ## PM helpers

`pm` has 1565 nodes; only `pm.nodes[11]` (the AllReducePrim) writes tid 564.
The AllReducePrim's inputs are tids 1069..1072, each written by exactly
one earlier node (0, 2, 4, 6 with `params := [r * 32]`). -/

-- Bind once for clarity. Use private defs since `local notation` doesn't accept
-- structure literals reliably. `@[reducible]` lets `rfl` unfold them.
@[reducible] private def n0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [714, 1065], outs := [1069], params := [0] }
@[reducible] private def n1 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [716], outs := [1085], params := [1] }
@[reducible] private def n2 : NodeDecl :=
  { rank := 1, op := "OpName.FW_embedding", ins := [714, 1066], outs := [1070], params := [32] }
@[reducible] private def n3 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [716], outs := [1086], params := [1] }
@[reducible] private def n4 : NodeDecl :=
  { rank := 2, op := "OpName.FW_embedding", ins := [714, 1067], outs := [1071], params := [64] }
@[reducible] private def n5 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [716], outs := [1087], params := [1] }
@[reducible] private def n6 : NodeDecl :=
  { rank := 3, op := "OpName.FW_embedding", ins := [714, 1068], outs := [1072], params := [96] }

private theorem pm_take11_at_1069 (initPM : Store) :
    (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1069 =
      fw_embedding_offset 0 (initPM 714) (initPM 1065) := by
  have hsub :
      (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1069 =
        (denoteGraph { pm with nodes := pm.nodes.take 1 } initPM) 1069 := by
    have hsplit : ({ pm with nodes := pm.nodes.take 11 } : GraphDecl).nodes =
        pm.nodes.take 1 ++ ((pm.nodes.drop 1).take 10) := by decide
    exact denoteGraph_tid_eq_of_suffix_no_writes
      { pm with nodes := pm.nodes.take 11 } initPM 1069
      (pm.nodes.take 1) ((pm.nodes.drop 1).take 10) hsplit
      (by set_option maxRecDepth 4096 in decide)
  rw [hsub]
  have h1 : ({ pm with nodes := pm.nodes.take 1 } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := n0 :: [] } := rfl
  rw [h1, denoteGraph_cons_eq pm n0 []]
  change (applyNode pm initPM n0) 1069 = _
  exact applyNode_fw_embedding_offset_out _ initPM 0 0 714 1065 1069

private theorem pm_take11_at_1070 (initPM : Store) :
    (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1070 =
      fw_embedding_offset 32 (initPM 714) (initPM 1066) := by
  have hsub :
      (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1070 =
        (denoteGraph { pm with nodes := pm.nodes.take 3 } initPM) 1070 := by
    have hsplit : ({ pm with nodes := pm.nodes.take 11 } : GraphDecl).nodes =
        pm.nodes.take 3 ++ ((pm.nodes.drop 3).take 8) := by decide
    exact denoteGraph_tid_eq_of_suffix_no_writes
      { pm with nodes := pm.nodes.take 11 } initPM 1070
      (pm.nodes.take 3) ((pm.nodes.drop 3).take 8) hsplit
      (by set_option maxRecDepth 4096 in decide)
  rw [hsub]
  have h3 : ({ pm with nodes := pm.nodes.take 3 } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := (n0 : NodeDecl) :: n1 :: n2 :: [] } := rfl
  rw [h3, denoteGraph_cons_eq pm n0, denoteGraph_cons_eq pm n1, denoteGraph_cons_eq pm n2]
  change (applyNode pm (applyNode pm (applyNode pm initPM n0) n1) n2) 1070 = _
  rw [applyNode_fw_embedding_offset_out pm
        (applyNode pm (applyNode pm initPM n0) n1) 1 32 714 1066 1070]
  have h714_n1 : (applyNode pm (applyNode pm initPM n0) n1) 714 = initPM 714 := by
    rw [applyNode_eq_of_not_mem_outs pm _ n1 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n0 714 (by decide)]
  have h1066_n1 : (applyNode pm (applyNode pm initPM n0) n1) 1066 = initPM 1066 := by
    rw [applyNode_eq_of_not_mem_outs pm _ n1 1066 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n0 1066 (by decide)]
  rw [h714_n1, h1066_n1]

private theorem pm_take11_at_1071 (initPM : Store) :
    (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1071 =
      fw_embedding_offset 64 (initPM 714) (initPM 1067) := by
  have hsub :
      (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1071 =
        (denoteGraph { pm with nodes := pm.nodes.take 5 } initPM) 1071 := by
    have hsplit : ({ pm with nodes := pm.nodes.take 11 } : GraphDecl).nodes =
        pm.nodes.take 5 ++ ((pm.nodes.drop 5).take 6) := by decide
    exact denoteGraph_tid_eq_of_suffix_no_writes
      { pm with nodes := pm.nodes.take 11 } initPM 1071
      (pm.nodes.take 5) ((pm.nodes.drop 5).take 6) hsplit
      (by set_option maxRecDepth 4096 in decide)
  rw [hsub]
  have h5 : ({ pm with nodes := pm.nodes.take 5 } : GraphDecl) =
      { numRanks := pm.numRanks,
        nodes := (n0 : NodeDecl) :: n1 :: n2 :: n3 :: n4 :: [] } := rfl
  rw [h5, denoteGraph_cons_eq pm n0, denoteGraph_cons_eq pm n1,
      denoteGraph_cons_eq pm n2, denoteGraph_cons_eq pm n3, denoteGraph_cons_eq pm n4]
  change (applyNode pm
    (applyNode pm (applyNode pm (applyNode pm (applyNode pm initPM n0) n1) n2) n3) n4) 1071 = _
  rw [applyNode_fw_embedding_offset_out pm _ 2 64 714 1067 1071]
  have h714 :
      (applyNode pm (applyNode pm (applyNode pm (applyNode pm initPM n0) n1) n2) n3) 714 =
        initPM 714 := by
    rw [applyNode_eq_of_not_mem_outs pm _ n3 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n2 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n1 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n0 714 (by decide)]
  have h1067 :
      (applyNode pm (applyNode pm (applyNode pm (applyNode pm initPM n0) n1) n2) n3) 1067 =
        initPM 1067 := by
    rw [applyNode_eq_of_not_mem_outs pm _ n3 1067 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n2 1067 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n1 1067 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n0 1067 (by decide)]
  rw [h714, h1067]

private theorem pm_take11_at_1072 (initPM : Store) :
    (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1072 =
      fw_embedding_offset 96 (initPM 714) (initPM 1068) := by
  have hsub :
      (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1072 =
        (denoteGraph { pm with nodes := pm.nodes.take 7 } initPM) 1072 := by
    have hsplit : ({ pm with nodes := pm.nodes.take 11 } : GraphDecl).nodes =
        pm.nodes.take 7 ++ ((pm.nodes.drop 7).take 4) := by decide
    exact denoteGraph_tid_eq_of_suffix_no_writes
      { pm with nodes := pm.nodes.take 11 } initPM 1072
      (pm.nodes.take 7) ((pm.nodes.drop 7).take 4) hsplit
      (by set_option maxRecDepth 4096 in decide)
  rw [hsub]
  have h7 : ({ pm with nodes := pm.nodes.take 7 } : GraphDecl) =
      { numRanks := pm.numRanks,
        nodes := (n0 : NodeDecl) :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: [] } := rfl
  rw [h7, denoteGraph_cons_eq pm n0, denoteGraph_cons_eq pm n1,
      denoteGraph_cons_eq pm n2, denoteGraph_cons_eq pm n3, denoteGraph_cons_eq pm n4,
      denoteGraph_cons_eq pm n5, denoteGraph_cons_eq pm n6]
  change (applyNode pm
    (applyNode pm (applyNode pm (applyNode pm (applyNode pm (applyNode pm
      (applyNode pm initPM n0) n1) n2) n3) n4) n5) n6) 1072 = _
  rw [applyNode_fw_embedding_offset_out pm _ 3 96 714 1068 1072]
  have h714 :
      (applyNode pm (applyNode pm (applyNode pm (applyNode pm (applyNode pm
        (applyNode pm initPM n0) n1) n2) n3) n4) n5) 714 = initPM 714 := by
    rw [applyNode_eq_of_not_mem_outs pm _ n5 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n4 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n3 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n2 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n1 714 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n0 714 (by decide)]
  have h1068 :
      (applyNode pm (applyNode pm (applyNode pm (applyNode pm (applyNode pm
        (applyNode pm initPM n0) n1) n2) n3) n4) n5) 1068 = initPM 1068 := by
    rw [applyNode_eq_of_not_mem_outs pm _ n5 1068 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n4 1068 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n3 1068 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n2 1068 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n1 1068 (by decide),
        applyNode_eq_of_not_mem_outs pm _ n0 1068 (by decide)]
  rw [h714, h1068]

/-- PM evaluation at tid 564: AllReducePrim of the four `fw_embedding_offset`s. -/
private theorem pm_eval_564 (initPM : Store) :
    denoteGraph pm initPM 564 = allReducePrim 4 0
      [ fw_embedding_offset 0 (initPM 714) (initPM 1065),
        fw_embedding_offset 32 (initPM 714) (initPM 1066),
        fw_embedding_offset 64 (initPM 714) (initPM 1067),
        fw_embedding_offset 96 (initPM 714) (initPM 1068) ] := by
  set arNode : NodeDecl :=
    { rank := 0, op := "OpName.AllReducePrim",
      ins := ((List.range 4).map (fun r => 1069 + r)),
      outs := [564] }
  -- Step 1: Drop nodes 12+ which don't write 564.
  have hsub : (denoteGraph pm initPM) 564 =
      (denoteGraph { pm with nodes := pm.nodes.take 12 } initPM) 564 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 564
      (pm.nodes.take 12) (pm.nodes.drop 12)
      (List.take_append_drop 12 _).symm
      (by set_option maxRecDepth 16384 in decide)
  rw [hsub]
  -- Step 2: take 12 = take 11 ++ [arNode].
  have htake12 : ({ pm with nodes := pm.nodes.take 12 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 11 ++ [arNode] } := by
    rfl
  rw [htake12, denoteGraph_nodes_append]
  -- Step 3: Reduce singleton-graph denoteGraph to applyNode.
  have hsing : ({ pm with nodes := [arNode] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := arNode :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm arNode []]
  -- Step 4: Apply the AllReducePrim semantics
  change (applyNode pm
    (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) arNode) 564 = _
  rw [applyNode_allReducePrim_out pm _ 0
        ((List.range 4).map (fun r => 1069 + r)) 564]
  have hnr : pm.numRanks = 4 := rfl
  rw [hnr]
  -- Step 5: Reduce the list-map to read the 4 inputs.
  change allReducePrim 4 0
      [ (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1069,
        (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1070,
        (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1071,
        (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1072 ] = _
  rw [pm_take11_at_1069 initPM, pm_take11_at_1070 initPM,
      pm_take11_at_1071 initPM, pm_take11_at_1072 initPM]

theorem prove_pattern_2 : pattern_2_stmt := by
  intro target h
  cases h
  intro initSM initPM _hSmInit _hPmInit hInitGoals
  -- Extract initGoal_563 and initGoal_714 hypotheses.
  have hInit563 : InitGoalHolds pm.numRanks initGoal_563 initSM initPM := by
    have hmem : initGoal_563 ∈ initGoals := by simp [initGoals]
    exact hInitGoals initGoal_563 hmem
  have hInit714 : InitGoalHolds pm.numRanks initGoal_714 initSM initPM := by
    have hmem : initGoal_714 ∈ initGoals := by simp [initGoals]
    exact hInitGoals initGoal_714 hmem
  obtain ⟨hSh563_sm, hSh563_pm, hRec563⟩ := hInit563
  obtain ⟨hSh714_sm, hSh714_pm, hRec714⟩ := hInit714
  -- Simplify the per-element shape lists to scalar shape facts.
  -- hSh563_pm : List.map shape [initPM 1065, ..., initPM 1068] = [[32,32], ..., [32,32]]
  have h1065 : (initPM 1065).shape = [32, 32] := by
    have hh := hSh563_pm
    simp only [initGoal_563, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.1
  have h1066 : (initPM 1066).shape = [32, 32] := by
    have hh := hSh563_pm
    simp only [initGoal_563, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.2.1
  have h1067 : (initPM 1067).shape = [32, 32] := by
    have hh := hSh563_pm
    simp only [initGoal_563, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.2.2.1
  have h1068 : (initPM 1068).shape = [32, 32] := by
    have hh := hSh563_pm
    simp only [initGoal_563, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.2.2.2.1
  have h714_pm_sh : (initPM 714).shape = [1, 8] := by
    have hh := hSh714_pm
    simp only [initGoal_714, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.1
  -- ts shapes from goal
  have h714_sm_sh : (initSM 714).shape = [1, 8] := by
    have hh := hSh714_sm
    simp only [initGoal_714] at hh
    exact hh
  have h563_sm_sh : (initSM 563).shape = [128, 32] := by
    have hh := hSh563_sm
    simp only [initGoal_563] at hh
    exact hh
  -- initSM 714 = initPM 714 (singleton reconstruction)
  have h714_eq : initSM 714 = initPM 714 := by
    have hh := hRec714
    simp only [initGoal_714, List.map_cons, List.map_nil,
                reconstructWithDim_singleton] at hh
    exact hh
  -- initSM 563 = allGatherPrimDimN 0 4 0 [initPM 1065, initPM 1066, initPM 1067, initPM 1068]
  have h563_eq : initSM 563 =
      allGatherPrimDimN 0 4 0 [initPM 1065, initPM 1066, initPM 1067, initPM 1068] := by
    have hh := hRec563
    simp only [initGoal_563, List.map_cons, List.map_nil] at hh
    -- hh : initSM 563 = reconstructWithDim 0 pm.numRanks 0 [initPM 1065, ..., initPM 1068]
    rw [hh]
    have hpm_nr : pm.numRanks = 4 := rfl
    rw [hpm_nr]
    -- Now: reconstructWithDim 0 4 0 [a, b, c, d] = allGatherPrimDimN 0 4 0 [...]
    have hne : (initPM 1065).shape ≠ [1] := by
      rw [h1065]; intro hc
      have : ([32, 32] : List Nat) = [1] := hc
      cases this
    -- Use the cons_cons_nonscalar lemma
    exact reconstructWithDim_cons_cons_nonscalar 0 4 0 (initPM 1065) (initPM 1066)
            [initPM 1067, initPM 1068] hne
  -- Now prove the three conjuncts.
  refine ⟨?_, ?_, ?_⟩
  · -- (denoteGraph sm initSM 564).shape = [1, 8, 32]
    show (denoteGraph sm initSM 564).shape = [1, 8, 32]
    rw [sm_eval_564, fw_embedding_shape, h714_sm_sh, h563_sm_sh]
    rfl
  · -- [(denoteGraph pm initPM 564).shape] = [[1, 8, 32]]
    show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 564 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [pm_eval_564]
    have hheadEq :
        ([fw_embedding_offset 0 (initPM 714) (initPM 1065),
          fw_embedding_offset 32 (initPM 714) (initPM 1066),
          fw_embedding_offset 64 (initPM 714) (initPM 1067),
          fw_embedding_offset 96 (initPM 714) (initPM 1068)] : List Tensor).head? =
        some (fw_embedding_offset 0 (initPM 714) (initPM 1065)) := rfl
    rw [allReducePrim_shape 4 0 _ _ hheadEq]
    rw [fw_embedding_offset_shape, h714_pm_sh, h1065]
    rfl
  · -- value equality
    show denoteGraph sm initSM 564 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 564 } : Piece)].map (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
    rw [sm_eval_564, pm_eval_564]
    -- LHS: fw_embedding (initSM 714) (initSM 563)
    -- RHS: allReducePrim 4 0 [fw_embedding_offset 0 (initPM 714) (initPM 1065), ...]
    rw [h714_eq, h563_eq]
    -- Apply bridging lemma:
    -- fw_embedding ids (allGatherPrimDimN 0 4 0 Ws) =
    --   allReducePrim 4 0 (List.ofFn (fun r : Fin 4 => fw_embedding_offset (r.val * 32) ids
    --                                  (Ws.getD r.val (zeroTensor [32, 32]))))
    have hbridge := fw_embedding_eq_allReduce_offset_shards 4 32 32
        (by decide) (by decide) (by decide)
        (initPM 714) [initPM 1065, initPM 1066, initPM 1067, initPM 1068]
        (by rfl)
        (by
          show (Option.map (fun t => Tensor.shape t)
                  (some (initPM 1065))).getD [] = [32, 32]
          show (initPM 1065).shape = [32, 32]
          exact h1065)
        (by
          intro r hr
          match r, hr with
          | 0, _ => exact h1065
          | 1, _ => exact h1066
          | 2, _ => exact h1067
          | 3, _ => exact h1068)
    rw [hbridge]
    -- The bridging lemma's RHS now matches our PM-side `allReducePrim` literal directly:
    -- `List.ofFn (fun r : Fin 4 => fw_embedding_offset (r.val * 32) (initPM 714)
    --   ([initPM 1065, ..., initPM 1068].getD r.val ...))` reduces to the explicit list.
    rfl

end TrainVerify.Denote.GeneratedPatterns

