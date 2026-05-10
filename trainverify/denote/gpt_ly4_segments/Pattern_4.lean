/- Auto-generated pattern proof file.
   Pattern: 4
   Hash: 3db6b13aae6c304a
   Goals: 4
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_2
import denote.gpt_ly4_segments.Pattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_4_goalIds : List Nat := [4]
inductive pattern_4_target : Prop → Prop
  | goal_4 : pattern_4_target goal_4_stmt

def pattern_4_stmt : Prop :=
  ∀ {target : Prop}, pattern_4_target target → target

set_option maxRecDepth 32768

@[reducible] private def p13 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [564], outs := [1109], params := [2] }
@[reducible] private def p14 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [564], outs := [1110], params := [2] }
@[reducible] private def p15 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [564], outs := [1111], params := [2] }
@[reducible] private def p16 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [564], outs := [1112], params := [2] }
@[reducible] private def p17 : NodeDecl :=
  { rank := 0, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1089 + r)), outs := [1113], params := [1, 2] }
@[reducible] private def p18 : NodeDecl :=
  { rank := 1, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1089 + r)), outs := [1114], params := [1, 2] }
@[reducible] private def p19 : NodeDecl :=
  { rank := 2, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1089 + r)), outs := [1115], params := [1, 2] }
@[reducible] private def p20 : NodeDecl :=
  { rank := 3, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1089 + r)), outs := [1116], params := [1, 2] }
@[reducible] private def p21 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [1109, 1113], outs := [1117] }
@[reducible] private def p22 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [1110, 1114], outs := [1118] }
@[reducible] private def p23 : NodeDecl :=
  { rank := 2, op := "OpName.FW_add", ins := [1111, 1115], outs := [1119] }
@[reducible] private def p24 : NodeDecl :=
  { rank := 3, op := "OpName.FW_add", ins := [1112, 1116], outs := [1120] }

private theorem applyNode_chunkPrimDimN_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) (dim : Nat) :
    applyNode g s { rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid], params := [dim] } outTid =
      chunkPrimDimN dim g.numRanks rank (s inTid) := by
  unfold applyNode
  change storeSet s [(outTid, chunkPrimDimN dim g.numRanks rank (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]

private theorem sm_eval_567 (initSM : Store) :
    denoteGraph sm initSM 567 = elemwiseAdd (denoteGraph sm initSM 564) (denoteGraph sm initSM 566) := by
  have hsub : (denoteGraph sm initSM) 567 =
      (denoteGraph { sm with nodes := sm.nodes.take 3 } initSM) 567 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 567
      (sm.nodes.take 3) (sm.nodes.drop 3)
      (List.take_append_drop 3 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 3 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 2 ++
        [{ rank := 0, op := "OpName.FW_add", ins := [564, 566], outs := [567] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_add", ins := [564, 566], outs := [567] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 2 } initSM)
      { rank := 0, op := "OpName.FW_add", ins := [564, 566], outs := [567] }) 567 = _
  rw [applyNode_fw_add2_out]
  have h564 : (denoteGraph { sm with nodes := sm.nodes.take 2 } initSM) 564 =
      denoteGraph sm initSM 564 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 564
      (sm.nodes.take 2) (sm.nodes.drop 2)
      (List.take_append_drop 2 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h566 : (denoteGraph { sm with nodes := sm.nodes.take 2 } initSM) 566 =
      denoteGraph sm initSM 566 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 566
      (sm.nodes.take 2) (sm.nodes.drop 2)
      (List.take_append_drop 2 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h564, h566]

private theorem pm_eval_1109 (initPM : Store) :
    denoteGraph pm initPM 1109 = chunkPrimDimN 2 4 0 (denoteGraph pm initPM 564) := by
  have hsub : (denoteGraph pm initPM) 1109 =
      (denoteGraph { pm with nodes := pm.nodes.take 14 } initPM) 1109 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1109
      (pm.nodes.take 14) (pm.nodes.drop 14)
      (List.take_append_drop 14 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 14 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 13 ++ [p13] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p13] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p13 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p13 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 13 } initPM) p13) 1109 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 13 } initPM 564 = denoteGraph pm initPM 564 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 564
      (pm.nodes.take 13) (pm.nodes.drop 13)
      (List.take_append_drop 13 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_1110 (initPM : Store) :
    denoteGraph pm initPM 1110 = chunkPrimDimN 2 4 1 (denoteGraph pm initPM 564) := by
  have hsub : (denoteGraph pm initPM) 1110 =
      (denoteGraph { pm with nodes := pm.nodes.take 15 } initPM) 1110 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1110
      (pm.nodes.take 15) (pm.nodes.drop 15)
      (List.take_append_drop 15 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 15 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 14 ++ [p14] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p14] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p14 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p14 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 14 } initPM) p14) 1110 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 14 } initPM 564 = denoteGraph pm initPM 564 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 564
      (pm.nodes.take 14) (pm.nodes.drop 14)
      (List.take_append_drop 14 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_1111 (initPM : Store) :
    denoteGraph pm initPM 1111 = chunkPrimDimN 2 4 2 (denoteGraph pm initPM 564) := by
  have hsub : (denoteGraph pm initPM) 1111 =
      (denoteGraph { pm with nodes := pm.nodes.take 16 } initPM) 1111 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1111
      (pm.nodes.take 16) (pm.nodes.drop 16)
      (List.take_append_drop 16 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 16 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 15 ++ [p15] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p15] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p15 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p15 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 15 } initPM) p15) 1111 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 15 } initPM 564 = denoteGraph pm initPM 564 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 564
      (pm.nodes.take 15) (pm.nodes.drop 15)
      (List.take_append_drop 15 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_1112 (initPM : Store) :
    denoteGraph pm initPM 1112 = chunkPrimDimN 2 4 3 (denoteGraph pm initPM 564) := by
  have hsub : (denoteGraph pm initPM) 1112 =
      (denoteGraph { pm with nodes := pm.nodes.take 17 } initPM) 1112 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1112
      (pm.nodes.take 17) (pm.nodes.drop 17)
      (List.take_append_drop 17 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 17 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 16 ++ [p16] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p16] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p16 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p16 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 16 } initPM) p16) 1112 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 16 } initPM 564 = denoteGraph pm initPM 564 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 564
      (pm.nodes.take 16) (pm.nodes.drop 16)
      (List.take_append_drop 16 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hprefix]
  rfl


private theorem pm_eval_1113 (initPM : Store) :
    denoteGraph pm initPM 1113 = allToAllPrimWithDims 4 0
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  have hsub : (denoteGraph pm initPM) 1113 =
      (denoteGraph { pm with nodes := pm.nodes.take 18 } initPM) 1113 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1113
      (pm.nodes.take 18) (pm.nodes.drop 18)
      (List.take_append_drop 18 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 18 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 17 ++ [p17] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p17] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p17 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p17 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 17 } initPM) p17) 1113 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 0
      [denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1089,
       denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1090,
       denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1091,
       denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1092] 1 2 = _
  have h1089 : denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1089 = denoteGraph pm initPM 1089 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1089 (pm.nodes.take 17) (pm.nodes.drop 17) (List.take_append_drop 17 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1090 : denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1090 = denoteGraph pm initPM 1090 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1090 (pm.nodes.take 17) (pm.nodes.drop 17) (List.take_append_drop 17 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1091 : denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1091 = denoteGraph pm initPM 1091 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1091 (pm.nodes.take 17) (pm.nodes.drop 17) (List.take_append_drop 17 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1092 : denoteGraph { pm with nodes := pm.nodes.take 17 } initPM 1092 = denoteGraph pm initPM 1092 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1092 (pm.nodes.take 17) (pm.nodes.drop 17) (List.take_append_drop 17 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1089, h1090, h1091, h1092]



private theorem pm_eval_1114 (initPM : Store) :
    denoteGraph pm initPM 1114 = allToAllPrimWithDims 4 1
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  have hsub : (denoteGraph pm initPM) 1114 =
      (denoteGraph { pm with nodes := pm.nodes.take 19 } initPM) 1114 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1114
      (pm.nodes.take 19) (pm.nodes.drop 19)
      (List.take_append_drop 18 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 19 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 18 ++ [p18] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p18] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p18 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p18 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 17 } initPM) p18) 1114 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 1
      [denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1089,
       denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1090,
       denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1091,
       denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1092] 1 2 = _
  have h1089 : denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1089 = denoteGraph pm initPM 1089 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1089 (pm.nodes.take 18) (pm.nodes.drop 18) (List.take_append_drop 18 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1090 : denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1090 = denoteGraph pm initPM 1090 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1090 (pm.nodes.take 18) (pm.nodes.drop 18) (List.take_append_drop 18 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1091 : denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1091 = denoteGraph pm initPM 1091 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1091 (pm.nodes.take 18) (pm.nodes.drop 18) (List.take_append_drop 18 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1092 : denoteGraph { pm with nodes := pm.nodes.take 18 } initPM 1092 = denoteGraph pm initPM 1092 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1092 (pm.nodes.take 18) (pm.nodes.drop 18) (List.take_append_drop 18 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1089, h1090, h1091, h1092]



private theorem pm_eval_1115 (initPM : Store) :
    denoteGraph pm initPM 1115 = allToAllPrimWithDims 4 2
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  have hsub : (denoteGraph pm initPM) 1115 =
      (denoteGraph { pm with nodes := pm.nodes.take 20 } initPM) 1115 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1115
      (pm.nodes.take 20) (pm.nodes.drop 20)
      (List.take_append_drop 18 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 20 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 19 ++ [p19] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p19] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p19 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p19 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 17 } initPM) p19) 1115 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 2
      [denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1089,
       denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1090,
       denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1091,
       denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1092] 1 2 = _
  have h1089 : denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1089 = denoteGraph pm initPM 1089 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1089 (pm.nodes.take 19) (pm.nodes.drop 19) (List.take_append_drop 19 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1090 : denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1090 = denoteGraph pm initPM 1090 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1090 (pm.nodes.take 19) (pm.nodes.drop 19) (List.take_append_drop 19 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1091 : denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1091 = denoteGraph pm initPM 1091 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1091 (pm.nodes.take 19) (pm.nodes.drop 19) (List.take_append_drop 19 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1092 : denoteGraph { pm with nodes := pm.nodes.take 19 } initPM 1092 = denoteGraph pm initPM 1092 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1092 (pm.nodes.take 19) (pm.nodes.drop 19) (List.take_append_drop 19 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1089, h1090, h1091, h1092]



private theorem pm_eval_1116 (initPM : Store) :
    denoteGraph pm initPM 1116 = allToAllPrimWithDims 4 3
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  have hsub : (denoteGraph pm initPM) 1116 =
      (denoteGraph { pm with nodes := pm.nodes.take 21 } initPM) 1116 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1116
      (pm.nodes.take 21) (pm.nodes.drop 21)
      (List.take_append_drop 18 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 21 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 20 ++ [p20] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p20] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p20 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p20 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 17 } initPM) p20) 1116 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 3
      [denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1089,
       denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1090,
       denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1091,
       denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1092] 1 2 = _
  have h1089 : denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1089 = denoteGraph pm initPM 1089 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1089 (pm.nodes.take 20) (pm.nodes.drop 20) (List.take_append_drop 20 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1090 : denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1090 = denoteGraph pm initPM 1090 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1090 (pm.nodes.take 20) (pm.nodes.drop 20) (List.take_append_drop 20 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1091 : denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1091 = denoteGraph pm initPM 1091 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1091 (pm.nodes.take 20) (pm.nodes.drop 20) (List.take_append_drop 20 _).symm (by set_option maxRecDepth 20000 in decide)
  have h1092 : denoteGraph { pm with nodes := pm.nodes.take 20 } initPM 1092 = denoteGraph pm initPM 1092 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1092 (pm.nodes.take 20) (pm.nodes.drop 20) (List.take_append_drop 20 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1089, h1090, h1091, h1092]


private theorem pm_eval_1117 (initPM : Store) :
    denoteGraph pm initPM 1117 = elemwiseAdd (denoteGraph pm initPM 1109) (denoteGraph pm initPM 1113) := by
  have hsub : (denoteGraph pm initPM) 1117 =
      (denoteGraph { pm with nodes := pm.nodes.take 22 } initPM) 1117 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1117
      (pm.nodes.take 22) (pm.nodes.drop 22)
      (List.take_append_drop 22 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 22 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 21 ++ [p21] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p21] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p21 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p21 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 21 } initPM) p21) 1117 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 21 } initPM 1109 = denoteGraph pm initPM 1109 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1109 (pm.nodes.take 21) (pm.nodes.drop 21) (List.take_append_drop 21 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 21 } initPM 1113 = denoteGraph pm initPM 1113 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1113 (pm.nodes.take 21) (pm.nodes.drop 21) (List.take_append_drop 21 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

private theorem pm_eval_1118 (initPM : Store) :
    denoteGraph pm initPM 1118 = elemwiseAdd (denoteGraph pm initPM 1110) (denoteGraph pm initPM 1114) := by
  have hsub : (denoteGraph pm initPM) 1118 =
      (denoteGraph { pm with nodes := pm.nodes.take 23 } initPM) 1118 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1118
      (pm.nodes.take 23) (pm.nodes.drop 23)
      (List.take_append_drop 23 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 23 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 22 ++ [p22] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p22] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p22 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p22 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 22 } initPM) p22) 1118 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 22 } initPM 1110 = denoteGraph pm initPM 1110 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1110 (pm.nodes.take 22) (pm.nodes.drop 22) (List.take_append_drop 22 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 22 } initPM 1114 = denoteGraph pm initPM 1114 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1114 (pm.nodes.take 22) (pm.nodes.drop 22) (List.take_append_drop 22 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

private theorem pm_eval_1119 (initPM : Store) :
    denoteGraph pm initPM 1119 = elemwiseAdd (denoteGraph pm initPM 1111) (denoteGraph pm initPM 1115) := by
  have hsub : (denoteGraph pm initPM) 1119 =
      (denoteGraph { pm with nodes := pm.nodes.take 24 } initPM) 1119 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1119
      (pm.nodes.take 24) (pm.nodes.drop 24)
      (List.take_append_drop 24 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 24 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 23 ++ [p23] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p23] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p23 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p23 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 23 } initPM) p23) 1119 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 23 } initPM 1111 = denoteGraph pm initPM 1111 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1111 (pm.nodes.take 23) (pm.nodes.drop 23) (List.take_append_drop 23 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 23 } initPM 1115 = denoteGraph pm initPM 1115 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1115 (pm.nodes.take 23) (pm.nodes.drop 23) (List.take_append_drop 23 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

private theorem pm_eval_1120 (initPM : Store) :
    denoteGraph pm initPM 1120 = elemwiseAdd (denoteGraph pm initPM 1112) (denoteGraph pm initPM 1116) := by
  have hsub : (denoteGraph pm initPM) 1120 =
      (denoteGraph { pm with nodes := pm.nodes.take 25 } initPM) 1120 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1120
      (pm.nodes.take 25) (pm.nodes.drop 25)
      (List.take_append_drop 25 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 25 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 24 ++ [p24] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p24] } : GraphDecl) = { numRanks := pm.numRanks, nodes := p24 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p24 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 24 } initPM) p24) 1120 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 24 } initPM 1112 = denoteGraph pm initPM 1112 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1112 (pm.nodes.take 24) (pm.nodes.drop 24) (List.take_append_drop 24 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 24 } initPM 1116 = denoteGraph pm initPM 1116 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1116 (pm.nodes.take 24) (pm.nodes.drop 24) (List.take_append_drop 24 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]
theorem prove_pattern_4 : pattern_4_stmt := by
  intro target h
  cases h
  intro initSM initPM hSmInit hPmInit hInitGoals
  have hGoal2 : goal_2_stmt := prove_pattern_2 pattern_2_target.goal_2
  have hGoal3 : goal_3_stmt := prove_pattern_3 pattern_3_target.goal_3
  have h2 := hGoal2 initSM initPM hSmInit hPmInit hInitGoals
  have h3 := hGoal3 initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h564_sm_shape, h564_pm_shapes, h564_eq_rec⟩ := h2
  obtain ⟨h566_sm_shape, h566_pm_shapes, h566_eq_rec⟩ := h3
  have h564_eq : denoteGraph sm initSM 564 = denoteGraph pm initPM 564 := by
    have hh := h564_eq_rec
    change denoteGraph sm initSM 564 =
      reconstructWithDim 0 pm.numRanks 0
        ([({ rank := 0, tid := 564 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) at hh
    simpa only [List.map_cons, List.map_nil, reconstructWithDim_singleton] using hh
  have h566_eq : denoteGraph sm initSM 566 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] := by
    have hh := h566_eq_rec
    change denoteGraph sm initSM 566 =
      reconstructWithDim 1 pm.numRanks 0
        ([({ rank := 0, tid := 1089 } : Piece), { rank := 1, tid := 1090 },
          { rank := 2, tid := 1091 }, { rank := 3, tid := 1092 }].map
          (fun p => denoteGraph pm initPM p.tid)) at hh
    simp only [List.map_cons, List.map_nil] at hh
    rw [hh]
    rw [show pm.numRanks = 4 from rfl]
    rw [reconstructWithDim_cons_cons_nonscalar]
    rw [show (denoteGraph pm initPM 1089).shape = [1, 2, 32] by
      have hs := h566_pm_shapes
      change [(denoteGraph pm initPM 1089).shape, (denoteGraph pm initPM 1090).shape,
        (denoteGraph pm initPM 1091).shape, (denoteGraph pm initPM 1092).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
      have hs0 := congrArg List.head? hs
      simpa using hs0]
    intro hbad
    cases hbad
  have h1113 : denoteGraph pm initPM 1113 = chunkPrimDimN 2 4 0 (denoteGraph sm initSM 566) := by
    rw [pm_eval_1113]
    rw [h566_eq]
    rfl
  have h1114 : denoteGraph pm initPM 1114 = chunkPrimDimN 2 4 1 (denoteGraph sm initSM 566) := by
    rw [pm_eval_1114]
    rw [h566_eq]
    rfl
  have h1115 : denoteGraph pm initPM 1115 = chunkPrimDimN 2 4 2 (denoteGraph sm initSM 566) := by
    rw [pm_eval_1115]
    rw [h566_eq]
    rfl
  have h1116 : denoteGraph pm initPM 1116 = chunkPrimDimN 2 4 3 (denoteGraph sm initSM 566) := by
    rw [pm_eval_1116]
    rw [h566_eq]
    rfl
  have h564_sm_shape' : (denoteGraph sm initSM 564).shape = [1, 8, 32] := by
    simpa [goal_2] using h564_sm_shape
  have h564_pm_shape : (denoteGraph pm initPM 564).shape = [1, 8, 32] := by
    simpa [goal_2] using h564_pm_shapes
  have h566_sm_shape' : (denoteGraph sm initSM 566).shape = [1, 8, 32] := by
    simpa [goal_3] using h566_sm_shape
  change (denoteGraph sm initSM 567).shape = [1, 8, 32] ∧
    List.map (fun t => t.shape)
      ([({ rank := 0, tid := 1117 } : Piece), { rank := 1, tid := 1118 },
        { rank := 2, tid := 1119 }, { rank := 3, tid := 1120 }].map
        (fun p => denoteGraph pm initPM p.tid)) =
      [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]] ∧
    denoteGraph sm initSM 567 =
      reconstructWithDim 2 pm.numRanks 0
        ([({ rank := 0, tid := 1117 } : Piece), { rank := 1, tid := 1118 },
          { rank := 2, tid := 1119 }, { rank := 3, tid := 1120 }].map
          (fun p => denoteGraph pm initPM p.tid))
  refine ⟨?_, ?_, ?_⟩
  · rw [sm_eval_567]
    exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 32] h564_sm_shape' h566_sm_shape'
  · simp only [List.map_cons, List.map_nil]
    rw [pm_eval_1117, pm_eval_1118, pm_eval_1119, pm_eval_1120]
    rw [pm_eval_1109, pm_eval_1110, pm_eval_1111, pm_eval_1112]
    rw [h1113, h1114, h1115, h1116]
    repeat rw [show (elemwiseAdd (chunkPrimDimN 2 4 0 (denoteGraph pm initPM 564))
        (chunkPrimDimN 2 4 0 (denoteGraph sm initSM 566))).shape = [1, 8, 8] by
      have ha : (chunkPrimDimN 2 4 0 (denoteGraph pm initPM 564)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 0 _ _ h564_pm_shape (by omega)]; simp [List.set, List.getD]
      have hb : (chunkPrimDimN 2 4 0 (denoteGraph sm initSM 566)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 0 _ _ h566_sm_shape' (by omega)]; simp [List.set, List.getD]
      exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] ha hb]
    repeat rw [show (elemwiseAdd (chunkPrimDimN 2 4 1 (denoteGraph pm initPM 564))
        (chunkPrimDimN 2 4 1 (denoteGraph sm initSM 566))).shape = [1, 8, 8] by
      have ha : (chunkPrimDimN 2 4 1 (denoteGraph pm initPM 564)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 1 _ _ h564_pm_shape (by omega)]; simp [List.set, List.getD]
      have hb : (chunkPrimDimN 2 4 1 (denoteGraph sm initSM 566)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 1 _ _ h566_sm_shape' (by omega)]; simp [List.set, List.getD]
      exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] ha hb]
    repeat rw [show (elemwiseAdd (chunkPrimDimN 2 4 2 (denoteGraph pm initPM 564))
        (chunkPrimDimN 2 4 2 (denoteGraph sm initSM 566))).shape = [1, 8, 8] by
      have ha : (chunkPrimDimN 2 4 2 (denoteGraph pm initPM 564)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 2 _ _ h564_pm_shape (by omega)]; simp [List.set, List.getD]
      have hb : (chunkPrimDimN 2 4 2 (denoteGraph sm initSM 566)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 2 _ _ h566_sm_shape' (by omega)]; simp [List.set, List.getD]
      exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] ha hb]
    repeat rw [show (elemwiseAdd (chunkPrimDimN 2 4 3 (denoteGraph pm initPM 564))
        (chunkPrimDimN 2 4 3 (denoteGraph sm initSM 566))).shape = [1, 8, 8] by
      have ha : (chunkPrimDimN 2 4 3 (denoteGraph pm initPM 564)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 3 _ _ h564_pm_shape (by omega)]; simp [List.set, List.getD]
      have hb : (chunkPrimDimN 2 4 3 (denoteGraph sm initSM 566)).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 3 _ _ h566_sm_shape' (by omega)]; simp [List.set, List.getD]
      exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] ha hb]
  · simp only [List.map_cons, List.map_nil]
    rw [sm_eval_567]
    rw [pm_eval_1117, pm_eval_1118, pm_eval_1119, pm_eval_1120]
    rw [pm_eval_1109, pm_eval_1110, pm_eval_1111, pm_eval_1112]
    rw [h1113, h1114, h1115, h1116]
    rw [← h564_eq]
    rw [show pm.numRanks = 4 from rfl]
    rw [reconstructWithDim_cons_cons_nonscalar]
    · exact fw_add_split_dim2_4_1_8_32 (denoteGraph sm initSM 564) (denoteGraph sm initSM 566)
        h564_sm_shape' h566_sm_shape'
    · have hs : (elemwiseAdd (chunkPrimDimN 2 4 0 (denoteGraph sm initSM 564))
          (chunkPrimDimN 2 4 0 (denoteGraph sm initSM 566))).shape = [1, 8, 8] := by
        have ha : (chunkPrimDimN 2 4 0 (denoteGraph sm initSM 564)).shape = [1, 8, 8] := by
          rw [chunkPrimDimN_shape 2 4 0 _ _ h564_sm_shape' (by omega)]; simp [List.set, List.getD]
        have hb : (chunkPrimDimN 2 4 0 (denoteGraph sm initSM 566)).shape = [1, 8, 8] := by
          rw [chunkPrimDimN_shape 2 4 0 _ _ h566_sm_shape' (by omega)]; simp [List.set, List.getD]
        exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 8] ha hb
      rw [hs]
      intro hbad
      cases hbad

end TrainVerify.Denote.GeneratedPatterns



