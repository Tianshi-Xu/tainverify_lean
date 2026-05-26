/- Auto-generated pattern proof file.
   Pattern: 44
   Hash: c118a3d5c38253d9
   Goals: 74, 79, 99, 104
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_43
import denote.gpt_ly4_segments.Pattern_45
import denote.gpt_ly4_segments.Pattern_128

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_44_goalIds : List Nat := [74, 79, 99, 104]
inductive pattern_44_target : Prop → Prop
  | goal_74 : pattern_44_target goal_74_stmt
  | goal_79 : pattern_44_target goal_79_stmt
  | goal_99 : pattern_44_target goal_99_stmt
  | goal_104 : pattern_44_target goal_104_stmt

def pattern_44_stmt : Prop :=
  ∀ {target : Prop}, pattern_44_target target → target

set_option maxRecDepth 200000

@[reducible] private def g74_pc0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [662], outs := [2609], params := [1] }
@[reducible] private def g74_pc1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [662], outs := [2610], params := [1] }
@[reducible] private def g74_pc2 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [662], outs := [2611], params := [1] }
@[reducible] private def g74_pc3 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [662], outs := [2612], params := [1] }
@[reducible] private def g74_pf0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [2605, 2609], outs := [2613] }
@[reducible] private def g74_pf1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [2606, 2610], outs := [2614] }
@[reducible] private def g74_pf2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_add", ins := [2607, 2611], outs := [2615] }
@[reducible] private def g74_pf3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_add", ins := [2608, 2612], outs := [2616] }

private theorem sm_eval_663 (initSM : Store) :
    denoteGraph sm initSM 663 = elemwiseAdd (denoteGraph sm initSM 993) (denoteGraph sm initSM 662) := by
  have hsub : (denoteGraph sm initSM) 663 =
      (denoteGraph { sm with nodes := sm.nodes.take 81 } initSM) 663 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 663
      (sm.nodes.take 81) (sm.nodes.drop 81)
      (List.take_append_drop 81 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 81 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 80 ++
        [{ rank := 0, op := "OpName.FW_add", ins := [993, 662], outs := [663] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_add", ins := [993, 662], outs := [663] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 80 } initSM)
      { rank := 0, op := "OpName.FW_add", ins := [993, 662], outs := [663] }) 663 = _
  rw [applyNode_fw_add2_out]
  have ha : (denoteGraph { sm with nodes := sm.nodes.take 80 } initSM) 993 =
      denoteGraph sm initSM 993 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 993
      (sm.nodes.take 80) (sm.nodes.drop 80)
      (List.take_append_drop 80 _).symm
      (by set_option maxRecDepth 50000 in decide)
  have hb : (denoteGraph { sm with nodes := sm.nodes.take 80 } initSM) 662 =
      denoteGraph sm initSM 662 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 662
      (sm.nodes.take 80) (sm.nodes.drop 80)
      (List.take_append_drop 80 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [ha, hb]

private theorem pm_eval_2609 (initPM : Store) :
    denoteGraph pm initPM 2609 = chunkPrimDimN 1 4 0 (denoteGraph pm initPM 662) := by
  have hsub : (denoteGraph pm initPM) 2609 =
      (denoteGraph { pm with nodes := pm.nodes.take 521 } initPM) 2609 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2609
      (pm.nodes.take 521) (pm.nodes.drop 521)
      (List.take_append_drop 521 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 521 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 520 ++ [g74_pc0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pc0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pc0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pc0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 520 } initPM) g74_pc0) 2609 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 520 } initPM 662 = denoteGraph pm initPM 662 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 662
      (pm.nodes.take 520) (pm.nodes.drop 520)
      (List.take_append_drop 520 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2610 (initPM : Store) :
    denoteGraph pm initPM 2610 = chunkPrimDimN 1 4 1 (denoteGraph pm initPM 662) := by
  have hsub : (denoteGraph pm initPM) 2610 =
      (denoteGraph { pm with nodes := pm.nodes.take 522 } initPM) 2610 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2610
      (pm.nodes.take 522) (pm.nodes.drop 522)
      (List.take_append_drop 522 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 522 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 521 ++ [g74_pc1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pc1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pc1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pc1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 521 } initPM) g74_pc1) 2610 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 521 } initPM 662 = denoteGraph pm initPM 662 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 662
      (pm.nodes.take 521) (pm.nodes.drop 521)
      (List.take_append_drop 521 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2611 (initPM : Store) :
    denoteGraph pm initPM 2611 = chunkPrimDimN 1 4 2 (denoteGraph pm initPM 662) := by
  have hsub : (denoteGraph pm initPM) 2611 =
      (denoteGraph { pm with nodes := pm.nodes.take 523 } initPM) 2611 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2611
      (pm.nodes.take 523) (pm.nodes.drop 523)
      (List.take_append_drop 523 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 523 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 522 ++ [g74_pc2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pc2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pc2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pc2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 522 } initPM) g74_pc2) 2611 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 522 } initPM 662 = denoteGraph pm initPM 662 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 662
      (pm.nodes.take 522) (pm.nodes.drop 522)
      (List.take_append_drop 522 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2612 (initPM : Store) :
    denoteGraph pm initPM 2612 = chunkPrimDimN 1 4 3 (denoteGraph pm initPM 662) := by
  have hsub : (denoteGraph pm initPM) 2612 =
      (denoteGraph { pm with nodes := pm.nodes.take 524 } initPM) 2612 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2612
      (pm.nodes.take 524) (pm.nodes.drop 524)
      (List.take_append_drop 524 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 524 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 523 ++ [g74_pc3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pc3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pc3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pc3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 523 } initPM) g74_pc3) 2612 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 523 } initPM 662 = denoteGraph pm initPM 662 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 662
      (pm.nodes.take 523) (pm.nodes.drop 523)
      (List.take_append_drop 523 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2613 (initPM : Store) :
    denoteGraph pm initPM 2613 = elemwiseAdd (denoteGraph pm initPM 2605) (denoteGraph pm initPM 2609) := by
  have hsub : (denoteGraph pm initPM) 2613 =
      (denoteGraph { pm with nodes := pm.nodes.take 525 } initPM) 2613 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2613
      (pm.nodes.take 525) (pm.nodes.drop 525)
      (List.take_append_drop 525 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 525 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 524 ++ [g74_pf0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pf0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pf0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pf0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 524 } initPM) g74_pf0) 2613 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 524 } initPM 2605 = denoteGraph pm initPM 2605 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2605
      (pm.nodes.take 524) (pm.nodes.drop 524)
      (List.take_append_drop 524 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 524 } initPM 2609 = denoteGraph pm initPM 2609 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2609
      (pm.nodes.take 524) (pm.nodes.drop 524)
      (List.take_append_drop 524 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_2614 (initPM : Store) :
    denoteGraph pm initPM 2614 = elemwiseAdd (denoteGraph pm initPM 2606) (denoteGraph pm initPM 2610) := by
  have hsub : (denoteGraph pm initPM) 2614 =
      (denoteGraph { pm with nodes := pm.nodes.take 526 } initPM) 2614 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2614
      (pm.nodes.take 526) (pm.nodes.drop 526)
      (List.take_append_drop 526 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 526 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 525 ++ [g74_pf1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pf1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pf1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pf1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 525 } initPM) g74_pf1) 2614 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 525 } initPM 2606 = denoteGraph pm initPM 2606 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2606
      (pm.nodes.take 525) (pm.nodes.drop 525)
      (List.take_append_drop 525 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 525 } initPM 2610 = denoteGraph pm initPM 2610 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2610
      (pm.nodes.take 525) (pm.nodes.drop 525)
      (List.take_append_drop 525 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_2615 (initPM : Store) :
    denoteGraph pm initPM 2615 = elemwiseAdd (denoteGraph pm initPM 2607) (denoteGraph pm initPM 2611) := by
  have hsub : (denoteGraph pm initPM) 2615 =
      (denoteGraph { pm with nodes := pm.nodes.take 527 } initPM) 2615 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2615
      (pm.nodes.take 527) (pm.nodes.drop 527)
      (List.take_append_drop 527 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 527 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 526 ++ [g74_pf2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pf2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pf2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pf2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 526 } initPM) g74_pf2) 2615 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 526 } initPM 2607 = denoteGraph pm initPM 2607 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2607
      (pm.nodes.take 526) (pm.nodes.drop 526)
      (List.take_append_drop 526 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 526 } initPM 2611 = denoteGraph pm initPM 2611 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2611
      (pm.nodes.take 526) (pm.nodes.drop 526)
      (List.take_append_drop 526 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_2616 (initPM : Store) :
    denoteGraph pm initPM 2616 = elemwiseAdd (denoteGraph pm initPM 2608) (denoteGraph pm initPM 2612) := by
  have hsub : (denoteGraph pm initPM) 2616 =
      (denoteGraph { pm with nodes := pm.nodes.take 528 } initPM) 2616 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2616
      (pm.nodes.take 528) (pm.nodes.drop 528)
      (List.take_append_drop 528 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 528 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 527 ++ [g74_pf3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g74_pf3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g74_pf3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g74_pf3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 527 } initPM) g74_pf3) 2616 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 527 } initPM 2608 = denoteGraph pm initPM 2608 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2608
      (pm.nodes.take 527) (pm.nodes.drop 527)
      (List.take_append_drop 527 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 527 } initPM 2612 = denoteGraph pm initPM 2612 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2612
      (pm.nodes.take 527) (pm.nodes.drop 527)
      (List.take_append_drop 527 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

@[reducible] private def g79_pc0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [671], outs := [2753], params := [1] }
@[reducible] private def g79_pc1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [671], outs := [2754], params := [1] }
@[reducible] private def g79_pc2 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [671], outs := [2755], params := [1] }
@[reducible] private def g79_pc3 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [671], outs := [2756], params := [1] }
@[reducible] private def g79_pf0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [2749, 2753], outs := [2757] }
@[reducible] private def g79_pf1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [2750, 2754], outs := [2758] }
@[reducible] private def g79_pf2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_add", ins := [2751, 2755], outs := [2759] }
@[reducible] private def g79_pf3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_add", ins := [2752, 2756], outs := [2760] }

private theorem sm_eval_672 (initSM : Store) :
    denoteGraph sm initSM 672 = elemwiseAdd (denoteGraph sm initSM 1024) (denoteGraph sm initSM 671) := by
  have hsub : (denoteGraph sm initSM) 672 =
      (denoteGraph { sm with nodes := sm.nodes.take 87 } initSM) 672 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 672
      (sm.nodes.take 87) (sm.nodes.drop 87)
      (List.take_append_drop 87 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 87 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 86 ++
        [{ rank := 0, op := "OpName.FW_add", ins := [1024, 671], outs := [672] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_add", ins := [1024, 671], outs := [672] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 86 } initSM)
      { rank := 0, op := "OpName.FW_add", ins := [1024, 671], outs := [672] }) 672 = _
  rw [applyNode_fw_add2_out]
  have ha : (denoteGraph { sm with nodes := sm.nodes.take 86 } initSM) 1024 =
      denoteGraph sm initSM 1024 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1024
      (sm.nodes.take 86) (sm.nodes.drop 86)
      (List.take_append_drop 86 _).symm
      (by set_option maxRecDepth 50000 in decide)
  have hb : (denoteGraph { sm with nodes := sm.nodes.take 86 } initSM) 671 =
      denoteGraph sm initSM 671 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 671
      (sm.nodes.take 86) (sm.nodes.drop 86)
      (List.take_append_drop 86 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [ha, hb]

private theorem pm_eval_2753 (initPM : Store) :
    denoteGraph pm initPM 2753 = chunkPrimDimN 1 4 0 (denoteGraph pm initPM 671) := by
  have hsub : (denoteGraph pm initPM) 2753 =
      (denoteGraph { pm with nodes := pm.nodes.take 563 } initPM) 2753 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2753
      (pm.nodes.take 563) (pm.nodes.drop 563)
      (List.take_append_drop 563 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 563 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 562 ++ [g79_pc0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pc0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pc0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pc0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 562 } initPM) g79_pc0) 2753 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 562 } initPM 671 = denoteGraph pm initPM 671 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 671
      (pm.nodes.take 562) (pm.nodes.drop 562)
      (List.take_append_drop 562 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2754 (initPM : Store) :
    denoteGraph pm initPM 2754 = chunkPrimDimN 1 4 1 (denoteGraph pm initPM 671) := by
  have hsub : (denoteGraph pm initPM) 2754 =
      (denoteGraph { pm with nodes := pm.nodes.take 564 } initPM) 2754 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2754
      (pm.nodes.take 564) (pm.nodes.drop 564)
      (List.take_append_drop 564 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 564 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 563 ++ [g79_pc1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pc1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pc1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pc1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 563 } initPM) g79_pc1) 2754 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 563 } initPM 671 = denoteGraph pm initPM 671 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 671
      (pm.nodes.take 563) (pm.nodes.drop 563)
      (List.take_append_drop 563 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2755 (initPM : Store) :
    denoteGraph pm initPM 2755 = chunkPrimDimN 1 4 2 (denoteGraph pm initPM 671) := by
  have hsub : (denoteGraph pm initPM) 2755 =
      (denoteGraph { pm with nodes := pm.nodes.take 565 } initPM) 2755 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2755
      (pm.nodes.take 565) (pm.nodes.drop 565)
      (List.take_append_drop 565 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 565 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 564 ++ [g79_pc2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pc2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pc2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pc2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 564 } initPM) g79_pc2) 2755 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 564 } initPM 671 = denoteGraph pm initPM 671 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 671
      (pm.nodes.take 564) (pm.nodes.drop 564)
      (List.take_append_drop 564 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2756 (initPM : Store) :
    denoteGraph pm initPM 2756 = chunkPrimDimN 1 4 3 (denoteGraph pm initPM 671) := by
  have hsub : (denoteGraph pm initPM) 2756 =
      (denoteGraph { pm with nodes := pm.nodes.take 566 } initPM) 2756 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2756
      (pm.nodes.take 566) (pm.nodes.drop 566)
      (List.take_append_drop 566 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 566 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 565 ++ [g79_pc3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pc3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pc3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pc3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 565 } initPM) g79_pc3) 2756 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 565 } initPM 671 = denoteGraph pm initPM 671 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 671
      (pm.nodes.take 565) (pm.nodes.drop 565)
      (List.take_append_drop 565 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_2757 (initPM : Store) :
    denoteGraph pm initPM 2757 = elemwiseAdd (denoteGraph pm initPM 2749) (denoteGraph pm initPM 2753) := by
  have hsub : (denoteGraph pm initPM) 2757 =
      (denoteGraph { pm with nodes := pm.nodes.take 567 } initPM) 2757 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2757
      (pm.nodes.take 567) (pm.nodes.drop 567)
      (List.take_append_drop 567 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 567 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 566 ++ [g79_pf0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pf0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pf0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pf0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 566 } initPM) g79_pf0) 2757 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 566 } initPM 2749 = denoteGraph pm initPM 2749 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2749
      (pm.nodes.take 566) (pm.nodes.drop 566)
      (List.take_append_drop 566 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 566 } initPM 2753 = denoteGraph pm initPM 2753 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2753
      (pm.nodes.take 566) (pm.nodes.drop 566)
      (List.take_append_drop 566 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_2758 (initPM : Store) :
    denoteGraph pm initPM 2758 = elemwiseAdd (denoteGraph pm initPM 2750) (denoteGraph pm initPM 2754) := by
  have hsub : (denoteGraph pm initPM) 2758 =
      (denoteGraph { pm with nodes := pm.nodes.take 568 } initPM) 2758 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2758
      (pm.nodes.take 568) (pm.nodes.drop 568)
      (List.take_append_drop 568 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 568 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 567 ++ [g79_pf1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pf1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pf1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pf1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 567 } initPM) g79_pf1) 2758 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 567 } initPM 2750 = denoteGraph pm initPM 2750 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2750
      (pm.nodes.take 567) (pm.nodes.drop 567)
      (List.take_append_drop 567 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 567 } initPM 2754 = denoteGraph pm initPM 2754 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2754
      (pm.nodes.take 567) (pm.nodes.drop 567)
      (List.take_append_drop 567 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_2759 (initPM : Store) :
    denoteGraph pm initPM 2759 = elemwiseAdd (denoteGraph pm initPM 2751) (denoteGraph pm initPM 2755) := by
  have hsub : (denoteGraph pm initPM) 2759 =
      (denoteGraph { pm with nodes := pm.nodes.take 569 } initPM) 2759 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2759
      (pm.nodes.take 569) (pm.nodes.drop 569)
      (List.take_append_drop 569 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 569 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 568 ++ [g79_pf2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pf2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pf2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pf2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 568 } initPM) g79_pf2) 2759 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 568 } initPM 2751 = denoteGraph pm initPM 2751 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2751
      (pm.nodes.take 568) (pm.nodes.drop 568)
      (List.take_append_drop 568 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 568 } initPM 2755 = denoteGraph pm initPM 2755 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2755
      (pm.nodes.take 568) (pm.nodes.drop 568)
      (List.take_append_drop 568 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_2760 (initPM : Store) :
    denoteGraph pm initPM 2760 = elemwiseAdd (denoteGraph pm initPM 2752) (denoteGraph pm initPM 2756) := by
  have hsub : (denoteGraph pm initPM) 2760 =
      (denoteGraph { pm with nodes := pm.nodes.take 570 } initPM) 2760 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2760
      (pm.nodes.take 570) (pm.nodes.drop 570)
      (List.take_append_drop 570 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 570 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 569 ++ [g79_pf3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g79_pf3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g79_pf3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g79_pf3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 569 } initPM) g79_pf3) 2760 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 569 } initPM 2752 = denoteGraph pm initPM 2752 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2752
      (pm.nodes.take 569) (pm.nodes.drop 569)
      (List.take_append_drop 569 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 569 } initPM 2756 = denoteGraph pm initPM 2756 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 2756
      (pm.nodes.take 569) (pm.nodes.drop 569)
      (List.take_append_drop 569 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

@[reducible] private def g99_pc0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [697], outs := [3173], params := [1] }
@[reducible] private def g99_pc1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [697], outs := [3174], params := [1] }
@[reducible] private def g99_pc2 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [697], outs := [3175], params := [1] }
@[reducible] private def g99_pc3 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [697], outs := [3176], params := [1] }
@[reducible] private def g99_pf0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [3169, 3173], outs := [3177] }
@[reducible] private def g99_pf1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [3170, 3174], outs := [3178] }
@[reducible] private def g99_pf2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_add", ins := [3171, 3175], outs := [3179] }
@[reducible] private def g99_pf3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_add", ins := [3172, 3176], outs := [3180] }

private theorem sm_eval_698 (initSM : Store) :
    denoteGraph sm initSM 698 = elemwiseAdd (denoteGraph sm initSM 1036) (denoteGraph sm initSM 697) := by
  have hsub : (denoteGraph sm initSM) 698 =
      (denoteGraph { sm with nodes := sm.nodes.take 109 } initSM) 698 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 698
      (sm.nodes.take 109) (sm.nodes.drop 109)
      (List.take_append_drop 109 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 109 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 108 ++
        [{ rank := 0, op := "OpName.FW_add", ins := [1036, 697], outs := [698] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_add", ins := [1036, 697], outs := [698] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 108 } initSM)
      { rank := 0, op := "OpName.FW_add", ins := [1036, 697], outs := [698] }) 698 = _
  rw [applyNode_fw_add2_out]
  have ha : (denoteGraph { sm with nodes := sm.nodes.take 108 } initSM) 1036 =
      denoteGraph sm initSM 1036 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1036
      (sm.nodes.take 108) (sm.nodes.drop 108)
      (List.take_append_drop 108 _).symm
      (by set_option maxRecDepth 50000 in decide)
  have hb : (denoteGraph { sm with nodes := sm.nodes.take 108 } initSM) 697 =
      denoteGraph sm initSM 697 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 697
      (sm.nodes.take 108) (sm.nodes.drop 108)
      (List.take_append_drop 108 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [ha, hb]

private theorem pm_eval_3173 (initPM : Store) :
    denoteGraph pm initPM 3173 = chunkPrimDimN 1 4 0 (denoteGraph pm initPM 697) := by
  have hsub : (denoteGraph pm initPM) 3173 =
      (denoteGraph { pm with nodes := pm.nodes.take 713 } initPM) 3173 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3173
      (pm.nodes.take 713) (pm.nodes.drop 713)
      (List.take_append_drop 713 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 713 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 712 ++ [g99_pc0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pc0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pc0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pc0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 712 } initPM) g99_pc0) 3173 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 712 } initPM 697 = denoteGraph pm initPM 697 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 697
      (pm.nodes.take 712) (pm.nodes.drop 712)
      (List.take_append_drop 712 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3174 (initPM : Store) :
    denoteGraph pm initPM 3174 = chunkPrimDimN 1 4 1 (denoteGraph pm initPM 697) := by
  have hsub : (denoteGraph pm initPM) 3174 =
      (denoteGraph { pm with nodes := pm.nodes.take 714 } initPM) 3174 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3174
      (pm.nodes.take 714) (pm.nodes.drop 714)
      (List.take_append_drop 714 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 714 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 713 ++ [g99_pc1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pc1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pc1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pc1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 713 } initPM) g99_pc1) 3174 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 713 } initPM 697 = denoteGraph pm initPM 697 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 697
      (pm.nodes.take 713) (pm.nodes.drop 713)
      (List.take_append_drop 713 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3175 (initPM : Store) :
    denoteGraph pm initPM 3175 = chunkPrimDimN 1 4 2 (denoteGraph pm initPM 697) := by
  have hsub : (denoteGraph pm initPM) 3175 =
      (denoteGraph { pm with nodes := pm.nodes.take 715 } initPM) 3175 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3175
      (pm.nodes.take 715) (pm.nodes.drop 715)
      (List.take_append_drop 715 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 715 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 714 ++ [g99_pc2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pc2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pc2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pc2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 714 } initPM) g99_pc2) 3175 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 714 } initPM 697 = denoteGraph pm initPM 697 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 697
      (pm.nodes.take 714) (pm.nodes.drop 714)
      (List.take_append_drop 714 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3176 (initPM : Store) :
    denoteGraph pm initPM 3176 = chunkPrimDimN 1 4 3 (denoteGraph pm initPM 697) := by
  have hsub : (denoteGraph pm initPM) 3176 =
      (denoteGraph { pm with nodes := pm.nodes.take 716 } initPM) 3176 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3176
      (pm.nodes.take 716) (pm.nodes.drop 716)
      (List.take_append_drop 716 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 716 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 715 ++ [g99_pc3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pc3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pc3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pc3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 715 } initPM) g99_pc3) 3176 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 715 } initPM 697 = denoteGraph pm initPM 697 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 697
      (pm.nodes.take 715) (pm.nodes.drop 715)
      (List.take_append_drop 715 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3177 (initPM : Store) :
    denoteGraph pm initPM 3177 = elemwiseAdd (denoteGraph pm initPM 3169) (denoteGraph pm initPM 3173) := by
  have hsub : (denoteGraph pm initPM) 3177 =
      (denoteGraph { pm with nodes := pm.nodes.take 717 } initPM) 3177 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3177
      (pm.nodes.take 717) (pm.nodes.drop 717)
      (List.take_append_drop 717 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 717 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 716 ++ [g99_pf0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pf0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pf0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pf0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 716 } initPM) g99_pf0) 3177 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 716 } initPM 3169 = denoteGraph pm initPM 3169 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3169
      (pm.nodes.take 716) (pm.nodes.drop 716)
      (List.take_append_drop 716 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 716 } initPM 3173 = denoteGraph pm initPM 3173 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3173
      (pm.nodes.take 716) (pm.nodes.drop 716)
      (List.take_append_drop 716 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_3178 (initPM : Store) :
    denoteGraph pm initPM 3178 = elemwiseAdd (denoteGraph pm initPM 3170) (denoteGraph pm initPM 3174) := by
  have hsub : (denoteGraph pm initPM) 3178 =
      (denoteGraph { pm with nodes := pm.nodes.take 718 } initPM) 3178 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3178
      (pm.nodes.take 718) (pm.nodes.drop 718)
      (List.take_append_drop 718 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 718 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 717 ++ [g99_pf1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pf1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pf1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pf1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 717 } initPM) g99_pf1) 3178 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 717 } initPM 3170 = denoteGraph pm initPM 3170 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3170
      (pm.nodes.take 717) (pm.nodes.drop 717)
      (List.take_append_drop 717 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 717 } initPM 3174 = denoteGraph pm initPM 3174 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3174
      (pm.nodes.take 717) (pm.nodes.drop 717)
      (List.take_append_drop 717 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_3179 (initPM : Store) :
    denoteGraph pm initPM 3179 = elemwiseAdd (denoteGraph pm initPM 3171) (denoteGraph pm initPM 3175) := by
  have hsub : (denoteGraph pm initPM) 3179 =
      (denoteGraph { pm with nodes := pm.nodes.take 719 } initPM) 3179 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3179
      (pm.nodes.take 719) (pm.nodes.drop 719)
      (List.take_append_drop 719 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 719 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 718 ++ [g99_pf2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pf2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pf2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pf2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 718 } initPM) g99_pf2) 3179 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 718 } initPM 3171 = denoteGraph pm initPM 3171 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3171
      (pm.nodes.take 718) (pm.nodes.drop 718)
      (List.take_append_drop 718 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 718 } initPM 3175 = denoteGraph pm initPM 3175 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3175
      (pm.nodes.take 718) (pm.nodes.drop 718)
      (List.take_append_drop 718 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_3180 (initPM : Store) :
    denoteGraph pm initPM 3180 = elemwiseAdd (denoteGraph pm initPM 3172) (denoteGraph pm initPM 3176) := by
  have hsub : (denoteGraph pm initPM) 3180 =
      (denoteGraph { pm with nodes := pm.nodes.take 720 } initPM) 3180 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3180
      (pm.nodes.take 720) (pm.nodes.drop 720)
      (List.take_append_drop 720 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 720 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 719 ++ [g99_pf3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g99_pf3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g99_pf3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g99_pf3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 719 } initPM) g99_pf3) 3180 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 719 } initPM 3172 = denoteGraph pm initPM 3172 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3172
      (pm.nodes.take 719) (pm.nodes.drop 719)
      (List.take_append_drop 719 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 719 } initPM 3176 = denoteGraph pm initPM 3176 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3176
      (pm.nodes.take 719) (pm.nodes.drop 719)
      (List.take_append_drop 719 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

@[reducible] private def g104_pc0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [706], outs := [3317], params := [1] }
@[reducible] private def g104_pc1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [706], outs := [3318], params := [1] }
@[reducible] private def g104_pc2 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [706], outs := [3319], params := [1] }
@[reducible] private def g104_pc3 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [706], outs := [3320], params := [1] }
@[reducible] private def g104_pf0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [3313, 3317], outs := [3321] }
@[reducible] private def g104_pf1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [3314, 3318], outs := [3322] }
@[reducible] private def g104_pf2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_add", ins := [3315, 3319], outs := [3323] }
@[reducible] private def g104_pf3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_add", ins := [3316, 3320], outs := [3324] }

private theorem sm_eval_707 (initSM : Store) :
    denoteGraph sm initSM 707 = elemwiseAdd (denoteGraph sm initSM 1067) (denoteGraph sm initSM 706) := by
  have hsub : (denoteGraph sm initSM) 707 =
      (denoteGraph { sm with nodes := sm.nodes.take 115 } initSM) 707 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 707
      (sm.nodes.take 115) (sm.nodes.drop 115)
      (List.take_append_drop 115 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 115 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 114 ++
        [{ rank := 0, op := "OpName.FW_add", ins := [1067, 706], outs := [707] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_add", ins := [1067, 706], outs := [707] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 114 } initSM)
      { rank := 0, op := "OpName.FW_add", ins := [1067, 706], outs := [707] }) 707 = _
  rw [applyNode_fw_add2_out]
  have ha : (denoteGraph { sm with nodes := sm.nodes.take 114 } initSM) 1067 =
      denoteGraph sm initSM 1067 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1067
      (sm.nodes.take 114) (sm.nodes.drop 114)
      (List.take_append_drop 114 _).symm
      (by set_option maxRecDepth 50000 in decide)
  have hb : (denoteGraph { sm with nodes := sm.nodes.take 114 } initSM) 706 =
      denoteGraph sm initSM 706 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 706
      (sm.nodes.take 114) (sm.nodes.drop 114)
      (List.take_append_drop 114 _).symm
      (by set_option maxRecDepth 50000 in decide)
  rw [ha, hb]

private theorem pm_eval_3317 (initPM : Store) :
    denoteGraph pm initPM 3317 = chunkPrimDimN 1 4 0 (denoteGraph pm initPM 706) := by
  have hsub : (denoteGraph pm initPM) 3317 =
      (denoteGraph { pm with nodes := pm.nodes.take 755 } initPM) 3317 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3317
      (pm.nodes.take 755) (pm.nodes.drop 755)
      (List.take_append_drop 755 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 755 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 754 ++ [g104_pc0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pc0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pc0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pc0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 754 } initPM) g104_pc0) 3317 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 754 } initPM 706 = denoteGraph pm initPM 706 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 706
      (pm.nodes.take 754) (pm.nodes.drop 754)
      (List.take_append_drop 754 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3318 (initPM : Store) :
    denoteGraph pm initPM 3318 = chunkPrimDimN 1 4 1 (denoteGraph pm initPM 706) := by
  have hsub : (denoteGraph pm initPM) 3318 =
      (denoteGraph { pm with nodes := pm.nodes.take 756 } initPM) 3318 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3318
      (pm.nodes.take 756) (pm.nodes.drop 756)
      (List.take_append_drop 756 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 756 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 755 ++ [g104_pc1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pc1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pc1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pc1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 755 } initPM) g104_pc1) 3318 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 755 } initPM 706 = denoteGraph pm initPM 706 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 706
      (pm.nodes.take 755) (pm.nodes.drop 755)
      (List.take_append_drop 755 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3319 (initPM : Store) :
    denoteGraph pm initPM 3319 = chunkPrimDimN 1 4 2 (denoteGraph pm initPM 706) := by
  have hsub : (denoteGraph pm initPM) 3319 =
      (denoteGraph { pm with nodes := pm.nodes.take 757 } initPM) 3319 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3319
      (pm.nodes.take 757) (pm.nodes.drop 757)
      (List.take_append_drop 757 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 757 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 756 ++ [g104_pc2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pc2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pc2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pc2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 756 } initPM) g104_pc2) 3319 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 756 } initPM 706 = denoteGraph pm initPM 706 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 706
      (pm.nodes.take 756) (pm.nodes.drop 756)
      (List.take_append_drop 756 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3320 (initPM : Store) :
    denoteGraph pm initPM 3320 = chunkPrimDimN 1 4 3 (denoteGraph pm initPM 706) := by
  have hsub : (denoteGraph pm initPM) 3320 =
      (denoteGraph { pm with nodes := pm.nodes.take 758 } initPM) 3320 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3320
      (pm.nodes.take 758) (pm.nodes.drop 758)
      (List.take_append_drop 758 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 758 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 757 ++ [g104_pc3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pc3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pc3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pc3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 757 } initPM) g104_pc3) 3320 = _
  rw [applyNode_chunkPrimDimN_out]
  have hprefix : denoteGraph { pm with nodes := pm.nodes.take 757 } initPM 706 = denoteGraph pm initPM 706 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 706
      (pm.nodes.take 757) (pm.nodes.drop 757)
      (List.take_append_drop 757 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hprefix]
  rfl

private theorem pm_eval_3321 (initPM : Store) :
    denoteGraph pm initPM 3321 = elemwiseAdd (denoteGraph pm initPM 3313) (denoteGraph pm initPM 3317) := by
  have hsub : (denoteGraph pm initPM) 3321 =
      (denoteGraph { pm with nodes := pm.nodes.take 759 } initPM) 3321 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3321
      (pm.nodes.take 759) (pm.nodes.drop 759)
      (List.take_append_drop 759 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 759 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 758 ++ [g104_pf0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pf0] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pf0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pf0 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 758 } initPM) g104_pf0) 3321 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 758 } initPM 3313 = denoteGraph pm initPM 3313 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3313
      (pm.nodes.take 758) (pm.nodes.drop 758)
      (List.take_append_drop 758 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 758 } initPM 3317 = denoteGraph pm initPM 3317 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3317
      (pm.nodes.take 758) (pm.nodes.drop 758)
      (List.take_append_drop 758 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_3322 (initPM : Store) :
    denoteGraph pm initPM 3322 = elemwiseAdd (denoteGraph pm initPM 3314) (denoteGraph pm initPM 3318) := by
  have hsub : (denoteGraph pm initPM) 3322 =
      (denoteGraph { pm with nodes := pm.nodes.take 760 } initPM) 3322 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3322
      (pm.nodes.take 760) (pm.nodes.drop 760)
      (List.take_append_drop 760 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 760 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 759 ++ [g104_pf1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pf1] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pf1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pf1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 759 } initPM) g104_pf1) 3322 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 759 } initPM 3314 = denoteGraph pm initPM 3314 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3314
      (pm.nodes.take 759) (pm.nodes.drop 759)
      (List.take_append_drop 759 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 759 } initPM 3318 = denoteGraph pm initPM 3318 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3318
      (pm.nodes.take 759) (pm.nodes.drop 759)
      (List.take_append_drop 759 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_3323 (initPM : Store) :
    denoteGraph pm initPM 3323 = elemwiseAdd (denoteGraph pm initPM 3315) (denoteGraph pm initPM 3319) := by
  have hsub : (denoteGraph pm initPM) 3323 =
      (denoteGraph { pm with nodes := pm.nodes.take 761 } initPM) 3323 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3323
      (pm.nodes.take 761) (pm.nodes.drop 761)
      (List.take_append_drop 761 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 761 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 760 ++ [g104_pf2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pf2] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pf2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pf2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 760 } initPM) g104_pf2) 3323 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 760 } initPM 3315 = denoteGraph pm initPM 3315 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3315
      (pm.nodes.take 760) (pm.nodes.drop 760)
      (List.take_append_drop 760 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 760 } initPM 3319 = denoteGraph pm initPM 3319 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3319
      (pm.nodes.take 760) (pm.nodes.drop 760)
      (List.take_append_drop 760 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

private theorem pm_eval_3324 (initPM : Store) :
    denoteGraph pm initPM 3324 = elemwiseAdd (denoteGraph pm initPM 3316) (denoteGraph pm initPM 3320) := by
  have hsub : (denoteGraph pm initPM) 3324 =
      (denoteGraph { pm with nodes := pm.nodes.take 762 } initPM) 3324 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3324
      (pm.nodes.take 762) (pm.nodes.drop 762)
      (List.take_append_drop 762 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 762 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 761 ++ [g104_pf3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g104_pf3] } : GraphDecl) = { numRanks := pm.numRanks, nodes := g104_pf3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g104_pf3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 761 } initPM) g104_pf3) 3324 = _
  rw [applyNode_fw_add2_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 761 } initPM 3316 = denoteGraph pm initPM 3316 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3316
      (pm.nodes.take 761) (pm.nodes.drop 761)
      (List.take_append_drop 761 _).symm
      (by set_option maxRecDepth 100000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 761 } initPM 3320 = denoteGraph pm initPM 3320 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3320
      (pm.nodes.take 761) (pm.nodes.drop 761)
      (List.take_append_drop 761 _).symm
      (by set_option maxRecDepth 100000 in decide)
  rw [hx, hy]

theorem prove_pattern_44 : pattern_44_stmt := by
  intro target h
  cases h with
  | goal_74 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hGoalX : goal_287_stmt := prove_pattern_128 pattern_128_target.goal_287
      have hGoalY : goal_73_stmt := prove_pattern_43 pattern_43_target.goal_73
      have hX := hGoalX initSM initPM hSmInit hPmInit hInitGoals
      have hY := hGoalY initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hXa_sm_shape, hXa_pm_shapes, hXa_eq_rec⟩ := hX
      obtain ⟨hXb_sm_shape, hXb_pm_shapes, hXb_eq_rec⟩ := hY
      have hXa_eq : denoteGraph sm initSM 993 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2605, denoteGraph pm initPM 2606,
           denoteGraph pm initPM 2607, denoteGraph pm initPM 2608] := by
        have hh := hXa_eq_rec
        change denoteGraph sm initSM 993 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 2605 } : Piece), { rank := 1, tid := 2606 },
              { rank := 2, tid := 2607 }, { rank := 3, tid := 2608 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 2605).shape = [1, 2, 32] by
          have hs := hXa_pm_shapes
          change [(denoteGraph pm initPM 2605).shape, (denoteGraph pm initPM 2606).shape,
            (denoteGraph pm initPM 2607).shape, (denoteGraph pm initPM 2608).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      have hXb_eq : denoteGraph sm initSM 662 = denoteGraph pm initPM 662 := by
        have hh := hXb_eq_rec
        change denoteGraph sm initSM 662 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 662 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) at hh
        simpa only [List.map_cons, List.map_nil, reconstructWithDim_singleton] using hh
      have hXa_sm_shape' : (denoteGraph sm initSM 993).shape = [1, 8, 32] := by
        simpa [goal_287] using hXa_sm_shape
      have hXb_sm_shape' : (denoteGraph sm initSM 662).shape = [1, 8, 32] := by
        simpa [goal_73] using hXb_sm_shape
      have hXb_pm_shape : (denoteGraph pm initPM 662).shape = [1, 8, 32] := by
        rw [← hXb_eq]; exact hXb_sm_shape'
      have ⟨ha0_shape, ha1_shape, ha2_shape, ha3_shape⟩ : (denoteGraph pm initPM 2605).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2606).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2607).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2608).shape = [1, 2, 32] := by
        have hs := hXa_pm_shapes
        change [(denoteGraph pm initPM 2605).shape, (denoteGraph pm initPM 2606).shape,
          (denoteGraph pm initPM 2607).shape, (denoteGraph pm initPM 2608).shape] =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hck0_shape : (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 662)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 0 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck1_shape : (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 662)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 1 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck2_shape : (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 662)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 2 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck3_shape : (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 662)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 3 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hpf0_shape : (elemwiseAdd (denoteGraph pm initPM 2605) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 662))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha0_shape hck0_shape
      have hpf1_shape : (elemwiseAdd (denoteGraph pm initPM 2606) (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 662))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha1_shape hck1_shape
      have hpf2_shape : (elemwiseAdd (denoteGraph pm initPM 2607) (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 662))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha2_shape hck2_shape
      have hpf3_shape : (elemwiseAdd (denoteGraph pm initPM 2608) (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 662))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha3_shape hck3_shape
      change (denoteGraph sm initSM 663).shape = [1, 8, 32] ∧
        List.map (fun t => t.shape)
          ([({ rank := 0, tid := 2613 } : Piece), { rank := 1, tid := 2614 },
            { rank := 2, tid := 2615 }, { rank := 3, tid := 2616 }].map
            (fun p => denoteGraph pm initPM p.tid)) =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] ∧
        denoteGraph sm initSM 663 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 2613 } : Piece), { rank := 1, tid := 2614 },
              { rank := 2, tid := 2615 }, { rank := 3, tid := 2616 }].map
              (fun p => denoteGraph pm initPM p.tid))
      refine ⟨?_, ?_, ?_⟩
      · rw [sm_eval_663]
        exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 32] hXa_sm_shape' hXb_sm_shape'
      · simp only [List.map_cons, List.map_nil]
        rw [pm_eval_2613, pm_eval_2614, pm_eval_2615, pm_eval_2616]
        rw [pm_eval_2609, pm_eval_2610, pm_eval_2611, pm_eval_2612]
        simp only [List.cons.injEq, and_true]
        exact ⟨hpf0_shape, hpf1_shape, hpf2_shape, hpf3_shape⟩
      · simp only [List.map_cons, List.map_nil]
        rw [sm_eval_663]
        rw [pm_eval_2613, pm_eval_2614, pm_eval_2615, pm_eval_2616]
        rw [pm_eval_2609, pm_eval_2610, pm_eval_2611, pm_eval_2612]
        rw [← hXb_eq]
        rw [hXa_eq]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        · exact fw_add_dim1_with_x_pieces_4_1_2_32_to_1_8_32
            (denoteGraph pm initPM 2605) (denoteGraph pm initPM 2606)
            (denoteGraph pm initPM 2607) (denoteGraph pm initPM 2608)
            (denoteGraph sm initSM 662)
            ha0_shape ha1_shape ha2_shape ha3_shape
            (by rw [hXb_eq]; exact hXb_pm_shape)
        · rw [hXb_eq]
          rw [show (elemwiseAdd (denoteGraph pm initPM 2605) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 662))).shape = [1, 2, 32] from hpf0_shape]
          intro hbad
          cases hbad
  | goal_79 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hGoalX : goal_297_stmt := prove_pattern_128 pattern_128_target.goal_297
      have hGoalY : goal_78_stmt := prove_pattern_45 pattern_45_target.goal_78
      have hX := hGoalX initSM initPM hSmInit hPmInit hInitGoals
      have hY := hGoalY initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hXa_sm_shape, hXa_pm_shapes, hXa_eq_rec⟩ := hX
      obtain ⟨hXb_sm_shape, hXb_pm_shapes, hXb_eq_rec⟩ := hY
      have hXa_eq : denoteGraph sm initSM 1024 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2749, denoteGraph pm initPM 2750,
           denoteGraph pm initPM 2751, denoteGraph pm initPM 2752] := by
        have hh := hXa_eq_rec
        change denoteGraph sm initSM 1024 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 2749 } : Piece), { rank := 1, tid := 2750 },
              { rank := 2, tid := 2751 }, { rank := 3, tid := 2752 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 2749).shape = [1, 2, 32] by
          have hs := hXa_pm_shapes
          change [(denoteGraph pm initPM 2749).shape, (denoteGraph pm initPM 2750).shape,
            (denoteGraph pm initPM 2751).shape, (denoteGraph pm initPM 2752).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      have hXb_eq : denoteGraph sm initSM 671 = denoteGraph pm initPM 671 := by
        have hh := hXb_eq_rec
        change denoteGraph sm initSM 671 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 671 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) at hh
        simpa only [List.map_cons, List.map_nil, reconstructWithDim_singleton] using hh
      have hXa_sm_shape' : (denoteGraph sm initSM 1024).shape = [1, 8, 32] := by
        simpa [goal_297] using hXa_sm_shape
      have hXb_sm_shape' : (denoteGraph sm initSM 671).shape = [1, 8, 32] := by
        simpa [goal_78] using hXb_sm_shape
      have hXb_pm_shape : (denoteGraph pm initPM 671).shape = [1, 8, 32] := by
        rw [← hXb_eq]; exact hXb_sm_shape'
      have ⟨ha0_shape, ha1_shape, ha2_shape, ha3_shape⟩ : (denoteGraph pm initPM 2749).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2750).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2751).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2752).shape = [1, 2, 32] := by
        have hs := hXa_pm_shapes
        change [(denoteGraph pm initPM 2749).shape, (denoteGraph pm initPM 2750).shape,
          (denoteGraph pm initPM 2751).shape, (denoteGraph pm initPM 2752).shape] =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hck0_shape : (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 671)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 0 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck1_shape : (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 671)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 1 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck2_shape : (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 671)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 2 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck3_shape : (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 671)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 3 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hpf0_shape : (elemwiseAdd (denoteGraph pm initPM 2749) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 671))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha0_shape hck0_shape
      have hpf1_shape : (elemwiseAdd (denoteGraph pm initPM 2750) (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 671))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha1_shape hck1_shape
      have hpf2_shape : (elemwiseAdd (denoteGraph pm initPM 2751) (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 671))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha2_shape hck2_shape
      have hpf3_shape : (elemwiseAdd (denoteGraph pm initPM 2752) (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 671))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha3_shape hck3_shape
      change (denoteGraph sm initSM 672).shape = [1, 8, 32] ∧
        List.map (fun t => t.shape)
          ([({ rank := 0, tid := 2757 } : Piece), { rank := 1, tid := 2758 },
            { rank := 2, tid := 2759 }, { rank := 3, tid := 2760 }].map
            (fun p => denoteGraph pm initPM p.tid)) =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] ∧
        denoteGraph sm initSM 672 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 2757 } : Piece), { rank := 1, tid := 2758 },
              { rank := 2, tid := 2759 }, { rank := 3, tid := 2760 }].map
              (fun p => denoteGraph pm initPM p.tid))
      refine ⟨?_, ?_, ?_⟩
      · rw [sm_eval_672]
        exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 32] hXa_sm_shape' hXb_sm_shape'
      · simp only [List.map_cons, List.map_nil]
        rw [pm_eval_2757, pm_eval_2758, pm_eval_2759, pm_eval_2760]
        rw [pm_eval_2753, pm_eval_2754, pm_eval_2755, pm_eval_2756]
        simp only [List.cons.injEq, and_true]
        exact ⟨hpf0_shape, hpf1_shape, hpf2_shape, hpf3_shape⟩
      · simp only [List.map_cons, List.map_nil]
        rw [sm_eval_672]
        rw [pm_eval_2757, pm_eval_2758, pm_eval_2759, pm_eval_2760]
        rw [pm_eval_2753, pm_eval_2754, pm_eval_2755, pm_eval_2756]
        rw [← hXb_eq]
        rw [hXa_eq]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        · exact fw_add_dim1_with_x_pieces_4_1_2_32_to_1_8_32
            (denoteGraph pm initPM 2749) (denoteGraph pm initPM 2750)
            (denoteGraph pm initPM 2751) (denoteGraph pm initPM 2752)
            (denoteGraph sm initSM 671)
            ha0_shape ha1_shape ha2_shape ha3_shape
            (by rw [hXb_eq]; exact hXb_pm_shape)
        · rw [hXb_eq]
          rw [show (elemwiseAdd (denoteGraph pm initPM 2749) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 671))).shape = [1, 2, 32] from hpf0_shape]
          intro hbad
          cases hbad
  | goal_99 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hGoalX : goal_301_stmt := prove_pattern_128 pattern_128_target.goal_301
      have hGoalY : goal_98_stmt := prove_pattern_43 pattern_43_target.goal_98
      have hX := hGoalX initSM initPM hSmInit hPmInit hInitGoals
      have hY := hGoalY initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hXa_sm_shape, hXa_pm_shapes, hXa_eq_rec⟩ := hX
      obtain ⟨hXb_sm_shape, hXb_pm_shapes, hXb_eq_rec⟩ := hY
      have hXa_eq : denoteGraph sm initSM 1036 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 3169, denoteGraph pm initPM 3170,
           denoteGraph pm initPM 3171, denoteGraph pm initPM 3172] := by
        have hh := hXa_eq_rec
        change denoteGraph sm initSM 1036 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 3169 } : Piece), { rank := 1, tid := 3170 },
              { rank := 2, tid := 3171 }, { rank := 3, tid := 3172 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 3169).shape = [1, 2, 32] by
          have hs := hXa_pm_shapes
          change [(denoteGraph pm initPM 3169).shape, (denoteGraph pm initPM 3170).shape,
            (denoteGraph pm initPM 3171).shape, (denoteGraph pm initPM 3172).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      have hXb_eq : denoteGraph sm initSM 697 = denoteGraph pm initPM 697 := by
        have hh := hXb_eq_rec
        change denoteGraph sm initSM 697 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 697 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) at hh
        simpa only [List.map_cons, List.map_nil, reconstructWithDim_singleton] using hh
      have hXa_sm_shape' : (denoteGraph sm initSM 1036).shape = [1, 8, 32] := by
        simpa [goal_301] using hXa_sm_shape
      have hXb_sm_shape' : (denoteGraph sm initSM 697).shape = [1, 8, 32] := by
        simpa [goal_98] using hXb_sm_shape
      have hXb_pm_shape : (denoteGraph pm initPM 697).shape = [1, 8, 32] := by
        rw [← hXb_eq]; exact hXb_sm_shape'
      have ⟨ha0_shape, ha1_shape, ha2_shape, ha3_shape⟩ : (denoteGraph pm initPM 3169).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3170).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3171).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3172).shape = [1, 2, 32] := by
        have hs := hXa_pm_shapes
        change [(denoteGraph pm initPM 3169).shape, (denoteGraph pm initPM 3170).shape,
          (denoteGraph pm initPM 3171).shape, (denoteGraph pm initPM 3172).shape] =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hck0_shape : (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 697)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 0 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck1_shape : (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 697)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 1 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck2_shape : (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 697)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 2 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck3_shape : (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 697)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 3 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hpf0_shape : (elemwiseAdd (denoteGraph pm initPM 3169) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 697))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha0_shape hck0_shape
      have hpf1_shape : (elemwiseAdd (denoteGraph pm initPM 3170) (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 697))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha1_shape hck1_shape
      have hpf2_shape : (elemwiseAdd (denoteGraph pm initPM 3171) (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 697))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha2_shape hck2_shape
      have hpf3_shape : (elemwiseAdd (denoteGraph pm initPM 3172) (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 697))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha3_shape hck3_shape
      change (denoteGraph sm initSM 698).shape = [1, 8, 32] ∧
        List.map (fun t => t.shape)
          ([({ rank := 0, tid := 3177 } : Piece), { rank := 1, tid := 3178 },
            { rank := 2, tid := 3179 }, { rank := 3, tid := 3180 }].map
            (fun p => denoteGraph pm initPM p.tid)) =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] ∧
        denoteGraph sm initSM 698 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 3177 } : Piece), { rank := 1, tid := 3178 },
              { rank := 2, tid := 3179 }, { rank := 3, tid := 3180 }].map
              (fun p => denoteGraph pm initPM p.tid))
      refine ⟨?_, ?_, ?_⟩
      · rw [sm_eval_698]
        exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 32] hXa_sm_shape' hXb_sm_shape'
      · simp only [List.map_cons, List.map_nil]
        rw [pm_eval_3177, pm_eval_3178, pm_eval_3179, pm_eval_3180]
        rw [pm_eval_3173, pm_eval_3174, pm_eval_3175, pm_eval_3176]
        simp only [List.cons.injEq, and_true]
        exact ⟨hpf0_shape, hpf1_shape, hpf2_shape, hpf3_shape⟩
      · simp only [List.map_cons, List.map_nil]
        rw [sm_eval_698]
        rw [pm_eval_3177, pm_eval_3178, pm_eval_3179, pm_eval_3180]
        rw [pm_eval_3173, pm_eval_3174, pm_eval_3175, pm_eval_3176]
        rw [← hXb_eq]
        rw [hXa_eq]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        · exact fw_add_dim1_with_x_pieces_4_1_2_32_to_1_8_32
            (denoteGraph pm initPM 3169) (denoteGraph pm initPM 3170)
            (denoteGraph pm initPM 3171) (denoteGraph pm initPM 3172)
            (denoteGraph sm initSM 697)
            ha0_shape ha1_shape ha2_shape ha3_shape
            (by rw [hXb_eq]; exact hXb_pm_shape)
        · rw [hXb_eq]
          rw [show (elemwiseAdd (denoteGraph pm initPM 3169) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 697))).shape = [1, 2, 32] from hpf0_shape]
          intro hbad
          cases hbad
  | goal_104 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hGoalX : goal_311_stmt := prove_pattern_128 pattern_128_target.goal_311
      have hGoalY : goal_103_stmt := prove_pattern_45 pattern_45_target.goal_103
      have hX := hGoalX initSM initPM hSmInit hPmInit hInitGoals
      have hY := hGoalY initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hXa_sm_shape, hXa_pm_shapes, hXa_eq_rec⟩ := hX
      obtain ⟨hXb_sm_shape, hXb_pm_shapes, hXb_eq_rec⟩ := hY
      have hXa_eq : denoteGraph sm initSM 1067 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 3313, denoteGraph pm initPM 3314,
           denoteGraph pm initPM 3315, denoteGraph pm initPM 3316] := by
        have hh := hXa_eq_rec
        change denoteGraph sm initSM 1067 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 3313 } : Piece), { rank := 1, tid := 3314 },
              { rank := 2, tid := 3315 }, { rank := 3, tid := 3316 }].map
              (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        rw [show (denoteGraph pm initPM 3313).shape = [1, 2, 32] by
          have hs := hXa_pm_shapes
          change [(denoteGraph pm initPM 3313).shape, (denoteGraph pm initPM 3314).shape,
            (denoteGraph pm initPM 3315).shape, (denoteGraph pm initPM 3316).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
          have hs0 := congrArg List.head? hs
          simpa using hs0]
        intro hbad
        cases hbad
      have hXb_eq : denoteGraph sm initSM 706 = denoteGraph pm initPM 706 := by
        have hh := hXb_eq_rec
        change denoteGraph sm initSM 706 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 706 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) at hh
        simpa only [List.map_cons, List.map_nil, reconstructWithDim_singleton] using hh
      have hXa_sm_shape' : (denoteGraph sm initSM 1067).shape = [1, 8, 32] := by
        simpa [goal_311] using hXa_sm_shape
      have hXb_sm_shape' : (denoteGraph sm initSM 706).shape = [1, 8, 32] := by
        simpa [goal_103] using hXb_sm_shape
      have hXb_pm_shape : (denoteGraph pm initPM 706).shape = [1, 8, 32] := by
        rw [← hXb_eq]; exact hXb_sm_shape'
      have ⟨ha0_shape, ha1_shape, ha2_shape, ha3_shape⟩ : (denoteGraph pm initPM 3313).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3314).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3315).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 3316).shape = [1, 2, 32] := by
        have hs := hXa_pm_shapes
        change [(denoteGraph pm initPM 3313).shape, (denoteGraph pm initPM 3314).shape,
          (denoteGraph pm initPM 3315).shape, (denoteGraph pm initPM 3316).shape] =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] at hs
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hck0_shape : (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 706)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 0 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck1_shape : (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 706)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 1 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck2_shape : (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 706)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 2 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hck3_shape : (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 706)).shape = [1, 2, 32] := by
        rw [chunkPrimDimN_shape 1 4 3 _ _ hXb_pm_shape (by omega)]; simp [List.set, List.getD]
      have hpf0_shape : (elemwiseAdd (denoteGraph pm initPM 3313) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 706))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha0_shape hck0_shape
      have hpf1_shape : (elemwiseAdd (denoteGraph pm initPM 3314) (chunkPrimDimN 1 4 1 (denoteGraph pm initPM 706))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha1_shape hck1_shape
      have hpf2_shape : (elemwiseAdd (denoteGraph pm initPM 3315) (chunkPrimDimN 1 4 2 (denoteGraph pm initPM 706))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha2_shape hck2_shape
      have hpf3_shape : (elemwiseAdd (denoteGraph pm initPM 3316) (chunkPrimDimN 1 4 3 (denoteGraph pm initPM 706))).shape = [1, 2, 32] :=
        elemwiseAdd_shape_of_shapes _ _ [1, 2, 32] ha3_shape hck3_shape
      change (denoteGraph sm initSM 707).shape = [1, 8, 32] ∧
        List.map (fun t => t.shape)
          ([({ rank := 0, tid := 3321 } : Piece), { rank := 1, tid := 3322 },
            { rank := 2, tid := 3323 }, { rank := 3, tid := 3324 }].map
            (fun p => denoteGraph pm initPM p.tid)) =
          [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] ∧
        denoteGraph sm initSM 707 =
          reconstructWithDim 1 pm.numRanks 0
            ([({ rank := 0, tid := 3321 } : Piece), { rank := 1, tid := 3322 },
              { rank := 2, tid := 3323 }, { rank := 3, tid := 3324 }].map
              (fun p => denoteGraph pm initPM p.tid))
      refine ⟨?_, ?_, ?_⟩
      · rw [sm_eval_707]
        exact elemwiseAdd_shape_of_shapes _ _ [1, 8, 32] hXa_sm_shape' hXb_sm_shape'
      · simp only [List.map_cons, List.map_nil]
        rw [pm_eval_3321, pm_eval_3322, pm_eval_3323, pm_eval_3324]
        rw [pm_eval_3317, pm_eval_3318, pm_eval_3319, pm_eval_3320]
        simp only [List.cons.injEq, and_true]
        exact ⟨hpf0_shape, hpf1_shape, hpf2_shape, hpf3_shape⟩
      · simp only [List.map_cons, List.map_nil]
        rw [sm_eval_707]
        rw [pm_eval_3321, pm_eval_3322, pm_eval_3323, pm_eval_3324]
        rw [pm_eval_3317, pm_eval_3318, pm_eval_3319, pm_eval_3320]
        rw [← hXb_eq]
        rw [hXa_eq]
        rw [show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar]
        · exact fw_add_dim1_with_x_pieces_4_1_2_32_to_1_8_32
            (denoteGraph pm initPM 3313) (denoteGraph pm initPM 3314)
            (denoteGraph pm initPM 3315) (denoteGraph pm initPM 3316)
            (denoteGraph sm initSM 706)
            ha0_shape ha1_shape ha2_shape ha3_shape
            (by rw [hXb_eq]; exact hXb_pm_shape)
        · rw [hXb_eq]
          rw [show (elemwiseAdd (denoteGraph pm initPM 3313) (chunkPrimDimN 1 4 0 (denoteGraph pm initPM 706))).shape = [1, 2, 32] from hpf0_shape]
          intro hbad
          cases hbad

end TrainVerify.Denote.GeneratedPatterns
