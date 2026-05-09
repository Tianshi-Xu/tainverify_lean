/- Auto-generated pattern proof file.
   Pattern: 8
   Hash: e82f3b2e5c42daaa
   Goals: 9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_6
import denote.gpt_ly4_segments.Pattern_7
import denote.gpt_ly4_segments.Pattern_25

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_8_goalIds : List Nat := [9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88]
inductive pattern_8_target : Prop → Prop
  | goal_9 : pattern_8_target goal_9_stmt
  | goal_11 : pattern_8_target goal_11_stmt
  | goal_13 : pattern_8_target goal_13_stmt
  | goal_34 : pattern_8_target goal_34_stmt
  | goal_36 : pattern_8_target goal_36_stmt
  | goal_38 : pattern_8_target goal_38_stmt
  | goal_59 : pattern_8_target goal_59_stmt
  | goal_61 : pattern_8_target goal_61_stmt
  | goal_63 : pattern_8_target goal_63_stmt
  | goal_84 : pattern_8_target goal_84_stmt
  | goal_86 : pattern_8_target goal_86_stmt
  | goal_88 : pattern_8_target goal_88_stmt

def pattern_8_stmt : Prop :=
  ∀ {target : Prop}, pattern_8_target target → target

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## Helper: applyNode for FW_view with params [1,8,4,8]. -/

private theorem evalOp_fw_view_1_8_4_8 (numParts rank : Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_view" [1, 8, 4, 8] [x] =
      [fw_view [1, 8, 4, 8] x] := rfl

private theorem applyNode_fw_view_1_8_4_8
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_view", ins := [xTid], outs := [outTid], params := [1, 8, 4, 8] } outTid =
      fw_view [1, 8, 4, 8] (s xTid) := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl,
      evalOp_fw_view_1_8_4_8]
  change storeSet s [(outTid, fw_view [1, 8, 4, 8] (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-! ## Shape lemma for fw_view. -/

private theorem fw_view_shape (sh : Shape) (x : Tensor) :
    (fw_view sh x).shape = sh := rfl

/-! ## SM evaluation lemmas. -/

@[reducible] private def sm_n577 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [572], outs := [577], params := [1, 8, 4, 8] }
@[reducible] private def sm_n579 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [574], outs := [579], params := [1, 8, 4, 8] }
@[reducible] private def sm_n581 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [576], outs := [581], params := [1, 8, 4, 8] }
@[reducible] private def sm_n612 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [607], outs := [612], params := [1, 8, 4, 8] }
@[reducible] private def sm_n614 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [609], outs := [614], params := [1, 8, 4, 8] }
@[reducible] private def sm_n616 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [611], outs := [616], params := [1, 8, 4, 8] }
@[reducible] private def sm_n647 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [642], outs := [647], params := [1, 8, 4, 8] }
@[reducible] private def sm_n649 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [644], outs := [649], params := [1, 8, 4, 8] }
@[reducible] private def sm_n651 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [646], outs := [651], params := [1, 8, 4, 8] }
@[reducible] private def sm_n682 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [677], outs := [682], params := [1, 8, 4, 8] }
@[reducible] private def sm_n684 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [679], outs := [684], params := [1, 8, 4, 8] }
@[reducible] private def sm_n686 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [681], outs := [686], params := [1, 8, 4, 8] }

private theorem sm_eval_577 (initSM : Store) :
    denoteGraph sm initSM 577 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 572) := by
  have hsub : (denoteGraph sm initSM) 577 =
      (denoteGraph { sm with nodes := sm.nodes.take 10 } initSM) 577 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 577
      (sm.nodes.take 10) (sm.nodes.drop 10)
      (List.take_append_drop 10 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 10 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 9 ++ [sm_n577] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n577] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n577 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n577 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 9 } initSM) 572 =
      (denoteGraph sm initSM) 572 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 572
      (sm.nodes.take 9) (sm.nodes.drop 9)
      (List.take_append_drop 9 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_579 (initSM : Store) :
    denoteGraph sm initSM 579 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 574) := by
  have hsub : (denoteGraph sm initSM) 579 =
      (denoteGraph { sm with nodes := sm.nodes.take 11 } initSM) 579 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 579
      (sm.nodes.take 11) (sm.nodes.drop 11)
      (List.take_append_drop 11 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 11 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 10 ++ [sm_n579] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n579] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n579 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n579 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 10 } initSM) 574 =
      (denoteGraph sm initSM) 574 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 574
      (sm.nodes.take 10) (sm.nodes.drop 10)
      (List.take_append_drop 10 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_581 (initSM : Store) :
    denoteGraph sm initSM 581 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 576) := by
  have hsub : (denoteGraph sm initSM) 581 =
      (denoteGraph { sm with nodes := sm.nodes.take 12 } initSM) 581 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 581
      (sm.nodes.take 12) (sm.nodes.drop 12)
      (List.take_append_drop 12 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 12 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 11 ++ [sm_n581] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n581] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n581 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n581 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 11 } initSM) 576 =
      (denoteGraph sm initSM) 576 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 576
      (sm.nodes.take 11) (sm.nodes.drop 11)
      (List.take_append_drop 11 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_612 (initSM : Store) :
    denoteGraph sm initSM 612 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 607) := by
  have hsub : (denoteGraph sm initSM) 612 =
      (denoteGraph { sm with nodes := sm.nodes.take 38 } initSM) 612 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 612
      (sm.nodes.take 38) (sm.nodes.drop 38)
      (List.take_append_drop 38 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 38 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 37 ++ [sm_n612] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n612] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n612 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n612 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 37 } initSM) 607 =
      (denoteGraph sm initSM) 607 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 607
      (sm.nodes.take 37) (sm.nodes.drop 37)
      (List.take_append_drop 37 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_614 (initSM : Store) :
    denoteGraph sm initSM 614 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 609) := by
  have hsub : (denoteGraph sm initSM) 614 =
      (denoteGraph { sm with nodes := sm.nodes.take 39 } initSM) 614 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 614
      (sm.nodes.take 39) (sm.nodes.drop 39)
      (List.take_append_drop 39 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 39 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 38 ++ [sm_n614] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n614] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n614 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n614 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 38 } initSM) 609 =
      (denoteGraph sm initSM) 609 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 609
      (sm.nodes.take 38) (sm.nodes.drop 38)
      (List.take_append_drop 38 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_616 (initSM : Store) :
    denoteGraph sm initSM 616 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 611) := by
  have hsub : (denoteGraph sm initSM) 616 =
      (denoteGraph { sm with nodes := sm.nodes.take 40 } initSM) 616 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 616
      (sm.nodes.take 40) (sm.nodes.drop 40)
      (List.take_append_drop 40 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 40 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 39 ++ [sm_n616] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n616] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n616 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n616 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 39 } initSM) 611 =
      (denoteGraph sm initSM) 611 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 611
      (sm.nodes.take 39) (sm.nodes.drop 39)
      (List.take_append_drop 39 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_647 (initSM : Store) :
    denoteGraph sm initSM 647 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 642) := by
  have hsub : (denoteGraph sm initSM) 647 =
      (denoteGraph { sm with nodes := sm.nodes.take 66 } initSM) 647 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 647
      (sm.nodes.take 66) (sm.nodes.drop 66)
      (List.take_append_drop 66 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 66 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 65 ++ [sm_n647] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n647] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n647 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n647 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 65 } initSM) 642 =
      (denoteGraph sm initSM) 642 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 642
      (sm.nodes.take 65) (sm.nodes.drop 65)
      (List.take_append_drop 65 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_649 (initSM : Store) :
    denoteGraph sm initSM 649 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 644) := by
  have hsub : (denoteGraph sm initSM) 649 =
      (denoteGraph { sm with nodes := sm.nodes.take 67 } initSM) 649 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 649
      (sm.nodes.take 67) (sm.nodes.drop 67)
      (List.take_append_drop 67 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 67 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 66 ++ [sm_n649] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n649] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n649 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n649 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 66 } initSM) 644 =
      (denoteGraph sm initSM) 644 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 644
      (sm.nodes.take 66) (sm.nodes.drop 66)
      (List.take_append_drop 66 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_651 (initSM : Store) :
    denoteGraph sm initSM 651 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 646) := by
  have hsub : (denoteGraph sm initSM) 651 =
      (denoteGraph { sm with nodes := sm.nodes.take 68 } initSM) 651 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 651
      (sm.nodes.take 68) (sm.nodes.drop 68)
      (List.take_append_drop 68 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 68 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 67 ++ [sm_n651] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n651] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n651 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n651 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 67 } initSM) 646 =
      (denoteGraph sm initSM) 646 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 646
      (sm.nodes.take 67) (sm.nodes.drop 67)
      (List.take_append_drop 67 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_682 (initSM : Store) :
    denoteGraph sm initSM 682 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 677) := by
  have hsub : (denoteGraph sm initSM) 682 =
      (denoteGraph { sm with nodes := sm.nodes.take 94 } initSM) 682 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 682
      (sm.nodes.take 94) (sm.nodes.drop 94)
      (List.take_append_drop 94 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 94 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 93 ++ [sm_n682] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n682] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n682 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n682 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 93 } initSM) 677 =
      (denoteGraph sm initSM) 677 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 677
      (sm.nodes.take 93) (sm.nodes.drop 93)
      (List.take_append_drop 93 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_684 (initSM : Store) :
    denoteGraph sm initSM 684 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 679) := by
  have hsub : (denoteGraph sm initSM) 684 =
      (denoteGraph { sm with nodes := sm.nodes.take 95 } initSM) 684 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 684
      (sm.nodes.take 95) (sm.nodes.drop 95)
      (List.take_append_drop 95 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 95 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 94 ++ [sm_n684] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n684] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n684 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n684 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 94 } initSM) 679 =
      (denoteGraph sm initSM) 679 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 679
      (sm.nodes.take 94) (sm.nodes.drop 94)
      (List.take_append_drop 94 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem sm_eval_686 (initSM : Store) :
    denoteGraph sm initSM 686 = fw_view [1, 8, 4, 8] (denoteGraph sm initSM 681) := by
  have hsub : (denoteGraph sm initSM) 686 =
      (denoteGraph { sm with nodes := sm.nodes.take 96 } initSM) 686 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 686
      (sm.nodes.take 96) (sm.nodes.drop 96)
      (List.take_append_drop 96 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 96 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 95 ++ [sm_n686] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [sm_n686] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := sm_n686 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm sm_n686 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { sm with nodes := sm.nodes.take 95 } initSM) 681 =
      (denoteGraph sm initSM) 681 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 681
      (sm.nodes.take 95) (sm.nodes.drop 95)
      (List.take_append_drop 95 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

/-! ## PM evaluation lemmas (rank=3 last write). -/

@[reducible] private def pm_n577 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [572], outs := [577], params := [1, 8, 4, 8] }
@[reducible] private def pm_n579 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [574], outs := [579], params := [1, 8, 4, 8] }
@[reducible] private def pm_n581 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [576], outs := [581], params := [1, 8, 4, 8] }
@[reducible] private def pm_n612 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [607], outs := [612], params := [1, 8, 4, 8] }
@[reducible] private def pm_n614 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [609], outs := [614], params := [1, 8, 4, 8] }
@[reducible] private def pm_n616 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [611], outs := [616], params := [1, 8, 4, 8] }
@[reducible] private def pm_n647 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [642], outs := [647], params := [1, 8, 4, 8] }
@[reducible] private def pm_n649 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [644], outs := [649], params := [1, 8, 4, 8] }
@[reducible] private def pm_n651 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [646], outs := [651], params := [1, 8, 4, 8] }
@[reducible] private def pm_n682 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [677], outs := [682], params := [1, 8, 4, 8] }
@[reducible] private def pm_n684 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [679], outs := [684], params := [1, 8, 4, 8] }
@[reducible] private def pm_n686 : NodeDecl :=
  { rank := 3, op := "OpName.FW_view", ins := [681], outs := [686], params := [1, 8, 4, 8] }

private theorem pm_eval_577 (initPM : Store) :
    denoteGraph pm initPM 577 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 572) := by
  have hsub : (denoteGraph pm initPM) 577 =
      (denoteGraph { pm with nodes := pm.nodes.take 61 } initPM) 577 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 577
      (pm.nodes.take 61) (pm.nodes.drop 61)
      (List.take_append_drop 61 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 61 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 60 ++ [pm_n577] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n577] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n577 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n577 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 60 } initPM) 572 =
      (denoteGraph pm initPM) 572 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 572
      (pm.nodes.take 60) (pm.nodes.drop 60)
      (List.take_append_drop 60 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_579 (initPM : Store) :
    denoteGraph pm initPM 579 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 574) := by
  have hsub : (denoteGraph pm initPM) 579 =
      (denoteGraph { pm with nodes := pm.nodes.take 65 } initPM) 579 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 579
      (pm.nodes.take 65) (pm.nodes.drop 65)
      (List.take_append_drop 65 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 65 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 64 ++ [pm_n579] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n579] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n579 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n579 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 64 } initPM) 574 =
      (denoteGraph pm initPM) 574 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 574
      (pm.nodes.take 64) (pm.nodes.drop 64)
      (List.take_append_drop 64 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_581 (initPM : Store) :
    denoteGraph pm initPM 581 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 576) := by
  have hsub : (denoteGraph pm initPM) 581 =
      (denoteGraph { pm with nodes := pm.nodes.take 69 } initPM) 581 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 581
      (pm.nodes.take 69) (pm.nodes.drop 69)
      (List.take_append_drop 69 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 69 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 68 ++ [pm_n581] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n581] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n581 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n581 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 68 } initPM) 576 =
      (denoteGraph pm initPM) 576 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 576
      (pm.nodes.take 68) (pm.nodes.drop 68)
      (List.take_append_drop 68 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_612 (initPM : Store) :
    denoteGraph pm initPM 612 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 607) := by
  have hsub : (denoteGraph pm initPM) 612 =
      (denoteGraph { pm with nodes := pm.nodes.take 236 } initPM) 612 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 612
      (pm.nodes.take 236) (pm.nodes.drop 236)
      (List.take_append_drop 236 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 236 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 235 ++ [pm_n612] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n612] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n612 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n612 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 235 } initPM) 607 =
      (denoteGraph pm initPM) 607 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 607
      (pm.nodes.take 235) (pm.nodes.drop 235)
      (List.take_append_drop 235 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_614 (initPM : Store) :
    denoteGraph pm initPM 614 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 609) := by
  have hsub : (denoteGraph pm initPM) 614 =
      (denoteGraph { pm with nodes := pm.nodes.take 231 } initPM) 614 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 614
      (pm.nodes.take 231) (pm.nodes.drop 231)
      (List.take_append_drop 231 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 231 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 230 ++ [pm_n614] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n614] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n614 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n614 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 230 } initPM) 609 =
      (denoteGraph pm initPM) 609 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 609
      (pm.nodes.take 230) (pm.nodes.drop 230)
      (List.take_append_drop 230 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_616 (initPM : Store) :
    denoteGraph pm initPM 616 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 611) := by
  have hsub : (denoteGraph pm initPM) 616 =
      (denoteGraph { pm with nodes := pm.nodes.take 244 } initPM) 616 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 616
      (pm.nodes.take 244) (pm.nodes.drop 244)
      (List.take_append_drop 244 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 244 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 243 ++ [pm_n616] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n616] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n616 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n616 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 243 } initPM) 611 =
      (denoteGraph pm initPM) 611 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 611
      (pm.nodes.take 243) (pm.nodes.drop 243)
      (List.take_append_drop 243 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_647 (initPM : Store) :
    denoteGraph pm initPM 647 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 642) := by
  have hsub : (denoteGraph pm initPM) 647 =
      (denoteGraph { pm with nodes := pm.nodes.take 425 } initPM) 647 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 647
      (pm.nodes.take 425) (pm.nodes.drop 425)
      (List.take_append_drop 425 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 425 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 424 ++ [pm_n647] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n647] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n647 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n647 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 424 } initPM) 642 =
      (denoteGraph pm initPM) 642 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 642
      (pm.nodes.take 424) (pm.nodes.drop 424)
      (List.take_append_drop 424 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_649 (initPM : Store) :
    denoteGraph pm initPM 649 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 644) := by
  have hsub : (denoteGraph pm initPM) 649 =
      (denoteGraph { pm with nodes := pm.nodes.take 429 } initPM) 649 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 649
      (pm.nodes.take 429) (pm.nodes.drop 429)
      (List.take_append_drop 429 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 429 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 428 ++ [pm_n649] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n649] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n649 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n649 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 428 } initPM) 644 =
      (denoteGraph pm initPM) 644 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 644
      (pm.nodes.take 428) (pm.nodes.drop 428)
      (List.take_append_drop 428 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_651 (initPM : Store) :
    denoteGraph pm initPM 651 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 646) := by
  have hsub : (denoteGraph pm initPM) 651 =
      (denoteGraph { pm with nodes := pm.nodes.take 421 } initPM) 651 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 651
      (pm.nodes.take 421) (pm.nodes.drop 421)
      (List.take_append_drop 421 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 421 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 420 ++ [pm_n651] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n651] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n651 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n651 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 420 } initPM) 646 =
      (denoteGraph pm initPM) 646 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 646
      (pm.nodes.take 420) (pm.nodes.drop 420)
      (List.take_append_drop 420 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_682 (initPM : Store) :
    denoteGraph pm initPM 682 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 677) := by
  have hsub : (denoteGraph pm initPM) 682 =
      (denoteGraph { pm with nodes := pm.nodes.take 613 } initPM) 682 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 682
      (pm.nodes.take 613) (pm.nodes.drop 613)
      (List.take_append_drop 613 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 613 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 612 ++ [pm_n682] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n682] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n682 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n682 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 612 } initPM) 677 =
      (denoteGraph pm initPM) 677 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 677
      (pm.nodes.take 612) (pm.nodes.drop 612)
      (List.take_append_drop 612 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_684 (initPM : Store) :
    denoteGraph pm initPM 684 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 679) := by
  have hsub : (denoteGraph pm initPM) 684 =
      (denoteGraph { pm with nodes := pm.nodes.take 617 } initPM) 684 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 684
      (pm.nodes.take 617) (pm.nodes.drop 617)
      (List.take_append_drop 617 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 617 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 616 ++ [pm_n684] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n684] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n684 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n684 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 616 } initPM) 679 =
      (denoteGraph pm initPM) 679 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 679
      (pm.nodes.take 616) (pm.nodes.drop 616)
      (List.take_append_drop 616 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

private theorem pm_eval_686 (initPM : Store) :
    denoteGraph pm initPM 686 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 681) := by
  have hsub : (denoteGraph pm initPM) 686 =
      (denoteGraph { pm with nodes := pm.nodes.take 609 } initPM) 686 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 686
      (pm.nodes.take 609) (pm.nodes.drop 609)
      (List.take_append_drop 609 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 609 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 608 ++ [pm_n686] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [pm_n686] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := pm_n686 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm pm_n686 []]
  simp only [denoteGraph_nodes_nil]
  rw [applyNode_fw_view_1_8_4_8]
  have hin : (denoteGraph { pm with nodes := pm.nodes.take 608 } initPM) 681 =
      (denoteGraph pm initPM) 681 := by
    have h := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 681
      (pm.nodes.take 608) (pm.nodes.drop 608)
      (List.take_append_drop 608 _).symm
      (by set_option maxRecDepth 20000 in decide)
    exact h.symm
  rw [hin]

theorem prove_pattern_8 : pattern_8_stmt := by
  intro target h
  cases h
  all_goals (intro initSM initPM hSmInit hPmInit hInitGoals)
  -- Goal 9: ts=577, in=572, bridge=goal_6 (P6)
  · have hBridge := prove_pattern_6 (target := goal_6_stmt) .goal_6
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 572 = denoteGraph pm initPM 572 := by
      have hh := hgB.2.2
      simp only [goal_6, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 577).shape = [1, 8, 4, 8]
      rw [sm_eval_577]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 577 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_577]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 577 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 577 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_577, pm_eval_577, hSM_eq_PM]
  -- Goal 11: ts=579, in=574, bridge=goal_7 (P6)
  · have hBridge := prove_pattern_6 (target := goal_7_stmt) .goal_7
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 574 = denoteGraph pm initPM 574 := by
      have hh := hgB.2.2
      simp only [goal_7, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 579).shape = [1, 8, 4, 8]
      rw [sm_eval_579]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 579 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_579]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 579 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 579 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_579, pm_eval_579, hSM_eq_PM]
  -- Goal 13: ts=581, in=576, bridge=goal_8 (P7)
  · have hBridge := prove_pattern_7 (target := goal_8_stmt) .goal_8
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 576 = denoteGraph pm initPM 576 := by
      have hh := hgB.2.2
      simp only [goal_8, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 581).shape = [1, 8, 4, 8]
      rw [sm_eval_581]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 581 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_581]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 581 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 581 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_581, pm_eval_581, hSM_eq_PM]
  -- Goal 34: ts=612, in=607, bridge=goal_31 (P25)
  · have hBridge := prove_pattern_25 (target := goal_31_stmt) .goal_31
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 607 = denoteGraph pm initPM 607 := by
      have hh := hgB.2.2
      simp only [goal_31, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 612).shape = [1, 8, 4, 8]
      rw [sm_eval_612]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 612 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_612]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 612 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 612 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_612, pm_eval_612, hSM_eq_PM]
  -- Goal 36: ts=614, in=609, bridge=goal_32 (P6)
  · have hBridge := prove_pattern_6 (target := goal_32_stmt) .goal_32
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 609 = denoteGraph pm initPM 609 := by
      have hh := hgB.2.2
      simp only [goal_32, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 614).shape = [1, 8, 4, 8]
      rw [sm_eval_614]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 614 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_614]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 614 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 614 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_614, pm_eval_614, hSM_eq_PM]
  -- Goal 38: ts=616, in=611, bridge=goal_33 (P25)
  · have hBridge := prove_pattern_25 (target := goal_33_stmt) .goal_33
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 611 = denoteGraph pm initPM 611 := by
      have hh := hgB.2.2
      simp only [goal_33, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 616).shape = [1, 8, 4, 8]
      rw [sm_eval_616]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 616 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_616]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 616 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 616 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_616, pm_eval_616, hSM_eq_PM]
  -- Goal 59: ts=647, in=642, bridge=goal_56 (P7)
  · have hBridge := prove_pattern_7 (target := goal_56_stmt) .goal_56
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 642 = denoteGraph pm initPM 642 := by
      have hh := hgB.2.2
      simp only [goal_56, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 647).shape = [1, 8, 4, 8]
      rw [sm_eval_647]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 647 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_647]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 647 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 647 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_647, pm_eval_647, hSM_eq_PM]
  -- Goal 61: ts=649, in=644, bridge=goal_57 (P7)
  · have hBridge := prove_pattern_7 (target := goal_57_stmt) .goal_57
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 644 = denoteGraph pm initPM 644 := by
      have hh := hgB.2.2
      simp only [goal_57, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 649).shape = [1, 8, 4, 8]
      rw [sm_eval_649]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 649 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_649]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 649 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 649 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_649, pm_eval_649, hSM_eq_PM]
  -- Goal 63: ts=651, in=646, bridge=goal_58 (P6)
  · have hBridge := prove_pattern_6 (target := goal_58_stmt) .goal_58
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 646 = denoteGraph pm initPM 646 := by
      have hh := hgB.2.2
      simp only [goal_58, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 651).shape = [1, 8, 4, 8]
      rw [sm_eval_651]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 651 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_651]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 651 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 651 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_651, pm_eval_651, hSM_eq_PM]
  -- Goal 84: ts=682, in=677, bridge=goal_81 (P25)
  · have hBridge := prove_pattern_25 (target := goal_81_stmt) .goal_81
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 677 = denoteGraph pm initPM 677 := by
      have hh := hgB.2.2
      simp only [goal_81, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 682).shape = [1, 8, 4, 8]
      rw [sm_eval_682]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 682 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_682]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 682 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 682 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_682, pm_eval_682, hSM_eq_PM]
  -- Goal 86: ts=684, in=679, bridge=goal_82 (P25)
  · have hBridge := prove_pattern_25 (target := goal_82_stmt) .goal_82
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 679 = denoteGraph pm initPM 679 := by
      have hh := hgB.2.2
      simp only [goal_82, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 684).shape = [1, 8, 4, 8]
      rw [sm_eval_684]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 684 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_684]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 684 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 684 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_684, pm_eval_684, hSM_eq_PM]
  -- Goal 88: ts=686, in=681, bridge=goal_83 (P6)
  · have hBridge := prove_pattern_6 (target := goal_83_stmt) .goal_83
    have hgB := hBridge initSM initPM hSmInit hPmInit hInitGoals
    have hSM_eq_PM : denoteGraph sm initSM 681 = denoteGraph pm initPM 681 := by
      have hh := hgB.2.2
      simp only [goal_83, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
      exact hh
    refine ⟨?_, ?_, ?_⟩
    · show (denoteGraph sm initSM 686).shape = [1, 8, 4, 8]
      rw [sm_eval_686]
      exact fw_view_shape _ _
    · show List.map (fun t => Tensor.shape t)
          ([({ rank := 0, tid := 686 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) = [[1, 8, 4, 8]]
      simp only [List.map_cons, List.map_nil]
      rw [pm_eval_686]
      exact congrArg (fun s => [s]) (fw_view_shape _ _)
    · show denoteGraph sm initSM 686 =
          reconstructWithDim 0 pm.numRanks 0
            ([({ rank := 0, tid := 686 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
      simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
      rw [sm_eval_686, pm_eval_686, hSM_eq_PM]

end TrainVerify.Denote.GeneratedPatterns
