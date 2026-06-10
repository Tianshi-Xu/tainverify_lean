/- Auto-generated pattern proof file.
   Pattern: 28
   Hash: bb72061ee5790bea
   Goals: 41
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_26
import denote.gpt_ly4_segments.Pattern_27

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

def pattern_28_goalIds : List Nat := [41]
inductive pattern_28_target : Prop → Prop
  | goal_41 : pattern_28_target goal_41_stmt

def pattern_28_stmt : Prop :=
  ∀ {target : Prop}, pattern_28_target target → target

@[reducible] private def p28_aa1873 : NodeDecl :=
  { rank := 0, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1873], params := [2, 1] }
@[reducible] private def p28_aa1874 : NodeDecl :=
  { rank := 1, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1874], params := [2, 1] }
@[reducible] private def p28_aa1875 : NodeDecl :=
  { rank := 2, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1875], params := [2, 1] }
@[reducible] private def p28_aa1876 : NodeDecl :=
  { rank := 3, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1876], params := [2, 1] }
@[reducible] private def p28_aa1877 : NodeDecl :=
  { rank := 0, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1877], params := [3, 1] }
@[reducible] private def p28_aa1878 : NodeDecl :=
  { rank := 1, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1878], params := [3, 1] }
@[reducible] private def p28_aa1879 : NodeDecl :=
  { rank := 2, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1879], params := [3, 1] }
@[reducible] private def p28_aa1880 : NodeDecl :=
  { rank := 3, op := "OpName.AllToAllPrim", ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1880], params := [3, 1] }
@[reducible] private def p28_mm1881 : NodeDecl :=
  { rank := 0, op := "OpName.FW_matmul", ins := [1873, 1877], outs := [1881] }
@[reducible] private def p28_mm1882 : NodeDecl :=
  { rank := 1, op := "OpName.FW_matmul", ins := [1874, 1878], outs := [1882] }
@[reducible] private def p28_mm1883 : NodeDecl :=
  { rank := 2, op := "OpName.FW_matmul", ins := [1875, 1879], outs := [1883] }
@[reducible] private def p28_mm1884 : NodeDecl :=
  { rank := 3, op := "OpName.FW_matmul", ins := [1876, 1880], outs := [1884] }

private theorem sm_eval_619 (initSM : Store) :
    denoteGraph sm initSM 619 = fw_matmul (denoteGraph sm initSM 613) (denoteGraph sm initSM 618) := by
  have hsub : (denoteGraph sm initSM) 619 =
      (denoteGraph { sm with nodes := sm.nodes.take 45 } initSM) 619 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 619
      (sm.nodes.take 45) (sm.nodes.drop 45)
      (List.take_append_drop 45 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 45 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 44 ++
        [{ rank := 0, op := "OpName.FW_matmul", ins := [613, 618], outs := [619] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm { rank := 0, op := "OpName.FW_matmul", ins := [613, 618], outs := [619] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 44 } initSM)
      { rank := 0, op := "OpName.FW_matmul", ins := [613, 618], outs := [619] }) 619 = _
  rw [applyNode_fw_matmul_out]
  have h613 : (denoteGraph { sm with nodes := sm.nodes.take 44 } initSM) 613 =
      denoteGraph sm initSM 613 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 613
      (sm.nodes.take 44) (sm.nodes.drop 44)
      (List.take_append_drop 44 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h618 : (denoteGraph { sm with nodes := sm.nodes.take 44 } initSM) 618 =
      denoteGraph sm initSM 618 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 618
      (sm.nodes.take 44) (sm.nodes.drop 44)
      (List.take_append_drop 44 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h613, h618]

/-! ## PM eval for the AllToAll nodes producing 1873..1876 (split dim 2, gather dim 1) -/

private theorem pm_eval_1873 (initPM : Store) :
    denoteGraph pm initPM 1873 = allToAllPrimWithDims 4 0
      [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
       denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  have hsub : (denoteGraph pm initPM) 1873 =
      (denoteGraph { pm with nodes := pm.nodes.take 269 } initPM) 1873 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1873
      (pm.nodes.take 269) (pm.nodes.drop 269)
      (List.take_append_drop 269 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 269 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 268 ++ [p28_aa1873] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1873] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1873 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1873 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 268 } initPM) p28_aa1873) 1873 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 0
      [denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1781,
       denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1782,
       denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1783,
       denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1784] 2 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1781 = denoteGraph pm initPM 1781 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1781 (pm.nodes.take 268) (pm.nodes.drop 268) (List.take_append_drop 268 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1782 = denoteGraph pm initPM 1782 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1782 (pm.nodes.take 268) (pm.nodes.drop 268) (List.take_append_drop 268 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1783 = denoteGraph pm initPM 1783 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1783 (pm.nodes.take 268) (pm.nodes.drop 268) (List.take_append_drop 268 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 268 } initPM 1784 = denoteGraph pm initPM 1784 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1784 (pm.nodes.take 268) (pm.nodes.drop 268) (List.take_append_drop 268 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

private theorem pm_eval_1874 (initPM : Store) :
    denoteGraph pm initPM 1874 = allToAllPrimWithDims 4 1
      [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
       denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  have hsub : (denoteGraph pm initPM) 1874 =
      (denoteGraph { pm with nodes := pm.nodes.take 270 } initPM) 1874 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1874
      (pm.nodes.take 270) (pm.nodes.drop 270)
      (List.take_append_drop 270 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 270 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 269 ++ [p28_aa1874] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1874] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1874 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1874 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 269 } initPM) p28_aa1874) 1874 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 1
      [denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1781,
       denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1782,
       denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1783,
       denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1784] 2 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1781 = denoteGraph pm initPM 1781 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1781 (pm.nodes.take 269) (pm.nodes.drop 269) (List.take_append_drop 269 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1782 = denoteGraph pm initPM 1782 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1782 (pm.nodes.take 269) (pm.nodes.drop 269) (List.take_append_drop 269 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1783 = denoteGraph pm initPM 1783 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1783 (pm.nodes.take 269) (pm.nodes.drop 269) (List.take_append_drop 269 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 269 } initPM 1784 = denoteGraph pm initPM 1784 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1784 (pm.nodes.take 269) (pm.nodes.drop 269) (List.take_append_drop 269 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

private theorem pm_eval_1875 (initPM : Store) :
    denoteGraph pm initPM 1875 = allToAllPrimWithDims 4 2
      [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
       denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  have hsub : (denoteGraph pm initPM) 1875 =
      (denoteGraph { pm with nodes := pm.nodes.take 271 } initPM) 1875 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1875
      (pm.nodes.take 271) (pm.nodes.drop 271)
      (List.take_append_drop 271 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 271 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 270 ++ [p28_aa1875] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1875] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1875 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1875 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 270 } initPM) p28_aa1875) 1875 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 2
      [denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1781,
       denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1782,
       denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1783,
       denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1784] 2 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1781 = denoteGraph pm initPM 1781 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1781 (pm.nodes.take 270) (pm.nodes.drop 270) (List.take_append_drop 270 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1782 = denoteGraph pm initPM 1782 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1782 (pm.nodes.take 270) (pm.nodes.drop 270) (List.take_append_drop 270 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1783 = denoteGraph pm initPM 1783 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1783 (pm.nodes.take 270) (pm.nodes.drop 270) (List.take_append_drop 270 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 270 } initPM 1784 = denoteGraph pm initPM 1784 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1784 (pm.nodes.take 270) (pm.nodes.drop 270) (List.take_append_drop 270 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

private theorem pm_eval_1876 (initPM : Store) :
    denoteGraph pm initPM 1876 = allToAllPrimWithDims 4 3
      [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
       denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  have hsub : (denoteGraph pm initPM) 1876 =
      (denoteGraph { pm with nodes := pm.nodes.take 272 } initPM) 1876 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1876
      (pm.nodes.take 272) (pm.nodes.drop 272)
      (List.take_append_drop 272 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 272 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 271 ++ [p28_aa1876] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1876] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1876 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1876 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 271 } initPM) p28_aa1876) 1876 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 3
      [denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1781,
       denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1782,
       denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1783,
       denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1784] 2 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1781 = denoteGraph pm initPM 1781 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1781 (pm.nodes.take 271) (pm.nodes.drop 271) (List.take_append_drop 271 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1782 = denoteGraph pm initPM 1782 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1782 (pm.nodes.take 271) (pm.nodes.drop 271) (List.take_append_drop 271 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1783 = denoteGraph pm initPM 1783 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1783 (pm.nodes.take 271) (pm.nodes.drop 271) (List.take_append_drop 271 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 271 } initPM 1784 = denoteGraph pm initPM 1784 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1784 (pm.nodes.take 271) (pm.nodes.drop 271) (List.take_append_drop 271 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

/-! ## PM eval for the AllToAll nodes producing 1877..1880 (split dim 3, gather dim 1) -/

private theorem pm_eval_1877 (initPM : Store) :
    denoteGraph pm initPM 1877 = allToAllPrimWithDims 4 0
      [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
       denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  have hsub : (denoteGraph pm initPM) 1877 =
      (denoteGraph { pm with nodes := pm.nodes.take 281 } initPM) 1877 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1877
      (pm.nodes.take 281) (pm.nodes.drop 281)
      (List.take_append_drop 281 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 281 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 280 ++ [p28_aa1877] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1877] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1877 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1877 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 280 } initPM) p28_aa1877) 1877 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 0
      [denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1853,
       denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1854,
       denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1855,
       denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1856] 3 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1853 = denoteGraph pm initPM 1853 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1853 (pm.nodes.take 280) (pm.nodes.drop 280) (List.take_append_drop 280 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1854 = denoteGraph pm initPM 1854 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1854 (pm.nodes.take 280) (pm.nodes.drop 280) (List.take_append_drop 280 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1855 = denoteGraph pm initPM 1855 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1855 (pm.nodes.take 280) (pm.nodes.drop 280) (List.take_append_drop 280 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 280 } initPM 1856 = denoteGraph pm initPM 1856 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1856 (pm.nodes.take 280) (pm.nodes.drop 280) (List.take_append_drop 280 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

private theorem pm_eval_1878 (initPM : Store) :
    denoteGraph pm initPM 1878 = allToAllPrimWithDims 4 1
      [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
       denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  have hsub : (denoteGraph pm initPM) 1878 =
      (denoteGraph { pm with nodes := pm.nodes.take 282 } initPM) 1878 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1878
      (pm.nodes.take 282) (pm.nodes.drop 282)
      (List.take_append_drop 282 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 282 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 281 ++ [p28_aa1878] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1878] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1878 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1878 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 281 } initPM) p28_aa1878) 1878 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 1
      [denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1853,
       denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1854,
       denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1855,
       denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1856] 3 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1853 = denoteGraph pm initPM 1853 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1853 (pm.nodes.take 281) (pm.nodes.drop 281) (List.take_append_drop 281 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1854 = denoteGraph pm initPM 1854 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1854 (pm.nodes.take 281) (pm.nodes.drop 281) (List.take_append_drop 281 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1855 = denoteGraph pm initPM 1855 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1855 (pm.nodes.take 281) (pm.nodes.drop 281) (List.take_append_drop 281 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 281 } initPM 1856 = denoteGraph pm initPM 1856 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1856 (pm.nodes.take 281) (pm.nodes.drop 281) (List.take_append_drop 281 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

private theorem pm_eval_1879 (initPM : Store) :
    denoteGraph pm initPM 1879 = allToAllPrimWithDims 4 2
      [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
       denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  have hsub : (denoteGraph pm initPM) 1879 =
      (denoteGraph { pm with nodes := pm.nodes.take 283 } initPM) 1879 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1879
      (pm.nodes.take 283) (pm.nodes.drop 283)
      (List.take_append_drop 283 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 283 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 282 ++ [p28_aa1879] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1879] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1879 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1879 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 282 } initPM) p28_aa1879) 1879 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 2
      [denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1853,
       denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1854,
       denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1855,
       denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1856] 3 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1853 = denoteGraph pm initPM 1853 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1853 (pm.nodes.take 282) (pm.nodes.drop 282) (List.take_append_drop 282 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1854 = denoteGraph pm initPM 1854 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1854 (pm.nodes.take 282) (pm.nodes.drop 282) (List.take_append_drop 282 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1855 = denoteGraph pm initPM 1855 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1855 (pm.nodes.take 282) (pm.nodes.drop 282) (List.take_append_drop 282 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 282 } initPM 1856 = denoteGraph pm initPM 1856 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1856 (pm.nodes.take 282) (pm.nodes.drop 282) (List.take_append_drop 282 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

private theorem pm_eval_1880 (initPM : Store) :
    denoteGraph pm initPM 1880 = allToAllPrimWithDims 4 3
      [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
       denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  have hsub : (denoteGraph pm initPM) 1880 =
      (denoteGraph { pm with nodes := pm.nodes.take 284 } initPM) 1880 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1880
      (pm.nodes.take 284) (pm.nodes.drop 284)
      (List.take_append_drop 284 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 284 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 283 ++ [p28_aa1880] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_aa1880] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_aa1880 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_aa1880 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 283 } initPM) p28_aa1880) 1880 = _
  rw [applyNode_allToAllPrimWithDims_out]
  change allToAllPrimWithDims 4 3
      [denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1853,
       denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1854,
       denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1855,
       denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1856] 3 1 = _
  have h1 : denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1853 = denoteGraph pm initPM 1853 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1853 (pm.nodes.take 283) (pm.nodes.drop 283) (List.take_append_drop 283 _).symm (by set_option maxRecDepth 20000 in decide)
  have h2 : denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1854 = denoteGraph pm initPM 1854 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1854 (pm.nodes.take 283) (pm.nodes.drop 283) (List.take_append_drop 283 _).symm (by set_option maxRecDepth 20000 in decide)
  have h3 : denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1855 = denoteGraph pm initPM 1855 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1855 (pm.nodes.take 283) (pm.nodes.drop 283) (List.take_append_drop 283 _).symm (by set_option maxRecDepth 20000 in decide)
  have h4 : denoteGraph { pm with nodes := pm.nodes.take 283 } initPM 1856 = denoteGraph pm initPM 1856 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1856 (pm.nodes.take 283) (pm.nodes.drop 283) (List.take_append_drop 283 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [h1, h2, h3, h4]

/-! ## PM eval for the FW_matmul nodes producing 1881..1884 -/

private theorem pm_eval_1881 (initPM : Store) :
    denoteGraph pm initPM 1881 = fw_matmul (denoteGraph pm initPM 1873) (denoteGraph pm initPM 1877) := by
  have hsub : (denoteGraph pm initPM) 1881 =
      (denoteGraph { pm with nodes := pm.nodes.take 285 } initPM) 1881 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1881
      (pm.nodes.take 285) (pm.nodes.drop 285)
      (List.take_append_drop 285 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 285 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 284 ++ [p28_mm1881] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_mm1881] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_mm1881 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_mm1881 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 284 } initPM) p28_mm1881) 1881 = _
  rw [applyNode_fw_matmul_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 284 } initPM 1873 = denoteGraph pm initPM 1873 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1873 (pm.nodes.take 284) (pm.nodes.drop 284) (List.take_append_drop 284 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 284 } initPM 1877 = denoteGraph pm initPM 1877 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1877 (pm.nodes.take 284) (pm.nodes.drop 284) (List.take_append_drop 284 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

private theorem pm_eval_1882 (initPM : Store) :
    denoteGraph pm initPM 1882 = fw_matmul (denoteGraph pm initPM 1874) (denoteGraph pm initPM 1878) := by
  have hsub : (denoteGraph pm initPM) 1882 =
      (denoteGraph { pm with nodes := pm.nodes.take 286 } initPM) 1882 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1882
      (pm.nodes.take 286) (pm.nodes.drop 286)
      (List.take_append_drop 286 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 286 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 285 ++ [p28_mm1882] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_mm1882] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_mm1882 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_mm1882 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 285 } initPM) p28_mm1882) 1882 = _
  rw [applyNode_fw_matmul_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 285 } initPM 1874 = denoteGraph pm initPM 1874 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1874 (pm.nodes.take 285) (pm.nodes.drop 285) (List.take_append_drop 285 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 285 } initPM 1878 = denoteGraph pm initPM 1878 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1878 (pm.nodes.take 285) (pm.nodes.drop 285) (List.take_append_drop 285 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

private theorem pm_eval_1883 (initPM : Store) :
    denoteGraph pm initPM 1883 = fw_matmul (denoteGraph pm initPM 1875) (denoteGraph pm initPM 1879) := by
  have hsub : (denoteGraph pm initPM) 1883 =
      (denoteGraph { pm with nodes := pm.nodes.take 287 } initPM) 1883 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1883
      (pm.nodes.take 287) (pm.nodes.drop 287)
      (List.take_append_drop 287 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 287 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 286 ++ [p28_mm1883] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_mm1883] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_mm1883 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_mm1883 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 286 } initPM) p28_mm1883) 1883 = _
  rw [applyNode_fw_matmul_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 286 } initPM 1875 = denoteGraph pm initPM 1875 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1875 (pm.nodes.take 286) (pm.nodes.drop 286) (List.take_append_drop 286 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 286 } initPM 1879 = denoteGraph pm initPM 1879 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1879 (pm.nodes.take 286) (pm.nodes.drop 286) (List.take_append_drop 286 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

private theorem pm_eval_1884 (initPM : Store) :
    denoteGraph pm initPM 1884 = fw_matmul (denoteGraph pm initPM 1876) (denoteGraph pm initPM 1880) := by
  have hsub : (denoteGraph pm initPM) 1884 =
      (denoteGraph { pm with nodes := pm.nodes.take 288 } initPM) 1884 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1884
      (pm.nodes.take 288) (pm.nodes.drop 288)
      (List.take_append_drop 288 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 288 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 287 ++ [p28_mm1884] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p28_mm1884] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p28_mm1884 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p28_mm1884 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 287 } initPM) p28_mm1884) 1884 = _
  rw [applyNode_fw_matmul_out]
  have hx : denoteGraph { pm with nodes := pm.nodes.take 287 } initPM 1876 = denoteGraph pm initPM 1876 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1876 (pm.nodes.take 287) (pm.nodes.drop 287) (List.take_append_drop 287 _).symm (by set_option maxRecDepth 20000 in decide)
  have hy : denoteGraph { pm with nodes := pm.nodes.take 287 } initPM 1880 = denoteGraph pm initPM 1880 := by
    symm; exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1880 (pm.nodes.take 287) (pm.nodes.drop 287) (List.take_append_drop 287 _).symm (by set_option maxRecDepth 20000 in decide)
  rw [hx, hy]

/-! ## Main theorem -/

theorem prove_pattern_28 : pattern_28_stmt := by
  intro target h
  cases h
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Use Pattern_26 to discharge goal_35 (SM.613 = allGather dim 2 of [PM.1781..1784])
  have hGoal35 : goal_35_stmt := prove_pattern_26 pattern_26_target.goal_35
  -- Use Pattern_27 to discharge goal_40 (SM.618 = allGather dim 3 of [PM.1853..1856])
  have hGoal40 : goal_40_stmt := prove_pattern_27 pattern_27_target.goal_40
  have h35 := hGoal35 initSM initPM hSmInit hPmInit hInitGoals
  have h40 := hGoal40 initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h613_sm_shape, h613_pm_shapes, h613_eq_rec⟩ := h35
  obtain ⟨h618_sm_shape, h618_pm_shapes, h618_eq_rec⟩ := h40
  -- Convert to value-level equalities using non-scalar reconstruction
  have h613_eq : denoteGraph sm initSM 613 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
       denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] := by
    have hh := h613_eq_rec
    change denoteGraph sm initSM 613 =
      reconstructWithDim 2 pm.numRanks 0
        ([({ rank := 0, tid := 1781 } : Piece), { rank := 1, tid := 1782 },
          { rank := 2, tid := 1783 }, { rank := 3, tid := 1784 }].map
          (fun p => denoteGraph pm initPM p.tid)) at hh
    simp only [List.map_cons, List.map_nil] at hh
    rw [hh]
    rw [show pm.numRanks = 4 from rfl]
    rw [reconstructWithDim_cons_cons_nonscalar]
    rw [show (denoteGraph pm initPM 1781).shape = [1, 4, 2, 8] by
      have hs := h613_pm_shapes
      change [(denoteGraph pm initPM 1781).shape, (denoteGraph pm initPM 1782).shape,
        (denoteGraph pm initPM 1783).shape, (denoteGraph pm initPM 1784).shape] =
        [[1, 4, 2, 8], [1, 4, 2, 8], [1, 4, 2, 8], [1, 4, 2, 8]] at hs
      have hs0 := congrArg List.head? hs
      simpa using hs0]
    intro hbad
    cases hbad
  have h618_eq : denoteGraph sm initSM 618 = allGatherPrimDimN 3 4 0
      [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
       denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] := by
    have hh := h618_eq_rec
    change denoteGraph sm initSM 618 =
      reconstructWithDim 3 pm.numRanks 0
        ([({ rank := 0, tid := 1853 } : Piece), { rank := 1, tid := 1854 },
          { rank := 2, tid := 1855 }, { rank := 3, tid := 1856 }].map
          (fun p => denoteGraph pm initPM p.tid)) at hh
    simp only [List.map_cons, List.map_nil] at hh
    rw [hh]
    rw [show pm.numRanks = 4 from rfl]
    rw [reconstructWithDim_cons_cons_nonscalar]
    rw [show (denoteGraph pm initPM 1853).shape = [1, 4, 8, 2] by
      have hs := h618_pm_shapes
      change [(denoteGraph pm initPM 1853).shape, (denoteGraph pm initPM 1854).shape,
        (denoteGraph pm initPM 1855).shape, (denoteGraph pm initPM 1856).shape] =
        [[1, 4, 8, 2], [1, 4, 8, 2], [1, 4, 8, 2], [1, 4, 8, 2]] at hs
      have hs0 := congrArg List.head? hs
      simpa using hs0]
    intro hbad
    cases hbad
  -- Now express PM AllToAll outputs in terms of SM tensors
  have h1873 : denoteGraph pm initPM 1873 = chunkPrimDimN 1 4 0 (denoteGraph sm initSM 613) := by
    rw [pm_eval_1873]
    unfold allToAllPrimWithDims
    rw [← h613_eq]
  have h1874 : denoteGraph pm initPM 1874 = chunkPrimDimN 1 4 1 (denoteGraph sm initSM 613) := by
    rw [pm_eval_1874]
    unfold allToAllPrimWithDims
    rw [← h613_eq]
  have h1875 : denoteGraph pm initPM 1875 = chunkPrimDimN 1 4 2 (denoteGraph sm initSM 613) := by
    rw [pm_eval_1875]
    unfold allToAllPrimWithDims
    rw [← h613_eq]
  have h1876 : denoteGraph pm initPM 1876 = chunkPrimDimN 1 4 3 (denoteGraph sm initSM 613) := by
    rw [pm_eval_1876]
    unfold allToAllPrimWithDims
    rw [← h613_eq]
  have h1877 : denoteGraph pm initPM 1877 = chunkPrimDimN 1 4 0 (denoteGraph sm initSM 618) := by
    rw [pm_eval_1877]
    unfold allToAllPrimWithDims
    rw [← h618_eq]
  have h1878 : denoteGraph pm initPM 1878 = chunkPrimDimN 1 4 1 (denoteGraph sm initSM 618) := by
    rw [pm_eval_1878]
    unfold allToAllPrimWithDims
    rw [← h618_eq]
  have h1879 : denoteGraph pm initPM 1879 = chunkPrimDimN 1 4 2 (denoteGraph sm initSM 618) := by
    rw [pm_eval_1879]
    unfold allToAllPrimWithDims
    rw [← h618_eq]
  have h1880 : denoteGraph pm initPM 1880 = chunkPrimDimN 1 4 3 (denoteGraph sm initSM 618) := by
    rw [pm_eval_1880]
    unfold allToAllPrimWithDims
    rw [← h618_eq]
  -- Shape facts on SM 613/618
  have h613_sm_shape' : (denoteGraph sm initSM 613).shape = [1, 4, 8, 8] := by
    simpa [goal_35] using h613_sm_shape
  have h618_sm_shape' : (denoteGraph sm initSM 618).shape = [1, 4, 8, 8] := by
    simpa [goal_40] using h618_sm_shape
  -- Now goal_41 final
  change (denoteGraph sm initSM 619).shape = [1, 4, 8, 8] ∧
    List.map (fun t => t.shape)
      ([({ rank := 0, tid := 1881 } : Piece), { rank := 1, tid := 1882 },
        { rank := 2, tid := 1883 }, { rank := 3, tid := 1884 }].map
        (fun p => denoteGraph pm initPM p.tid)) =
      [[1, 1, 8, 8], [1, 1, 8, 8], [1, 1, 8, 8], [1, 1, 8, 8]] ∧
    denoteGraph sm initSM 619 =
      reconstructWithDim 1 pm.numRanks 0
        ([({ rank := 0, tid := 1881 } : Piece), { rank := 1, tid := 1882 },
          { rank := 2, tid := 1883 }, { rank := 3, tid := 1884 }].map
          (fun p => denoteGraph pm initPM p.tid))
  refine ⟨?_, ?_, ?_⟩
  · -- shape of SM 619
    rw [sm_eval_619]
    exact fw_matmul_shape_1_4_8_8 _ _ h613_sm_shape' h618_sm_shape'
  · -- shapes of PM 1881..1884
    simp only [List.map_cons, List.map_nil]
    rw [pm_eval_1881, pm_eval_1882, pm_eval_1883, pm_eval_1884]
    rw [h1873, h1874, h1875, h1876, h1877, h1878, h1879, h1880]
    have hchunk613 : ∀ r, r < 4 → (chunkPrimDimN 1 4 r (denoteGraph sm initSM 613)).shape = [1, 1, 8, 8] := by
      intro r hr
      rw [chunkPrimDimN_shape 1 4 r _ _ h613_sm_shape' (by omega)]
      simp [List.set, List.getD]
    have hchunk618 : ∀ r, r < 4 → (chunkPrimDimN 1 4 r (denoteGraph sm initSM 618)).shape = [1, 1, 8, 8] := by
      intro r hr
      rw [chunkPrimDimN_shape 1 4 r _ _ h618_sm_shape' (by omega)]
      simp [List.set, List.getD]
    rw [show (fw_matmul (chunkPrimDimN 1 4 0 (denoteGraph sm initSM 613))
        (chunkPrimDimN 1 4 0 (denoteGraph sm initSM 618))).shape = [1, 1, 8, 8] from
      fw_matmul_shape_1_1_8_8 _ _ (hchunk613 0 (by decide)) (hchunk618 0 (by decide))]
    rw [show (fw_matmul (chunkPrimDimN 1 4 1 (denoteGraph sm initSM 613))
        (chunkPrimDimN 1 4 1 (denoteGraph sm initSM 618))).shape = [1, 1, 8, 8] from
      fw_matmul_shape_1_1_8_8 _ _ (hchunk613 1 (by decide)) (hchunk618 1 (by decide))]
    rw [show (fw_matmul (chunkPrimDimN 1 4 2 (denoteGraph sm initSM 613))
        (chunkPrimDimN 1 4 2 (denoteGraph sm initSM 618))).shape = [1, 1, 8, 8] from
      fw_matmul_shape_1_1_8_8 _ _ (hchunk613 2 (by decide)) (hchunk618 2 (by decide))]
    rw [show (fw_matmul (chunkPrimDimN 1 4 3 (denoteGraph sm initSM 613))
        (chunkPrimDimN 1 4 3 (denoteGraph sm initSM 618))).shape = [1, 1, 8, 8] from
      fw_matmul_shape_1_1_8_8 _ _ (hchunk613 3 (by decide)) (hchunk618 3 (by decide))]
  · -- value-level equality
    simp only [List.map_cons, List.map_nil]
    rw [sm_eval_619]
    rw [pm_eval_1881, pm_eval_1882, pm_eval_1883, pm_eval_1884]
    rw [h1873, h1874, h1875, h1876, h1877, h1878, h1879, h1880]
    rw [show pm.numRanks = 4 from rfl]
    rw [reconstructWithDim_cons_cons_nonscalar]
    · exact fw_matmul_split_dim1_4_1_4_8_8 (denoteGraph sm initSM 613) (denoteGraph sm initSM 618)
        h613_sm_shape' h618_sm_shape'
    · have hs : (fw_matmul (chunkPrimDimN 1 4 0 (denoteGraph sm initSM 613))
          (chunkPrimDimN 1 4 0 (denoteGraph sm initSM 618))).shape = [1, 1, 8, 8] := by
        have ha : (chunkPrimDimN 1 4 0 (denoteGraph sm initSM 613)).shape = [1, 1, 8, 8] := by
          rw [chunkPrimDimN_shape 1 4 0 _ _ h613_sm_shape' (by omega)]; simp [List.set, List.getD]
        have hb : (chunkPrimDimN 1 4 0 (denoteGraph sm initSM 618)).shape = [1, 1, 8, 8] := by
          rw [chunkPrimDimN_shape 1 4 0 _ _ h618_sm_shape' (by omega)]; simp [List.set, List.getD]
        exact fw_matmul_shape_1_1_8_8 _ _ ha hb
      rw [hs]
      intro hbad
      cases hbad

end TrainVerify.Denote.GeneratedPatterns
