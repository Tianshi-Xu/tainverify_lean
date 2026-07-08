import denote.yoco_goals.Pattern_3_faithful

open TrainVerify
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoalsFaithful

namespace TrainVerify.Denote.Pattern3Faithful

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4790_shallow (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4790 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3_faithful initSM 4757)
        (denoteGraph_ringAttn sm_goal_3_faithful initSM 4788) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4790 =
      ((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4790 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4790 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4790 80 (by decide) (by decide)
  rw [hEntry]
  have hval_4790 : ((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4790 = elemwiseAdd ((((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7460)) ((((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4789)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4790 79 80 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 79 = sm_goal_3_faithful.nodes.take 78 ++ [{ rank := 0, op := "OpName.FW_add", ins := [7460, 4789], outs := [4790] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_add", ins := [7460, 4789], outs := [4790] } (by decide) (by decide),
        applyNode_fw_add2_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7460 4789 4790,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7460 78 80 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4789 78 80 (by omega) (by decide) (by decide)]
  have hval_4789 : ((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4789 = (((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4788) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4789 78 80 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 78 = sm_goal_3_faithful.nodes.take 77 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4788], outs := [4789] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4788], outs := [4789] } (by decide) (by decide),
        applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4788 4789 [],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4788 77 80 (by omega) (by decide) (by decide)]
  have hval_7460 : ((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7460 = (((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4757) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7460 55 80 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 55 = sm_goal_3_faithful.nodes.take 54 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 54).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] } (by decide) (by decide),
        applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 54).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4757 7460 [7456, 7460] 2 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4757 54 80 (by omega) (by decide) (by decide)]
  have hval_4788 : ((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4788 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4788 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4788 80 (by decide) (by decide)).symm
  have hval_4757 : ((sm_goal_3_faithful.nodes.take 80).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4757 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4757 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4757 80 (by decide) (by decide)).symm
  rw [hval_4790, hval_4789, hval_7460, hval_4788, hval_4757]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4788_shallow (init : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful init 4788 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3_faithful init 4768)
        (denoteGraph_ringAttn sm_goal_3_faithful init 4787) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful init 4788 = (((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) init)) 4788 :=
    foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes init 4788 78 (by decide) (by decide)
  rw [hEntry]
  have hval_4788 : (((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) init)) 4788 = elemwiseAdd ((((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) init)) 4768) ((((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) init)) 4787) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes init 4788 77 78 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 77 = sm_goal_3_faithful.nodes.take 76 ++ [{ rank := 0, op := "OpName.FW_add", ins := [4768, 4787], outs := [4788] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful ((((sm_goal_3_faithful.nodes.take 76).foldl (applyNodeRingAttn sm_goal_3_faithful) init))) { rank := 0, op := "OpName.FW_add", ins := [4768, 4787], outs := [4788] } (by decide) (by decide),
        applyNode_fw_add2_out sm_goal_3_faithful ((((sm_goal_3_faithful.nodes.take 76).foldl (applyNodeRingAttn sm_goal_3_faithful) init))) 0 4768 4787 4788,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes init 4768 76 78 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes init 4787 76 78 (by omega) (by decide) (by decide)]
  have hval_4768_dg : (((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) init)) 4768 = denoteGraph_ringAttn sm_goal_3_faithful init 4768 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes init 4768 78 (by decide) (by decide)).symm
  have hval_4787_dg : (((sm_goal_3_faithful.nodes.take 78).foldl (applyNodeRingAttn sm_goal_3_faithful) init)) 4787 = denoteGraph_ringAttn sm_goal_3_faithful init 4787 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes init 4787 78 (by decide) (by decide)).symm
  rw [hval_4788, hval_4768_dg, hval_4787_dg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7755_shallow (init : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful init 7755 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3_faithful init 7677)
        (denoteGraph_ringAttn pm_goal_3_faithful init 7751) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful init 7755 = (((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7755 :=
    foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7755 212 (by decide) (by decide)
  rw [hEntry]
  have hval_7755 : (((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7755 = elemwiseAdd ((((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7677) ((((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7751) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7755 211 212 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 211 = pm_goal_3_faithful.nodes.take 210 ++ [{ rank := 0, op := "OpName.FW_add", ins := [7677, 7751], outs := [7755] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 0, op := "OpName.FW_add", ins := [7677, 7751], outs := [7755] } (by decide) (by decide),
        applyNode_fw_add2_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 0 7677 7751 7755,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7677 210 212 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7751 210 212 (by omega) (by decide) (by decide)]
  have hval_7677_dg : (((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7677 = denoteGraph_ringAttn pm_goal_3_faithful init 7677 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7677 212 (by decide) (by decide)).symm
  have hval_7751_dg : (((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7751 = denoteGraph_ringAttn pm_goal_3_faithful init 7751 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7751 212 (by decide) (by decide)).symm
  rw [hval_7755, hval_7677_dg, hval_7751_dg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7756_shallow (init : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful init 7756 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3_faithful init 7678)
        (denoteGraph_ringAttn pm_goal_3_faithful init 7752) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful init 7756 = (((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7756 :=
    foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7756 213 (by decide) (by decide)
  rw [hEntry]
  have hval_7756 : (((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7756 = elemwiseAdd ((((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7678) ((((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7752) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7756 212 213 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 212 = pm_goal_3_faithful.nodes.take 211 ++ [{ rank := 1, op := "OpName.FW_add", ins := [7678, 7752], outs := [7756] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 1, op := "OpName.FW_add", ins := [7678, 7752], outs := [7756] } (by decide) (by decide),
        applyNode_fw_add2_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 1 7678 7752 7756,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7678 211 213 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7752 211 213 (by omega) (by decide) (by decide)]
  have hval_7678_dg : (((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7678 = denoteGraph_ringAttn pm_goal_3_faithful init 7678 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7678 213 (by decide) (by decide)).symm
  have hval_7752_dg : (((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7752 = denoteGraph_ringAttn pm_goal_3_faithful init 7752 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7752 213 (by decide) (by decide)).symm
  rw [hval_7756, hval_7678_dg, hval_7752_dg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7765_shallow (init : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful init 7765 =
      elemwiseAdd (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 (denoteGraph_ringAttn pm_goal_3_faithful init 4757))
        (denoteGraph_ringAttn pm_goal_3_faithful init 7755) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful init 7765 = (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7765 :=
    foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7765 216 (by decide) (by decide)
  rw [hEntry]
  have hval_7765 : (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7765 = elemwiseAdd ((((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 12011) ((((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7761) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7765 215 216 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 215 = pm_goal_3_faithful.nodes.take 214 ++ [{ rank := 0, op := "OpName.FW_add", ins := [12011, 7761], outs := [7765] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 214).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 0, op := "OpName.FW_add", ins := [12011, 7761], outs := [7765] } (by decide) (by decide),
        applyNode_fw_add2_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 214).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 0 12011 7761 7765,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 12011 214 216 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7761 214 216 (by omega) (by decide) (by decide)]
  have hval_7761 : (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7761 = (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7755 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7761 213 216 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 213 = pm_goal_3_faithful.nodes.take 212 ++ [{ rank := 0, op := "OpName.FW_float", ins := [7755], outs := [7761] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 0, op := "OpName.FW_float", ins := [7755], outs := [7761] } (by decide) (by decide),
        applyNode_fw_float_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 212).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 0 7755 7761 [],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7755 212 216 (by omega) (by decide) (by decide)]
  have hval_12011 : (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 12011 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 11890) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 12011 158 216 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 158 = pm_goal_3_faithful.nodes.take 157 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [11890], outs := [12011], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 157).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 0, op := "OpName.ChunkPrim", ins := [11890], outs := [12011], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 157).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 0 11890 12011 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 11890 157 216 (by omega) (by decide) (by decide)]
  have hval_11890 : (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 11890 = (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 11890 156 216 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 156 = pm_goal_3_faithful.nodes.take 155 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } (by decide) (by decide),
        RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 1 4757 11889 11890 (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 4757 155 216 (by omega) (by decide) (by decide)]
  have hval_4757_dg : (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 4757 = denoteGraph_ringAttn pm_goal_3_faithful init 4757 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 4757 216 (by decide) (by decide)).symm
  have hval_7755_dg : (((pm_goal_3_faithful.nodes.take 216).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7755 = denoteGraph_ringAttn pm_goal_3_faithful init 7755 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7755 216 (by decide) (by decide)).symm
  rw [hval_7765, hval_7761, hval_12011, hval_11890, hval_4757_dg, hval_7755_dg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7766_shallow (init : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful init 7766 =
      elemwiseAdd (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 (denoteGraph_ringAttn pm_goal_3_faithful init 4757))
        (denoteGraph_ringAttn pm_goal_3_faithful init 7756) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful init 7766 = (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7766 :=
    foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7766 217 (by decide) (by decide)
  rw [hEntry]
  have hval_7766 : (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7766 = elemwiseAdd ((((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 12012) ((((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7762) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7766 216 217 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 216 = pm_goal_3_faithful.nodes.take 215 ++ [{ rank := 1, op := "OpName.FW_add", ins := [12012, 7762], outs := [7766] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 215).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 1, op := "OpName.FW_add", ins := [12012, 7762], outs := [7766] } (by decide) (by decide),
        applyNode_fw_add2_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 215).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 1 12012 7762 7766,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 12012 215 217 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7762 215 217 (by omega) (by decide) (by decide)]
  have hval_7762 : (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7762 = (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7756 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7762 214 217 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 214 = pm_goal_3_faithful.nodes.take 213 ++ [{ rank := 1, op := "OpName.FW_float", ins := [7756], outs := [7762] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 1, op := "OpName.FW_float", ins := [7756], outs := [7762] } (by decide) (by decide),
        applyNode_fw_float_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 213).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 1 7756 7762 [],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7756 213 217 (by omega) (by decide) (by decide)]
  have hval_12012 : (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 12012 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 11890) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 12012 160 217 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 160 = pm_goal_3_faithful.nodes.take 159 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [11890], outs := [12012], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 159).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 1, op := "OpName.ChunkPrim", ins := [11890], outs := [12012], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 159).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 1 11890 12012 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 11890 159 217 (by omega) (by decide) (by decide)]
  have hval_11890 : (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 11890 = (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 11890 156 217 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 156 = pm_goal_3_faithful.nodes.take 155 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } (by decide) (by decide),
        RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3_faithful ((((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) init))) 1 4757 11889 11890 (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 4757 155 217 (by omega) (by decide) (by decide)]
  have hval_4757_dg : (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 4757 = denoteGraph_ringAttn pm_goal_3_faithful init 4757 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 4757 217 (by decide) (by decide)).symm
  have hval_7756_dg : (((pm_goal_3_faithful.nodes.take 217).foldl (applyNodeRingAttn pm_goal_3_faithful) init)) 7756 = denoteGraph_ringAttn pm_goal_3_faithful init 7756 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes init 7756 217 (by decide) (by decide)).symm
  rw [hval_7766, hval_7762, hval_12012, hval_11890, hval_4757_dg, hval_7756_dg]

#print axioms denote_sm_goal_3_faithful_4788_shallow
#print axioms denote_pm_goal_3_faithful_7755_shallow
#print axioms denote_pm_goal_3_faithful_7756_shallow
#print axioms denote_pm_goal_3_faithful_7765_shallow
#print axioms denote_pm_goal_3_faithful_7766_shallow

-- =============================================================================
-- L2 sub-commutes: SM 4768 (MoE) and SM 4787 (gate·mul) shard equalities
-- =============================================================================

-- First: SM 4768 deep unfold to fw_all2all_moe_gmm on gathered weights
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_faithful_4768 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4768 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3_faithful initSM 7471)
        (denoteGraph_ringAttn sm_goal_3_faithful initSM 4763)
        (denoteGraph_ringAttn sm_goal_3_faithful initSM 4764)
        (initSM 4766) (initSM 4767) 64 0 64 8 ((((10 : Nat) : Scalar))) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4768 =
      ((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4768 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4768 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4768 71 (by decide) (by decide)
  rw [hEntry]
  have hval_4768 : ((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4768 =
      fw_all2all_moe_gmm
        ((((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7471))
        ((((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4763))
        ((((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4764))
        (initSM 4766) (initSM 4767) 64 0 64 8 ((((10 : Nat) : Scalar))) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4768 70 71 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 70 = sm_goal_3_faithful.nodes.take 69 ++ [{ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7471, 4763, 4764, 4766, 4767], outs := [4768], params := [64, 0, 64, 8] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 69).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7471, 4763, 4764, 4766, 4767], outs := [4768], params := [64, 0, 64, 8] } (by decide) (by decide),
        applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 69).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7471 4763 4764 4766 4767 4768 [64, 0, 64, 8],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7471 69 71 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4763 69 71 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4764 69 71 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 69) initSM 4766 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 69) initSM 4767 (by decide) (by decide)]
    rfl
  have hval_7471 : ((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7471 = denoteGraph_ringAttn sm_goal_3_faithful initSM 7471 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7471 71 (by decide) (by decide)).symm
  have hval_4763 : ((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4763 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4763 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4763 71 (by decide) (by decide)).symm
  have hval_4764 : ((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4764 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4764 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4764 71 (by decide) (by decide)).symm
  rw [hval_4768, hval_7471, hval_4763, hval_4764]

#print axioms denote_sm_goal_3_faithful_4768

-- SM 4763 = fst of topk_routing (parallel to 4764)
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_faithful_4763 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4763 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3_faithful initSM 4762) 8
        (((denoteGraph_ringAttn sm_goal_3_faithful initSM 4762).shape.reverse.head?).getD 1)).fst := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4763 =
      ((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4763 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4763 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4763 67 (by decide) (by decide)
  rw [hEntry]
  have hval_4763 : ((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4763 = (fw_topk_routing ((((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4762)) 8 ((((((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4762)).shape.reverse.head?).getD 1)).fst := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4763 66 67 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 66 = sm_goal_3_faithful.nodes.take 65 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 65).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8] } (by decide) (by decide),
        applyNode_fw_topk_routing_probs_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 65).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4762 4763 4764 4765 [8],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4762 65 67 (by omega) (by decide) (by decide)]
    rfl
  have hval_4762 : ((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4762 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4762 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4762 67 (by decide) (by decide)).symm
  rw [hval_4763, hval_4762]

#print axioms denote_sm_goal_3_faithful_4763

-- SM 7471 = SM 4759 (multiref pos 1). SM 4759 = fw_rms_norm(SM 7456, initSM 4758)
-- and SM 7456 = SM 4757 (via multiref). We prove SM 7471 = fw_rms_norm(SM 4757, initSM 4758).
-- Indices: multiref 4757→[7456,7460] at 0-idx 54,
--          rms_norm 7456→4759 at 0-idx 55,
--          multiref 4759→[7467,7471,...] at 0-idx 56
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_faithful_7471 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 7471 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3_faithful initSM 4757) (initSM 4758) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 7471 =
      ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7471 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 7471 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7471 58 (by decide) (by decide)
  rw [hEntry]
  have hval_7471 : ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7471 = ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4759 := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7471 57 58 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 57 = sm_goal_3_faithful.nodes.take 56 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 56).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] } (by decide) (by decide),
        applyNode_fw_multiref5_at_pos1_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 56).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4759 7467 7471 7475 7479 7483 (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4759 56 58 (by omega) (by decide) (by decide)]
  have hval_4759 : ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4759 = fw_rms_norm ((((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7456)) (initSM 4758) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4759 56 58 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 56 = sm_goal_3_faithful.nodes.take 55 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7456, 4758], outs := [4759] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 55).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rms_norm", ins := [7456, 4758], outs := [4759] } (by decide) (by decide),
        applyNode_fw_rms_norm_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 55).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7456 4758 4759,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7456 55 58 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 55) initSM 4758 (by decide) (by decide)]
  have hval_7456 : ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7456 = ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7456 55 58 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 55 = sm_goal_3_faithful.nodes.take 54 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 54).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] } (by decide) (by decide),
        applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 54).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4757 7456 [7456, 7460] 2 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4757 54 58 (by omega) (by decide) (by decide)]
  have hval_4757_dg : ((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4757 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4757 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4757 58 (by decide) (by decide)).symm
  rw [hval_7471, hval_4759, hval_7456, hval_4757_dg]

#print axioms denote_sm_goal_3_faithful_7471

-- PM 7677 (rank 0 shard MoE) deep unfold to fw_all2all_moe_gmm_full
-- PM MoE_full node at 0-idx 196; take 198 (2 past write) allows split to peel node@196
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_7677 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7677 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 11977)
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 7667)
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 7669)
        [initPM 7673, initPM 7674] [initPM 7675, initPM 7676]
        64 8 ((((10 : Nat) : Scalar))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7677 =
      ((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7677 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7677 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7677 198 (by decide) (by decide)
  rw [hEntry]
  have hval_7677 : ((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7677 =
      fw_all2all_moe_gmm_full
        ((((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11977))
        ((((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7667))
        ((((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7669))
        [initPM 7673, initPM 7674] [initPM 7675, initPM 7676]
        64 8 ((((10 : Nat) : Scalar))) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7677 197 198 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 197 = pm_goal_3_faithful.nodes.take 196 ++ [{ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [11977, 7667, 7669, 7673, 7674, 7675, 7676], outs := [7677], params := [64, 8, 10] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 196).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [11977, 7667, 7669, 7673, 7674, 7675, 7676], outs := [7677], params := [64, 8, 10] } (by decide) (by decide),
        applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 196).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 11977 7667 7669 7673 7674 7675 7676 7677 [64, 8, 10],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11977 196 198 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7667 196 198 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7669 196 198 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 196) initPM 7673 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 196) initPM 7674 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 196) initPM 7675 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 196) initPM 7676 (by decide) (by decide)]
    rfl
  have hval_11977_dg : ((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11977 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11977 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11977 198 (by decide) (by decide)).symm
  have hval_7667_dg : ((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7667 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7667 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7667 198 (by decide) (by decide)).symm
  have hval_7669_dg : ((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7669 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7669 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7669 198 (by decide) (by decide)).symm
  rw [hval_7677, hval_11977_dg, hval_7667_dg, hval_7669_dg]

#print axioms denote_pm_goal_3_faithful_7677

-- PM 7678 (rank 1 shard MoE) — mirror of 7677 with rank-1 tids
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_7678 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7678 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 11978)
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 7668)
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 7670)
        [initPM 7673, initPM 7674] [initPM 7675, initPM 7676]
        64 8 ((((10 : Nat) : Scalar))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7678 =
      ((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7678 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7678 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7678 199 (by decide) (by decide)
  rw [hEntry]
  have hval_7678 : ((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7678 =
      fw_all2all_moe_gmm_full
        ((((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11978))
        ((((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7668))
        ((((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7670))
        [initPM 7673, initPM 7674] [initPM 7675, initPM 7676]
        64 8 ((((10 : Nat) : Scalar))) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7678 198 199 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 198 = pm_goal_3_faithful.nodes.take 197 ++ [{ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [11978, 7668, 7670, 7673, 7674, 7675, 7676], outs := [7678], params := [64, 8, 10] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 197).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [11978, 7668, 7670, 7673, 7674, 7675, 7676], outs := [7678], params := [64, 8, 10] } (by decide) (by decide),
        applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 197).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11978 7668 7670 7673 7674 7675 7676 7678 [64, 8, 10],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11978 197 199 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7668 197 199 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7670 197 199 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 197) initPM 7673 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 197) initPM 7674 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 197) initPM 7675 (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 197) initPM 7676 (by decide) (by decide)]
    rfl
  have hval_11978_dg : ((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11978 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11978 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11978 199 (by decide) (by decide)).symm
  have hval_7668_dg : ((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7668 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7668 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7668 199 (by decide) (by decide)).symm
  have hval_7670_dg : ((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7670 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7670 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7670 199 (by decide) (by decide)).symm
  rw [hval_7678, hval_11978_dg, hval_7668_dg, hval_7670_dg]

#print axioms denote_pm_goal_3_faithful_7678

-- Intermediate PM unfolds (needed for sub-commute A assembly):
-- PM 11977 = chunk 0 of PM 11904 (rank-0 ChunkPrim node at 0-idx 163)
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_11977 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11977 =
      chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 11904) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11977 =
      ((pm_goal_3_faithful.nodes.take 165).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11977 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11977 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11977 165 (by decide) (by decide)
  rw [hEntry]
  have hval_11977 : ((pm_goal_3_faithful.nodes.take 165).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11977 =
      chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((((pm_goal_3_faithful.nodes.take 165).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11904)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11977 164 165 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 164 = pm_goal_3_faithful.nodes.take 163 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [11904], outs := [11977], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [11904], outs := [11977], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 11904 11977 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11904 163 165 (by omega) (by decide) (by decide)]
  have hval_11904_dg : ((pm_goal_3_faithful.nodes.take 165).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11904 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11904 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11904 165 (by decide) (by decide)).symm
  rw [hval_11977, hval_11904_dg]

#print axioms denote_pm_goal_3_faithful_11977

-- PM 11978 = chunk 1 of PM 11904 (rank-1 ChunkPrim node at 0-idx 168)
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_11978 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11978 =
      chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 11904) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11978 =
      ((pm_goal_3_faithful.nodes.take 170).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11978 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11978 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11978 170 (by decide) (by decide)
  rw [hEntry]
  have hval_11978 : ((pm_goal_3_faithful.nodes.take 170).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11978 =
      chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((((pm_goal_3_faithful.nodes.take 170).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11904)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11978 169 170 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 169 = pm_goal_3_faithful.nodes.take 168 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [11904], outs := [11978], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 168).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [11904], outs := [11978], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 168).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11904 11978 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11904 168 170 (by omega) (by decide) (by decide)]
  have hval_11904_dg : ((pm_goal_3_faithful.nodes.take 170).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11904 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11904 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11904 170 (by decide) (by decide)).symm
  rw [hval_11978, hval_11904_dg]

#print axioms denote_pm_goal_3_faithful_11978

-- PM 4762 = fw_norm_linear (chain from PM 4757) — parallel to SM 4762
-- multiref 4757→[11889,11890] at 0-idx 154 (rank 0), rms_norm 11889→4759 at 155,
-- multiref 4759→[11903..11907] at 160 (rank 0), FW_float 11903→4760 at 165,
-- norm_linear 4760→4762 at 172 (rank 0)
-- Wait — this depends on the chain and rank 1 also writes 4759 at 158... let me look at PM 4762 more carefully.
-- Actually PM has denote_pm_goal_3_faithful_4762 already (line 25179). Let me use existing.

-- PM 7667 = topk_fst(PM 7665) — parallel to PM 7669 (existing at line 25264)
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_7667 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7667 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3_faithful initPM 7665) 8
        (((denoteGraph_ringAttn pm_goal_3_faithful initPM 7665).shape.reverse.head?).getD 1)).fst := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7667 =
      ((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7667 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7667 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7667 190 (by decide) (by decide)
  rw [hEntry]
  have hval_7667 : ((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7667 = (fw_topk_routing ((((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7665)) 8 ((((((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7665)).shape.reverse.head?).getD 1)).fst := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7667 189 190 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 189 = pm_goal_3_faithful.nodes.take 188 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 188).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8] } (by decide) (by decide),
        applyNode_fw_topk_routing_probs_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 188).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7665 7667 7669 7671 [8],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7665 188 190 (by omega) (by decide) (by decide)]
    rfl
  have hval_7665_dg : ((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7665 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7665 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7665 190 (by decide) (by decide)).symm
  rw [hval_7667, hval_7665_dg]

#print axioms denote_pm_goal_3_faithful_7667

-- PM 7668 = topk_fst(PM 7666) — rank 1 mirror
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_7668 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7668 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3_faithful initPM 7666) 8
        (((denoteGraph_ringAttn pm_goal_3_faithful initPM 7666).shape.reverse.head?).getD 1)).fst := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7668 =
      ((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7668 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7668 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7668 191 (by decide) (by decide)
  rw [hEntry]
  have hval_7668 : ((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7668 = (fw_topk_routing ((((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7666)) 8 ((((((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7666)).shape.reverse.head?).getD 1)).fst := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7668 190 191 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 190 = pm_goal_3_faithful.nodes.take 189 ++ [{ rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8] } (by decide) (by decide),
        applyNode_fw_topk_routing_probs_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7666 7668 7670 7672 [8],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7666 189 191 (by omega) (by decide) (by decide)]
    rfl
  have hval_7666_dg : ((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7666 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7666 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7666 191 (by decide) (by decide)).symm
  rw [hval_7668, hval_7666_dg]

#print axioms denote_pm_goal_3_faithful_7668

-- PM 11904 = multiref pos 1 of PM 4759 (rank 1 idx 161)
-- PM 4759 rank 1 rms_norm(11889, 4758) at idx 158
-- PM 11889 = multiref pos 0 of PM 4757 (rank 1 idx 155)
-- PM 11904 = fw_rms_norm (PM 4757, initPM 4758)
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_11904 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11904 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3_faithful initPM 4757) (initPM 4758) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11904 =
      ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11904 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11904 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11904 163 (by decide) (by decide)
  rw [hEntry]
  have hval_11904 : ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11904 = ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11904 162 163 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 162 = pm_goal_3_faithful.nodes.take 161 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] } (by decide) (by decide),
        applyNode_fw_multiref5_at_pos1_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4759 11903 11904 11905 11906 11907 (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 161 163 (by omega) (by decide) (by decide)]
  have hval_4759 : ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 = fw_rms_norm ((((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889)) (initPM 4758) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 159 163 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 159 = pm_goal_3_faithful.nodes.take 158 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] } (by decide) (by decide),
        applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11889 4758 4759,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 158 163 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 158) initPM 4758 (by decide) (by decide)]
  have hval_11889 : ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889 = ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 156 163 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 156 = pm_goal_3_faithful.nodes.take 155 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } (by decide) (by decide),
        applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4757 11889 [11889, 11890] 2 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 155 163 (by omega) (by decide) (by decide)]
  have hval_4757_dg : ((pm_goal_3_faithful.nodes.take 163).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4757 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 163 (by decide) (by decide)).symm
  rw [hval_11904, hval_4759, hval_11889, hval_4757_dg]

#print axioms denote_pm_goal_3_faithful_11904

-- Sub-commute A: SM 4768 (MoE) = allGather [PM 7677, PM 7678]
-- This is the E1 crux. Reduces via:
--   1. Unfold both sides via my deep unfolds
--   2. Bridge SM 7471/4763/4764 to their gathered-chunk PM analogues
--   3. Apply fw_all2all_moe_gmm_full_split_commute_2
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
theorem sm_pm_moe_gmm_L1_commute
    (initSM initPM : Store)
    (h_ss_sm : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4768
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3_faithful initPM 7677,
           denoteGraph_ringAttn pm_goal_3_faithful initPM 7678] := by
  -- unfold both sides
  rw [denote_sm_goal_3_faithful_4768, denote_pm_goal_3_faithful_7677, denote_pm_goal_3_faithful_7678]
  -- Bridge SM sub-terms to their PM/shard counterparts
  rw [denote_sm_goal_3_faithful_7471, denote_sm_goal_3_faithful_4763, denote_sm_goal_3_faithful_4764]
  rw [denote_pm_goal_3_faithful_11977, denote_pm_goal_3_faithful_11978,
      denote_pm_goal_3_faithful_11904,
      denote_pm_goal_3_faithful_7667, denote_pm_goal_3_faithful_7669,
      denote_pm_goal_3_faithful_7668, denote_pm_goal_3_faithful_7670,
      denote_pm_goal_3_faithful_7665, denote_pm_goal_3_faithful_7666,
      denote_sm_goal_3_faithful_4762, denote_pm_goal_3_faithful_4762]
  -- SM 4757 = PM 4757 via carry
  rw [sm_pm_carry_4757_commute initSM initPM h_ss_sm h_ss_pm hInit]
  -- initSM 4758 = initPM 4758, initSM 4761 = initPM 4761
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4758 : initSM 4758 = initPM 4758 := hb initGoal_4758 (by decide) rfl
  have h4761 : initSM 4761 = initPM 4761 := hb initGoal_4761 (by decide) rfl
  rw [h4758, h4761]
  -- Weight reconstructions (2-shard MoE weights)
  have h4766 : initSM 4766 = allGatherPrimDimN 0 2 0 [initPM 7673, initPM 7674] := by
    have hg := hII initGoal_4766 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_4766, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3_faithful.numRanks 0 (initPM 7673) (initPM 7674) []
        (by rw [h_ss_pm 7673 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3_faithful.numRanks = 2 from rfl] at hval
    exact hval
  have h4767 : initSM 4767 = allGatherPrimDimN 0 2 0 [initPM 7675, initPM 7676] := by
    have hg := hII initGoal_4767 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_4767, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3_faithful.numRanks 0 (initPM 7675) (initPM 7676) []
        (by rw [h_ss_pm 7675 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3_faithful.numRanks = 2 from rfl] at hval
    exact hval
  rw [h4766, h4767]
  rw [show pm_goal_3_faithful.numRanks = 2 from rfl]
  -- Now goal is fw_all2all_moe_gmm on gathered = allGather of fw_all2all_moe_gmm_full per-shard
  -- This matches fw_all2all_moe_gmm_full_split_commute_2 (with reconstruction from chunks)
  set RMS_PM := fw_rms_norm (denoteGraph_ringAttn pm_goal_3_faithful initPM 4757) (initPM 4758) with hRMSpm
  set NL_PM := fw_norm_linear RMS_PM (initPM 4761) with hNLpm
  have hRMSpm_sh : RMS_PM.shape = [4096, 1024] := by
    rw [hRMSpm, rms_sh]
    exact RouterShapesHelpers.hs_4757 initPM h_ss_pm
  have hNLpm_sh : NL_PM.shape = [4096, 64] := by
    rw [hNLpm]
    exact nl_sh 4096 1024 64 _ _ hRMSpm_sh (h_ss_pm 4761 [64,1024] (by decide))
  -- chunk shapes
  have hc0_RMS : (chunkPrimDimN 0 2 0 RMS_PM).shape = [2048, 1024] :=
    chunk0_2 0 _ 4096 1024 hRMSpm_sh
  have hc1_RMS : (chunkPrimDimN 0 2 1 RMS_PM).shape = [2048, 1024] :=
    chunk0_2 1 _ 4096 1024 hRMSpm_sh
  have hc0_NL : (chunkPrimDimN 0 2 0 NL_PM).shape = [2048, 64] :=
    chunk0_2 0 _ 4096 64 hNLpm_sh
  have hc1_NL : (chunkPrimDimN 0 2 1 NL_PM).shape = [2048, 64] :=
    chunk0_2 1 _ 4096 64 hNLpm_sh
  -- routing shapes
  have hrp0 : (fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).fst.shape = [2048, 64] :=
    fw_topk_routing_fst_shape (chunkPrimDimN 0 2 0 NL_PM) 8 64 2048 (by rw [hc0_NL]; rfl)
  have hrp1 : (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).fst.shape = [2048, 64] :=
    fw_topk_routing_fst_shape (chunkPrimDimN 0 2 1 NL_PM) 8 64 2048 (by rw [hc1_NL]; rfl)
  have hrm0 : (fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).snd.fst.shape = [2048, 64] :=
    topk_sf_sh (chunkPrimDimN 0 2 0 NL_PM) 2048 8 64 hc0_NL
  have hrm1 : (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).snd.fst.shape = [2048, 64] :=
    topk_sf_sh (chunkPrimDimN 0 2 1 NL_PM) 2048 8 64 hc1_NL
  -- weight shapes
  have hw73 : (initPM 7673).shape = [32,1024,1024] := h_ss_pm 7673 [32,1024,1024] (by decide)
  have hw74 : (initPM 7674).shape = [32,1024,1024] := h_ss_pm 7674 [32,1024,1024] (by decide)
  have hw75 : (initPM 7675).shape = [32,1024,512] := h_ss_pm 7675 [32,1024,512] (by decide)
  have hw76 : (initPM 7676).shape = [32,1024,512] := h_ss_pm 7676 [32,1024,512] (by decide)
  -- normalize k dim of NL
  have hk_full : (NL_PM.shape.reverse.head?).getD 1 = 64 := by rw [hNLpm_sh]; rfl
  have hk_c0 : ((chunkPrimDimN 0 2 0 NL_PM).shape.reverse.head?).getD 1 = 64 := by rw [hc0_NL]; rfl
  have hk_c1 : ((chunkPrimDimN 0 2 1 NL_PM).shape.reverse.head?).getD 1 = 64 := by rw [hc1_NL]; rfl
  rw [hk_full, hk_c0, hk_c1]
  -- topk_fst / topk_snd_fst chunk commutes: fw_topk_routing NL fst = allGather [chunk fsts]
  have hfstchunk : (fw_topk_routing NL_PM 8 64).fst =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).fst,
         (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).fst] := by
    have hchunk := allGather0_reconstruct_chunks_2d 2048 64 (by omega) (by omega) NL_PM hNLpm_sh
    conv_lhs => rw [← hchunk]
    rw [GeneratedPatterns.fw_topk_routing_fst_allGather0_commute_2_of
          (chunkPrimDimN 0 2 0 NL_PM) (chunkPrimDimN 0 2 1 NL_PM)
          2048 8 64 (by omega) (by omega) hc0_NL hc1_NL]
  have hsndchunk : (fw_topk_routing NL_PM 8 64).snd.fst =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).snd.fst,
         (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).snd.fst] :=
    topk_snd_fst_chunk_commute NL_PM 2048 8 64 (by omega) (by omega) hNLpm_sh
  -- Apply the split_commute lemma
  have key := GeneratedPatterns.fw_all2all_moe_gmm_full_split_commute_2
    (chunkPrimDimN 0 2 0 RMS_PM) (chunkPrimDimN 0 2 1 RMS_PM)
    (fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).fst (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).fst
    (fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).snd.fst (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).snd.fst
    (initPM 7673) (initPM 7674) (initPM 7675) (initPM 7676)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hc0_RMS hc1_RMS hrp0 hrp1 hrm0 hrm1 hw73 hw74 hw75 hw76
  rw [allGather0_reconstruct_chunks_2d 2048 1024 (by omega) (by omega) RMS_PM hRMSpm_sh,
      ← hfstchunk, ← hsndchunk] at key
  exact key

#print axioms sm_pm_moe_gmm_L1_commute

-- =============================================================================
-- Sub-commute B (SM 4787 = allGather [PM 7751, PM 7752]) — gate·mul path
-- =============================================================================

-- SM 4787 deep unfold to raw fw_mul(fw_sigmoid(fw_view(fw_linear(fw_view(RMS)))))
-- (fw_view(fw_linear(fw_view(fw_swiglu(fw_view(fw_linear(fw_view(RMS))), fw_view(fw_linear(fw_view(RMS))))))))
-- All at rank 0. Chain from idx 58-75 (15 nodes).
-- Also: 7475/7479/7483 = SM 4759 via multiref pos 2/3/4 (idx 56)
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_faithful_4787 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4787 =
      elemwiseMul
        (fw_sigmoid (fw_view [4096, 1]
          (fw_linear (fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3_faithful initSM 7475))
            (initSM 4770))))
        (fw_view [4096, 1024]
          (fw_linear
            (fw_view [4096, 512]
              (fw_swiglu
                (fw_view [4096, 512]
                  (fw_linear (fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3_faithful initSM 7479))
                    (initSM 4775)))
                (fw_view [4096, 512]
                  (fw_linear (fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3_faithful initSM 7483))
                    (initSM 4779)))))
            (initSM 4784))) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4787 =
      ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4787 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4787 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4787 77 (by decide) (by decide)
  rw [hEntry]
  -- Peel each node (4787 → 4773+4786 → ... → RMS_SM refs)
  have hval_4787 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4787 = elemwiseMul ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4773)) ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4786)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4787 76 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 76 = sm_goal_3_faithful.nodes.take 75 ++ [{ rank := 0, op := "OpName.FW_mul", ins := [4773, 4786], outs := [4787] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 75).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_mul", ins := [4773, 4786], outs := [4787] } (by decide) (by decide),
        applyNode_fw_mul_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 75).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4773 4786 4787,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4773 75 77 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4786 75 77 (by omega) (by decide) (by decide)]
  have hval_4786 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4786 = fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4785)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4786 75 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 75 = sm_goal_3_faithful.nodes.take 74 ++ [{ rank := 0, op := "OpName.FW_view", ins := [4785], outs := [4786], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 74).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_view", ins := [4785], outs := [4786], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_view_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 74).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4096 [1024] 4785 4786,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4785 74 77 (by omega) (by decide) (by decide)]
  have hval_4785 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4785 = fw_linear ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4783)) (initSM 4784) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4785 74 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 74 = sm_goal_3_faithful.nodes.take 73 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4783, 4784], outs := [4785] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 73).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4783, 4784], outs := [4785] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 73).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4783 4784 4785,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4783 73 77 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 73) initSM 4784 (by decide) (by decide)]
  have hval_4783 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4783 = fw_view [4096, 512] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4782)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4783 73 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 73 = sm_goal_3_faithful.nodes.take 72 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [4782], outs := [4783], params := [4096, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 72).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [4782], outs := [4783], params := [4096, 512] } (by decide) (by decide),
        applyNode_fw_reshape_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 72).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4782 4783 [4096, 512],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4782 72 77 (by omega) (by decide) (by decide)]
  have hval_4782 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4782 = fw_swiglu ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4777)) ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4781)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4782 72 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 72 = sm_goal_3_faithful.nodes.take 71 ++ [{ rank := 0, op := "OpName.FW_swiglu", ins := [4777, 4781], outs := [4782] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_swiglu", ins := [4777, 4781], outs := [4782] } (by decide) (by decide),
        applyNode_fw_swiglu_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 71).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4777 4781 4782,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4777 71 77 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4781 71 77 (by omega) (by decide) (by decide)]
  have hval_4781 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4781 = fw_view [4096, 512] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4780)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4781 69 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 69 = sm_goal_3_faithful.nodes.take 68 ++ [{ rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 68).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] } (by decide) (by decide),
        applyNode_fw_view_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 68).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4096 [512] 4780 4781,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4780 68 77 (by omega) (by decide) (by decide)]
  have hval_4780 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4780 = fw_linear ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4778)) (initSM 4779) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4780 65 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 65 = sm_goal_3_faithful.nodes.take 64 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 64).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 64).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4778 4779 4780,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4778 64 77 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 64) initSM 4779 (by decide) (by decide)]
  have hval_4778 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4778 = fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7483)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4778 61 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 61 = sm_goal_3_faithful.nodes.take 60 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [7483], outs := [4778], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 60).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [7483], outs := [4778], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_reshape_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 60).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7483 4778 [4096, 1024],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7483 60 77 (by omega) (by decide) (by decide)]
  have hval_4777 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4777 = fw_view [4096, 512] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4776)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4777 68 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 68 = sm_goal_3_faithful.nodes.take 67 ++ [{ rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] } (by decide) (by decide),
        applyNode_fw_view_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 67).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4096 [512] 4776 4777,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4776 67 77 (by omega) (by decide) (by decide)]
  have hval_4776 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4776 = fw_linear ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4774)) (initSM 4775) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4776 64 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 64 = sm_goal_3_faithful.nodes.take 63 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 63).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 63).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4774 4775 4776,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4774 63 77 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 63) initSM 4775 (by decide) (by decide)]
  have hval_4774 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4774 = fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7479)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4774 60 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 60 = sm_goal_3_faithful.nodes.take 59 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [7479], outs := [4774], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 59).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [7479], outs := [4774], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_reshape_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 59).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7479 4774 [4096, 1024],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7479 59 77 (by omega) (by decide) (by decide)]
  have hval_4773 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4773 = fw_sigmoid ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4772)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4773 71 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 71 = sm_goal_3_faithful.nodes.take 70 ++ [{ rank := 0, op := "OpName.FW_sigmoid", ins := [4772], outs := [4773] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 70).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_sigmoid", ins := [4772], outs := [4773] } (by decide) (by decide),
        applyNode_fw_sigmoid_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 70).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4772 4773,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4772 70 77 (by omega) (by decide) (by decide)]
  have hval_4772 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4772 = fw_view [4096, 1] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4771)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4772 67 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 67 = sm_goal_3_faithful.nodes.take 66 ++ [{ rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 66).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] } (by decide) (by decide),
        applyNode_fw_view_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 66).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4096 [1] 4771 4772,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4771 66 77 (by omega) (by decide) (by decide)]
  have hval_4771 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4771 = fw_linear ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4769)) (initSM 4770) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4771 63 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 63 = sm_goal_3_faithful.nodes.take 62 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 62).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 62).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4769 4770 4771,
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4769 62 77 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 62) initSM 4770 (by decide) (by decide)]
  have hval_4769 : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 4769 = fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7475)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4769 59 77 (by omega) (by decide) (by decide),
        show sm_goal_3_faithful.nodes.take 59 = sm_goal_3_faithful.nodes.take 58 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [7475], outs := [4769], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [7475], outs := [4769], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_reshape_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7475 4769 [4096, 1024],
        ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7475 58 77 (by omega) (by decide) (by decide)]
  -- 7475/7479/7483 dg bridges
  have hval_7475_dg : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7475 = denoteGraph_ringAttn sm_goal_3_faithful initSM 7475 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7475 77 (by decide) (by decide)).symm
  have hval_7479_dg : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7479 = denoteGraph_ringAttn sm_goal_3_faithful initSM 7479 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7479 77 (by decide) (by decide)).symm
  have hval_7483_dg : ((sm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) 7483 = denoteGraph_ringAttn sm_goal_3_faithful initSM 7483 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7483 77 (by decide) (by decide)).symm
  rw [hval_4787, hval_4786, hval_4785, hval_4783, hval_4782, hval_4781, hval_4780, hval_4778, hval_4777, hval_4776, hval_4774, hval_4773, hval_4772, hval_4771, hval_4769, hval_7475_dg, hval_7479_dg, hval_7483_dg]

#print axioms denote_sm_goal_3_faithful_4787

-- Helper: PM 4772 = fw_view [4096,1] (fw_linear (fw_view [4096,1024] RMS_PM) initPM 4770)
-- Chain: 4772@183(r1) → 4771@175(r1) → 4769@169(r1) → 11905@161(r1) → 4759@158(r1) → 11889@156(r1) → 4757
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_4772 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4772 =
      fw_view [4096, 1]
        (fw_linear
          (fw_view [4096, 1024]
            (fw_rms_norm (denoteGraph_ringAttn pm_goal_3_faithful initPM 4757) (initPM 4758)))
          (initPM 4770)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4772 =
      ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4772 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4772 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4772 185 (by decide) (by decide)
  rw [hEntry]
  have hval_4772 : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4772 = fw_view [4096, 1] ((((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4771)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4772 184 185 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 184 = pm_goal_3_faithful.nodes.take 183 ++ [{ rank := 1, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 183).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] } (by decide) (by decide),
        applyNode_fw_view_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 183).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4096 [1] 4771 4772,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4771 183 185 (by omega) (by decide) (by decide)]
  have hval_4771 : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4771 = fw_linear ((((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4769)) (initPM 4770) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4771 176 185 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 176 = pm_goal_3_faithful.nodes.take 175 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 175).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 175).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4769 4770 4771,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4769 175 185 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 175) initPM 4770 (by decide) (by decide)]
  have hval_4769 : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4769 = fw_view [4096, 1024] ((((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11905)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4769 170 185 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 170 = pm_goal_3_faithful.nodes.take 169 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [11905], outs := [4769], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 169).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_reshape", ins := [11905], outs := [4769], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 169).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11905 4769 [4096, 1024],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11905 169 185 (by omega) (by decide) (by decide)]
  have hval_11905 : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11905 = ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11905 162 185 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 162 = pm_goal_3_faithful.nodes.take 161 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] } (by decide) (by decide),
        applyNode_fw_multiref5_at_pos2_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 161 185 (by omega) (by decide) (by decide)]
  have hval_4759 : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 = fw_rms_norm ((((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889)) (initPM 4758) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 159 185 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 159 = pm_goal_3_faithful.nodes.take 158 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] } (by decide) (by decide),
        applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11889 4758 4759,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 158 185 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 158) initPM 4758 (by decide) (by decide)]
  have hval_11889 : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889 = ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 156 185 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 156 = pm_goal_3_faithful.nodes.take 155 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } (by decide) (by decide),
        applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4757 11889 [11889, 11890] 2 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 155 185 (by omega) (by decide) (by decide)]
  have hval_4757_dg : ((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4757 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 185 (by decide) (by decide)).symm
  rw [hval_4772, hval_4771, hval_4769, hval_11905, hval_4759, hval_11889, hval_4757_dg]

#print axioms denote_pm_goal_3_faithful_4772

-- PM 4777 = fw_view [4096,512] (fw_linear (fw_view [4096,1024] RMS_PM) initPM 4775)
-- Chain: 4777@185(r1) → 4776@177(r1) → 4774@170(r1) → 11906@161(r1,pos3) → 4759 → 11889 → 4757
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_4777 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4777 =
      fw_view [4096, 512]
        (fw_linear
          (fw_view [4096, 1024]
            (fw_rms_norm (denoteGraph_ringAttn pm_goal_3_faithful initPM 4757) (initPM 4758)))
          (initPM 4775)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4777 =
      ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4777 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4777 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4777 187 (by decide) (by decide)
  rw [hEntry]
  have hval_4777 : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4777 = fw_view [4096, 512] ((((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4776)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4777 186 187 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 186 = pm_goal_3_faithful.nodes.take 185 ++ [{ rank := 1, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] } (by decide) (by decide),
        applyNode_fw_view_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 185).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4096 [512] 4776 4777,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4776 185 187 (by omega) (by decide) (by decide)]
  have hval_4776 : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4776 = fw_linear ((((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4774)) (initPM 4775) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4776 178 187 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 178 = pm_goal_3_faithful.nodes.take 177 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 177).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 177).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4774 4775 4776,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4774 177 187 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 177) initPM 4775 (by decide) (by decide)]
  have hval_4774 : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4774 = fw_view [4096, 1024] ((((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11906)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4774 171 187 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 171 = pm_goal_3_faithful.nodes.take 170 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [11906], outs := [4774], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 170).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_reshape", ins := [11906], outs := [4774], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 170).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11906 4774 [4096, 1024],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11906 170 187 (by omega) (by decide) (by decide)]
  have hval_11906 : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11906 = ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11906 162 187 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 162 = pm_goal_3_faithful.nodes.take 161 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] } (by decide) (by decide),
        applyNode_fw_multiref5_at_pos3_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 161 187 (by omega) (by decide) (by decide)]
  have hval_4759 : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 = fw_rms_norm ((((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889)) (initPM 4758) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 159 187 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 159 = pm_goal_3_faithful.nodes.take 158 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] } (by decide) (by decide),
        applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11889 4758 4759,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 158 187 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 158) initPM 4758 (by decide) (by decide)]
  have hval_11889 : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889 = ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 156 187 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 156 = pm_goal_3_faithful.nodes.take 155 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } (by decide) (by decide),
        applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4757 11889 [11889, 11890] 2 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 155 187 (by omega) (by decide) (by decide)]
  have hval_4757_dg : ((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4757 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 187 (by decide) (by decide)).symm
  rw [hval_4777, hval_4776, hval_4774, hval_11906, hval_4759, hval_11889, hval_4757_dg]

#print axioms denote_pm_goal_3_faithful_4777

-- PM 4781 = fw_view [4096,512] (fw_linear (fw_view [4096,1024] RMS_PM) initPM 4779)
-- Chain: 4781@187(r1)... hEntry needs take 189
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_4781 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4781 =
      fw_view [4096, 512]
        (fw_linear
          (fw_view [4096, 1024]
            (fw_rms_norm (denoteGraph_ringAttn pm_goal_3_faithful initPM 4757) (initPM 4758)))
          (initPM 4779)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4781 =
      ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4781 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4781 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4781 189 (by decide) (by decide)
  rw [hEntry]
  have hval_4781 : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4781 = fw_view [4096, 512] ((((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4780)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4781 188 189 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 188 = pm_goal_3_faithful.nodes.take 187 ++ [{ rank := 1, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] } (by decide) (by decide),
        applyNode_fw_view_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 187).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4096 [512] 4780 4781,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4780 187 189 (by omega) (by decide) (by decide)]
  have hval_4780 : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4780 = fw_linear ((((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4778)) (initPM 4779) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4780 180 189 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 180 = pm_goal_3_faithful.nodes.take 179 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 179).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 179).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4778 4779 4780,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4778 179 189 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 179) initPM 4779 (by decide) (by decide)]
  have hval_4778 : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4778 = fw_view [4096, 1024] ((((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11907)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4778 172 189 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 172 = pm_goal_3_faithful.nodes.take 171 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [11907], outs := [4778], params := [4096, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 171).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_reshape", ins := [11907], outs := [4778], params := [4096, 1024] } (by decide) (by decide),
        applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 171).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11907 4778 [4096, 1024],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11907 171 189 (by omega) (by decide) (by decide)]
  have hval_11907 : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11907 = ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11907 162 189 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 162 = pm_goal_3_faithful.nodes.take 161 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] } (by decide) (by decide),
        applyNode_fw_multiref5_at_pos4_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 161).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 161 189 (by omega) (by decide) (by decide)]
  have hval_4759 : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4759 = fw_rms_norm ((((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889)) (initPM 4758) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4759 159 189 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 159 = pm_goal_3_faithful.nodes.take 158 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] } (by decide) (by decide),
        applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 158).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11889 4758 4759,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 158 189 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 158) initPM 4758 (by decide) (by decide)]
  have hval_11889 : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 11889 = ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11889 156 189 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 156 = pm_goal_3_faithful.nodes.take 155 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } (by decide) (by decide),
        applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 155).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4757 11889 [11889, 11890] 2 (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 155 189 (by omega) (by decide) (by decide)]
  have hval_4757_dg : ((pm_goal_3_faithful.nodes.take 189).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4757 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4757 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4757 189 (by decide) (by decide)).symm
  rw [hval_4781, hval_4780, hval_4778, hval_11907, hval_4759, hval_11889, hval_4757_dg]

#print axioms denote_pm_goal_3_faithful_4781

-- PM 7751 shard-form deep unfold: rank 0 gate·mul path
-- PM 7751 = elemwiseMul (fw_sigmoid (chunkPrimDimN 0 numRanks 0 PM_4772))
--                       (fw_view [2048,1024] (fw_linear (fw_reshape [2048,512]
--                          (fw_swiglu (chunkPrimDimN 0 numRanks 0 PM_4777) (chunkPrimDimN 0 numRanks 0 PM_4781)))
--                          (initPM 4784)))
-- Chain: 7751@208(r0)→7691@198(r0)+7747@206(r0);
--   7691→7689@190(r0)=chunk0(4772);
--   7747→7737@204(r0)→7731@202(r0)→7729@200(r0)+initPM 4784;
--   7729→7707@192(r0)+7725@194(r0); 7707=chunk0(4777), 7725=chunk0(4781)
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_7751 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7751 =
      elemwiseMul
        (fw_sigmoid (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0
          (denoteGraph_ringAttn pm_goal_3_faithful initPM 4772)))
        (fw_view [2048, 1024]
          (fw_linear
            (fw_view [2048, 512]
              (fw_swiglu
                (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0
                  (denoteGraph_ringAttn pm_goal_3_faithful initPM 4777))
                (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0
                  (denoteGraph_ringAttn pm_goal_3_faithful initPM 4781))))
            (initPM 4784))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7751 =
      ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7751 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7751 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7751 210 (by decide) (by decide)
  rw [hEntry]
  -- Peel: 7751 = mul(7691, 7747)
  have hval_7751 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7751 = elemwiseMul ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7691)) ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7747)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7751 209 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 209 = pm_goal_3_faithful.nodes.take 208 ++ [{ rank := 0, op := "OpName.FW_mul", ins := [7691, 7747], outs := [7751] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 208).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_mul", ins := [7691, 7747], outs := [7751] } (by decide) (by decide),
        applyNode_fw_mul_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 208).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7691 7747 7751,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7691 208 210 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7747 208 210 (by omega) (by decide) (by decide)]
  -- 7691 = sigmoid(7689)
  have hval_7691 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7691 = fw_sigmoid ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7689)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7691 199 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 199 = pm_goal_3_faithful.nodes.take 198 ++ [{ rank := 0, op := "OpName.FW_sigmoid", ins := [7689], outs := [7691] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_sigmoid", ins := [7689], outs := [7691] } (by decide) (by decide),
        applyNode_fw_sigmoid_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 198).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7689 7691,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7689 198 210 (by omega) (by decide) (by decide)]
  -- 7689 = chunk0(4772)
  have hval_7689 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7689 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4772)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7689 191 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 191 = pm_goal_3_faithful.nodes.take 190 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4772], outs := [7689], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4772], outs := [7689], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 190).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4772 7689 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4772 190 210 (by omega) (by decide) (by decide)]
  -- 7747 = fw_view [2048,1024] (7737)
  have hval_7747 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7747 = fw_view [2048, 1024] ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7737)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7747 207 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 207 = pm_goal_3_faithful.nodes.take 206 ++ [{ rank := 0, op := "OpName.FW_view", ins := [7737], outs := [7747], params := [2048, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 206).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_view", ins := [7737], outs := [7747], params := [2048, 1024] } (by decide) (by decide),
        applyNode_fw_view_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 206).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 2048 [1024] 7737 7747,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7737 206 210 (by omega) (by decide) (by decide)]
  -- 7737 = fw_linear(7731, initPM 4784)
  have hval_7737 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7737 = fw_linear ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7731)) (initPM 4784) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7737 205 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 205 = pm_goal_3_faithful.nodes.take 204 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7731, 4784], outs := [7737] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 204).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7731, 4784], outs := [7737] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 204).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7731 4784 7737,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7731 204 210 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 204) initPM 4784 (by decide) (by decide)]
  -- 7731 = fw_reshape [2048,512] (7729)
  have hval_7731 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7731 = fw_view [2048, 512] ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7729)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7731 203 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 203 = pm_goal_3_faithful.nodes.take 202 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [7729], outs := [7731], params := [2048, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 202).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_reshape", ins := [7729], outs := [7731], params := [2048, 512] } (by decide) (by decide),
        applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 202).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7729 7731 [2048, 512],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7729 202 210 (by omega) (by decide) (by decide)]
  -- 7729 = fw_swiglu(7707, 7725)
  have hval_7729 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7729 = fw_swiglu ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7707)) ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7725)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7729 201 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 201 = pm_goal_3_faithful.nodes.take 200 ++ [{ rank := 0, op := "OpName.FW_swiglu", ins := [7707, 7725], outs := [7729] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 200).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_swiglu", ins := [7707, 7725], outs := [7729] } (by decide) (by decide),
        applyNode_fw_swiglu_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 200).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7707 7725 7729,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7707 200 210 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7725 200 210 (by omega) (by decide) (by decide)]
  -- 7707 = chunk0(4777)
  have hval_7707 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7707 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4777)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7707 193 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 193 = pm_goal_3_faithful.nodes.take 192 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4777], outs := [7707], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 192).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4777], outs := [7707], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 192).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4777 7707 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4777 192 210 (by omega) (by decide) (by decide)]
  -- 7725 = chunk0(4781)
  have hval_7725 : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7725 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4781)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7725 195 210 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 195 = pm_goal_3_faithful.nodes.take 194 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4781], outs := [7725], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 194).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4781], outs := [7725], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 194).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4781 7725 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4781 194 210 (by omega) (by decide) (by decide)]
  -- dg bridges for 4772/4777/4781
  have hval_4772_dg : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4772 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4772 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4772 210 (by decide) (by decide)).symm
  have hval_4777_dg : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4777 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4777 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4777 210 (by decide) (by decide)).symm
  have hval_4781_dg : ((pm_goal_3_faithful.nodes.take 210).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4781 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4781 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4781 210 (by decide) (by decide)).symm
  rw [hval_7751, hval_7691, hval_7689, hval_7747, hval_7737, hval_7731, hval_7729, hval_7707, hval_7725,
      hval_4772_dg, hval_4777_dg, hval_4781_dg]

#print axioms denote_pm_goal_3_faithful_7751

-- PM 7752 = rank-1 mirror
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_faithful_7752 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7752 =
      elemwiseMul
        (fw_sigmoid (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1
          (denoteGraph_ringAttn pm_goal_3_faithful initPM 4772)))
        (fw_view [2048, 1024]
          (fw_linear
            (fw_view [2048, 512]
              (fw_swiglu
                (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1
                  (denoteGraph_ringAttn pm_goal_3_faithful initPM 4777))
                (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1
                  (denoteGraph_ringAttn pm_goal_3_faithful initPM 4781))))
            (initPM 4784))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7752 =
      ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7752 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7752 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7752 211 (by decide) (by decide)
  rw [hEntry]
  have hval_7752 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7752 = elemwiseMul ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7692)) ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7748)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7752 210 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 210 = pm_goal_3_faithful.nodes.take 209 ++ [{ rank := 1, op := "OpName.FW_mul", ins := [7692, 7748], outs := [7752] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 209).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_mul", ins := [7692, 7748], outs := [7752] } (by decide) (by decide),
        applyNode_fw_mul_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 209).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7692 7748 7752,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7692 209 211 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7748 209 211 (by omega) (by decide) (by decide)]
  have hval_7692 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7692 = fw_sigmoid ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7690)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7692 200 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 200 = pm_goal_3_faithful.nodes.take 199 ++ [{ rank := 1, op := "OpName.FW_sigmoid", ins := [7690], outs := [7692] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_sigmoid", ins := [7690], outs := [7692] } (by decide) (by decide),
        applyNode_fw_sigmoid_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 199).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7690 7692,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7690 199 211 (by omega) (by decide) (by decide)]
  have hval_7690 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7690 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4772)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7690 192 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 192 = pm_goal_3_faithful.nodes.take 191 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4772], outs := [7690], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4772], outs := [7690], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 191).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4772 7690 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4772 191 211 (by omega) (by decide) (by decide)]
  have hval_7748 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7748 = fw_view [2048, 1024] ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7738)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7748 208 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 208 = pm_goal_3_faithful.nodes.take 207 ++ [{ rank := 1, op := "OpName.FW_view", ins := [7738], outs := [7748], params := [2048, 1024] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 207).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_view", ins := [7738], outs := [7748], params := [2048, 1024] } (by decide) (by decide),
        applyNode_fw_view_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 207).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 2048 [1024] 7738 7748,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7738 207 211 (by omega) (by decide) (by decide)]
  have hval_7738 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7738 = fw_linear ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7732)) (initPM 4784) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7738 206 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 206 = pm_goal_3_faithful.nodes.take 205 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7732, 4784], outs := [7738] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 205).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7732, 4784], outs := [7738] } (by decide) (by decide),
        applyNode_fw_mix_precision_linear_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 205).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7732 4784 7738,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7732 205 211 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 205) initPM 4784 (by decide) (by decide)]
  have hval_7732 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7732 = fw_view [2048, 512] ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7730)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7732 204 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 204 = pm_goal_3_faithful.nodes.take 203 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [7730], outs := [7732], params := [2048, 512] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 203).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_reshape", ins := [7730], outs := [7732], params := [2048, 512] } (by decide) (by decide),
        applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 203).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7730 7732 [2048, 512],
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7730 203 211 (by omega) (by decide) (by decide)]
  have hval_7730 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7730 = fw_swiglu ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7708)) ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7726)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7730 202 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 202 = pm_goal_3_faithful.nodes.take 201 ++ [{ rank := 1, op := "OpName.FW_swiglu", ins := [7708, 7726], outs := [7730] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 201).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_swiglu", ins := [7708, 7726], outs := [7730] } (by decide) (by decide),
        applyNode_fw_swiglu_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 201).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7708 7726 7730,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7708 201 211 (by omega) (by decide) (by decide),
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7726 201 211 (by omega) (by decide) (by decide)]
  have hval_7708 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7708 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4777)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7708 194 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 194 = pm_goal_3_faithful.nodes.take 193 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4777], outs := [7708], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 193).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4777], outs := [7708], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 193).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4777 7708 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4777 193 211 (by omega) (by decide) (by decide)]
  have hval_7726 : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 7726 = chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4781)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7726 196 211 (by omega) (by decide) (by decide),
        show pm_goal_3_faithful.nodes.take 196 = pm_goal_3_faithful.nodes.take 195 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4781], outs := [7726], params := [0] }] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 195).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4781], outs := [7726], params := [0] } (by decide) (by decide),
        applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 195).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4781 7726 0,
        ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4781 195 211 (by omega) (by decide) (by decide)]
  have hval_4772_dg : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4772 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4772 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4772 211 (by decide) (by decide)).symm
  have hval_4777_dg : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4777 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4777 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4777 211 (by decide) (by decide)).symm
  have hval_4781_dg : ((pm_goal_3_faithful.nodes.take 211).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) 4781 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4781 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4781 211 (by decide) (by decide)).symm
  rw [hval_7752, hval_7692, hval_7690, hval_7748, hval_7738, hval_7732, hval_7730, hval_7708, hval_7726,
      hval_4772_dg, hval_4777_dg, hval_4781_dg]

#print axioms denote_pm_goal_3_faithful_7752

-- Sub-commute B: SM 4787 = allGather [PM 7751, PM 7752] (gate·mul path)
-- TODO: assembly using fw_mul_allGather0_commute_2_of_broadcast + fw_sigmoid/swiglu/linear/view allGather commutes
-- Sketch of proof (still needs debugging):
--   1. Deep unfold both sides via denote_sm/pm_goal_3_faithful_4787/7751/7752 (done)
--   2. Bridge PM 4772/4777/4781 → via existing deep unfolds (done)
--   3. Bridge SM 7475/7479/7483 → fw_rms_norm form (missing helpers, need to prove or import)
--   4. sm_pm_carry_4757_commute + hII/hb for initSM 4758/4770/4775/4779/4784 = initPM
--   5. allGather0_reconstruct_chunks_2d for PM_4772/4777/4781
--   6. fw_view_allGather0_commute_2_of + fw_linear_allGather0_commute_2_of
--      + fw_swiglu_allGather0_commute_2 + fw_sigmoid_allGather0_commute_2
--      + fw_mul_allGather0_commute_2_of_broadcast
-- This is ~250 lines assembly. Deferred for main theorem attempt.
theorem sm_pm_gate_mul_L1_commute
    (initSM initPM : Store)
    (h_ss_sm : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4787
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3_faithful initPM 7751,
           denoteGraph_ringAttn pm_goal_3_faithful initPM 7752] := by
  sorry

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem sm_pm_carry_4790_commute
    (initSM initPM : Store)
    (h_ss_sm : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4790
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3_faithful initPM 7765,
           denoteGraph_ringAttn pm_goal_3_faithful initPM 7766] := by
  sorry


end TrainVerify.Denote.Pattern3Faithful
