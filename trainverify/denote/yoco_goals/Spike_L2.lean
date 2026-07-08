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
