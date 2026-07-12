/-
  Pattern_3_L14_spike.lean — L14 zigzag-band proof (generic layer).
-/
import denote.yoco_goals.Pattern_3_L12_spike
import denote.yoco_goals.Pattern_3_L13_spike
set_option maxRecDepth 100000
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
namespace TrainVerify.Denote.GeneratedPatterns
-- Node definitions for L12
def nSM_14 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5440, 5441, 5442, 5443, 5444], outs := [5445],
    params := [16, 4, 64, 64, 1, 0] }
def nR0_14 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10007, 5441, 5442, 5443, 5444], outs := [10031],
    params := [16, 4, 64, 64, 1, 0] }
def nR1_14 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10008, 5441, 5442, 5443, 5444], outs := [10032],
    params := [16, 4, 64, 64, 1, 0] }
-- Buddy proofs (ring attention requires proving nodes are buddies)
set_option maxRecDepth 1000000 in
theorem buddy_sm_14 : ringAttnBuddies sm_goal_3 nSM_14 = [nSM_14] := by
  show (List.filter (fun m => decide (m.op = nSM_14.op) && decide (m.params = nSM_14.params) &&
      decide (m.ins.getD 3 0 = nSM_14.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_14.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_14]
  rw [show (List.filter (fun m => decide (m.op = nSM_14.op) && decide (m.params = nSM_14.params) &&
      decide (m.ins.getD 3 0 = nSM_14.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_14.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_14] from by rfl]
  simp
set_option maxRecDepth 1000000 in
theorem buddy_r0_14 : ringAttnBuddies pm_goal_3 nR0_14 = [nR0_14, nR1_14] := by
  show (List.filter (fun m => decide (m.op = nR0_14.op) && decide (m.params = nR0_14.params) &&
      decide (m.ins.getD 3 0 = nR0_14.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_14.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_14, nR1_14]
  rw [show (List.filter (fun m => decide (m.op = nR0_14.op) && decide (m.params = nR0_14.params) &&
      decide (m.ins.getD 3 0 = nR0_14.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_14.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_14, nR1_14] from by rfl]
  apply List.mergeSort_of_pairwise; decide
set_option maxRecDepth 1000000 in
theorem buddy_r1_14 : ringAttnBuddies pm_goal_3 nR1_14 = [nR0_14, nR1_14] := by
  show (List.filter (fun m => decide (m.op = nR1_14.op) && decide (m.params = nR1_14.params) &&
      decide (m.ins.getD 3 0 = nR1_14.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_14.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_14, nR1_14]
  rw [show (List.filter (fun m => decide (m.op = nR1_14.op) && decide (m.params = nR1_14.params) &&
      decide (m.ins.getD 3 0 = nR1_14.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_14.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_14, nR1_14] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L12 TID Lookup Table

Based on extraction from Goal_3.lean, here are the confirmed L12 tids:
-/

-- === hand-written K/V + Q-path denote ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5441 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5441 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5441 8041 482
    ({ rank := 0, op := "OpName.FW_to", ins := [8041], outs := [5441] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8041 5441 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8041 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8041 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5442 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5442 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5442 8099 494
    ({ rank := 0, op := "OpName.FW_to", ins := [8099], outs := [5442] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8099 5442 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8099 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8099 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8221 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8221 =
      denoteGraph_ringAttn sm_goal_3 initSM 5436 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8221 5436 571
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5436], outs := [8217, 8221], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5436 8221 [8217, 8221] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5438 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5438 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5436) (initSM 5437) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5438 8217 5437 572
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8217, 5437], outs := [5438] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8217 5437 5438)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8217 5436 571
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5436], outs := [8217, 8221], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5436 8217 [8217, 8221] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5437 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5440 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5440 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5438) (initSM 5439) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5440 5438 5439 573
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5438, 5439], outs := [5440] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5438 5439 5440 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5439 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5441 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5441 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5441 15823 1033
    ({ rank := 1, op := "OpName.FW_to", ins := [15823], outs := [5441] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15823 5441 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15823 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15823 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5442 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5442 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5442 15929 1057
    ({ rank := 1, op := "OpName.FW_to", ins := [15929], outs := [5442] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15929 5442 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15929 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15929 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16129 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16129 =
      denoteGraph_ringAttn pm_goal_3 initPM 10001 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16129 10001 1201
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10001], outs := [16125, 16129], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10001 16129 [16125, 16129] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16137 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16137 =
      denoteGraph_ringAttn pm_goal_3 initPM 10002 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16137 10002 1202
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10002], outs := [16133, 16137], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10002 16137 [16133, 16137] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10005 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10005 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10001) (initPM 5437) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10005 16125 5437 1203
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16125, 5437], outs := [10005] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16125 5437 10005)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16125 10001 1201
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10001], outs := [16125, 16129], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10001 16125 [16125, 16129] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5437 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10007 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10007 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10005) (initPM 5439) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10007 10005 5439 1205
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10005, 5439], outs := [10007] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 10005 5439 10007 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5439 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10006 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10006 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10002) (initPM 5437) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10006 16133 5437 1204
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16133, 5437], outs := [10006] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16133 5437 10006)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16133 10002 1202
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10002], outs := [16133, 16137], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10002 16133 [16133, 16137] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5437 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10008 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10008 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10006) (initPM 5439) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10008 10006 5439 1206
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10006, 5439], outs := [10008] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 10006 5439 10008 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5439 (by decide) (by decide))

-- === auto-ported generic denote ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5446 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5446 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5445) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5446 5445 575
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5445], outs := [5446], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5445 5446 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5447 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5447 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5446) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5447 5446 576
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5446], outs := [5447], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5446 5447 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5449 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5449 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5447) (initSM 5448) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5449 5447 5448 577
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5447, 5448], outs := [5449] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5447 5448 5449)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5448 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5450 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5450 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5449) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5450 5449 578
    ({ rank := 0, op := "OpName.FW_view", ins := [5449], outs := [5450], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5449 5450)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5451 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5451 =
      denoteGraph_ringAttn sm_goal_3 initSM 5450 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5451 5450 579
    ({ rank := 0, op := "OpName.FW_float", ins := [5450], outs := [5451] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5450 5451 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5452 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5452 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8221)
        (denoteGraph_ringAttn sm_goal_3 initSM 5451) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5452 8221 5451 580
    ({ rank := 0, op := "OpName.FW_add", ins := [8221, 5451], outs := [5452] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8221 5451 5452)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5454 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5454 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5452) (initSM 5453) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5454 8225 5453 582
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8225, 5453], outs := [5454] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8225 5453 5454)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8225 5452 581
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5452], outs := [8225, 8229], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5452 8225 [8225, 8229] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5453 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5455 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5455 =
      denoteGraph_ringAttn sm_goal_3 initSM 5454 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5455 8236 584
    ({ rank := 0, op := "OpName.FW_float", ins := [8236], outs := [5455] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8236 5455 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8236 5454 583
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5454 8236 [8236, 8240, 8244, 8248, 8252] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5457 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5457 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5455) (initSM 5456) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5457 5455 5456 588
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5455, 5456], outs := [5457] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5455 5456 5457 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5456 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5459 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5459 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5457) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5457).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5459 5457 592
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5457], outs := [5458, 5459, 5460], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5457 5458 5459 5460 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10033 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10033 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10031) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10033 10031 1209
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10031], outs := [10033], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10031 10033 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10039 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10039 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10033) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10039 10033 1211
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10033], outs := [10039], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10033 10039 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10043 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10043 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10039) (initPM 5448) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10043 10039 5448 1213
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10039, 5448], outs := [10043] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10039 5448 10043)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5448 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10053 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10053 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10043) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10053 10043 1215
    ({ rank := 0, op := "OpName.FW_view", ins := [10043], outs := [10053], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10043 10053)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10057 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10057 =
      denoteGraph_ringAttn pm_goal_3 initPM 10053 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10057 10053 1217
    ({ rank := 0, op := "OpName.FW_float", ins := [10053], outs := [10057] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10053 10057 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10034 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10034 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10032) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10034 10032 1210
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10032], outs := [10034], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10032 10034 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10040 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10040 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10034) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10040 10034 1212
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10034], outs := [10040], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10034 10040 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10044 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10044 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10040) (initPM 5448) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10044 10040 5448 1214
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10040, 5448], outs := [10044] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10040 5448 10044)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5448 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10054 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10054 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10044) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10054 10044 1216
    ({ rank := 1, op := "OpName.FW_view", ins := [10044], outs := [10054], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10044 10054)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10058 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10058 =
      denoteGraph_ringAttn pm_goal_3 initPM 10054 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10058 10054 1218
    ({ rank := 1, op := "OpName.FW_float", ins := [10054], outs := [10058] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10054 10058 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10061 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10061 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16129)
        (denoteGraph_ringAttn pm_goal_3 initPM 10057) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10061 16129 10057 1219
    ({ rank := 0, op := "OpName.FW_add", ins := [16129, 10057], outs := [10061] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16129 10057 10061)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10062 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10062 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16137)
        (denoteGraph_ringAttn pm_goal_3 initPM 10058) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10062 16137 10058 1220
    ({ rank := 1, op := "OpName.FW_add", ins := [16137, 10058], outs := [10062] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16137 10058 10062)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10065 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10065 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10061) (initPM 5453) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10065 16141 5453 1223
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16141, 5453], outs := [10065] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16141 5453 10065)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16141 10061 1221
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10061], outs := [16141, 16145], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10061 16141 [16141, 16145] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5453 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10067 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10067 =
      denoteGraph_ringAttn pm_goal_3 initPM 10065 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10067 16160 1227
    ({ rank := 0, op := "OpName.FW_float", ins := [16160], outs := [10067] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16160 10067 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16160 10065 1225
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10065 16160 [16160, 16164, 16168, 16172, 16176] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10073 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10073 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10067) (initPM 5456) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10073 10067 5456 1235
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [10067, 5456], outs := [10073] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 10067 5456 10073 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5456 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10077 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10077 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10073) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10073).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10077 10073 1243
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10073], outs := [10075, 10077, 10079], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 10073 10075 10077 10079 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10066 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10066 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10062) (initPM 5453) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10066 16149 5453 1224
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16149, 5453], outs := [10066] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16149 5453 10066)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16149 10062 1222
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10062], outs := [16149, 16153], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10062 16149 [16149, 16153] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5453 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10068 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10068 =
      denoteGraph_ringAttn pm_goal_3 initPM 10066 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10068 16183 1231
    ({ rank := 1, op := "OpName.FW_float", ins := [16183], outs := [10068] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16183 10068 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16183 10066 1226
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10066 16183 [16183, 16187, 16191, 16195, 16199] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10074 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10074 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10068) (initPM 5456) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10074 10068 5456 1239
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [10068, 5456], outs := [10074] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 10068 5456 10074 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5456 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10078 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10078 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10074) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10074).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10078 10074 1247
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10074], outs := [10076, 10078, 10080], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 10074 10076 10078 10080 [8] (by decide))
    rfl
-- === L14 attention denote↔applyNode bridges ===
set_option maxRecDepth 20000 in
theorem denote_sm_attn_L14_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5445
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_14 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5445
      = (sm_goal_3.nodes.take 575).foldl (applyNodeRingAttn sm_goal_3) initSM 5445 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5445 575 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 575 = sm_goal_3.nodes.take 574 ++ [nSM_14] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5440 5441 5442 5443 5444 5445 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L14_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10031
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_14 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10031
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10031 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10031 1208 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1208 = pm_goal_3.nodes.take 1207 ++ [nR0_14] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10007 5441 5442 5443 5444 10031 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L14_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10032
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_14 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10032
      = (pm_goal_3.nodes.take 1209).foldl (applyNodeRingAttn pm_goal_3) initPM 10032 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10032 1209 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1209 = pm_goal_3.nodes.take 1208 ++ [nR1_14] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10008 5441 5442 5443 5444 10032 [16, 4, 64, 64, 1, 0]

-- === L14 K/V replication commutes (reuse shared rms 5332 via sm_pm_rms_L12_commute) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5441 =
      denoteGraph_ringAttn pm_goal_3 initPM 5441 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5333 : initSM 5333 = initPM 5333 := hb initGoal_5333 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5441, denote_sm_goal_3_5334, hrms, hw5333,
      denote_pm_goal_3_5441, denote_pm_goal_3_5334]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5442 =
      denoteGraph_ringAttn pm_goal_3 initPM 5442 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5335 : initSM 5335 = initPM 5335 := hb initGoal_5335 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5442, denote_sm_goal_3_5336, hrms, hw5335,
      denote_pm_goal_3_5442, denote_pm_goal_3_5336]

-- === L14 Q full-sharding commute (no maybe_shuffle; direct multiref→rms→per_head) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5436 : denoteGraph_ringAttn sm_goal_3 initSM 5436 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10001,
         denoteGraph_ringAttn pm_goal_3 initPM 10002])
    (h10001 : (denoteGraph_ringAttn pm_goal_3 initPM 10001).shape = [2048, 1024])
    (h10002 : (denoteGraph_ringAttn pm_goal_3 initPM 10002).shape = [2048, 1024])
    (hw5439 : (initPM 5439).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5440 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10007,
         denoteGraph_ringAttn pm_goal_3 initPM 10008] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5437 : initSM 5437 = initPM 5437 := hb initGoal_5437 (by decide) rfl
  have hw5439e : initSM 5439 = initPM 5439 := hb initGoal_5439 (by decide) rfl
  rw [denote_sm_goal_3_5440, denote_sm_goal_3_5438,
      denote_pm_goal_3_10007, denote_pm_goal_3_10005,
      denote_pm_goal_3_10008, denote_pm_goal_3_10006]
  rw [hcarry5436, hw5437, hw5439e]
  have hrms10001 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10001) (initPM 5437)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h10001]
  have hrms10002 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10002) (initPM 5437)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h10002]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5437) 2048 1024 (by omega) (by omega) h10001 h10002,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5439) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms10001 hrms10002 hw5439]

-- === L14 attention commute ===
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626])
    (hcarry5436 : denoteGraph_ringAttn sm_goal_3 initSM 5436 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10001,
         denoteGraph_ringAttn pm_goal_3 initPM 10002])
    (h10001 : (denoteGraph_ringAttn pm_goal_3 initPM 10001).shape = [2048, 1024])
    (h10002 : (denoteGraph_ringAttn pm_goal_3 initPM 10002).shape = [2048, 1024])
    (hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5440).shape.length)
    (hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5441).shape.length)
    (hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5442).shape.length)
    (h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024])
    (h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024])
    (hw5341 : (initPM 5439).shape = [16, 64, 1024])
    (hk_shape :
      ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441).shape
        = [4096, 4, 64])
    (hv_shape :
      ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442])
        ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5443)
        ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5445
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10031,
           denoteGraph_ringAttn pm_goal_3 initPM 10032] := by
  -- folded-store bridges for the K/V replication commutes (denote ↔ prefix fold)
  have hkrepl := sm_pm_krepl_L14_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L14_commute initSM initPM hInit hcarry5330
  -- Q full-sharding commute (Blocker B) lifted into folded-prefix form
  have hq_full :
      (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5440 =
        allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008] := by
    have bq5342 : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5440
        = denoteGraph_ringAttn sm_goal_3 initSM 5440 :=
      (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5440 574 (by decide) (by decide)).symm
    have bq9659 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
        = denoteGraph_ringAttn pm_goal_3 initPM 10007 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1207 (by decide) (by decide)).symm
    have bq9660 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
        = denoteGraph_ringAttn pm_goal_3 initPM 10008 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1207 (by decide) (by decide)).symm
    rw [bq5342, bq9659, bq9660]
    exact sm_pm_qfull_L14_commute initSM initPM hInit hcarry5436 h10001 h10002 hw5341
  -- SM-side folded ↔ denote at K/V tids
  have bSM5343 : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5441
      = denoteGraph_ringAttn sm_goal_3 initSM 5441 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5441 574 (by decide) (by decide)).symm
  have bSM5344 : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5442
      = denoteGraph_ringAttn sm_goal_3 initSM 5442 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5442 574 (by decide) (by decide)).symm
  have bPM5343 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441
      = denoteGraph_ringAttn pm_goal_3 initPM 5441 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5441 1207 (by decide) (by decide)).symm
  have bPM5344 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442
      = denoteGraph_ringAttn pm_goal_3 initPM 5442 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5442 1207 (by decide) (by decide)).symm
  -- cu_seqlens folded = init (not written in prefix) then SM = PM via cut goals
  have hb := L12_weight_eq initSM initPM hInit
  have hS5345 : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5443 = initSM 5443 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 574) initSM 5443 (by decide) (by decide)
  have hS5346 : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5444 = initSM 5444 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 574) initSM 5444 (by decide) (by decide)
  have hP5345 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5443 = initPM 5443 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1207) initPM 5443 (by decide) (by decide)
  have hP5346 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444 = initPM 5444 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1207) initPM 5444 (by decide) (by decide)
  have hw5345 : initSM 5443 = initPM 5443 := hb initGoal_5443 (by decide) rfl
  have hw5346 : initSM 5444 = initPM 5444 := hb initGoal_5444 (by decide) rfl
  -- reconstruction inputs
  have hkfull : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5441
      = (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441 := by
    rw [bSM5343, bPM5343, hkrepl]
  have hvfull : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5442
      = (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442 := by
    rw [bSM5344, bPM5344, hvrepl]
  have hcuQ : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5443
      = (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5443 := by
    rw [hS5345, hP5345, hw5345]
  have hcuK : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5444
      = (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444 := by
    rw [hS5346, hP5346, hw5346]
  -- align rank-1 buddy folded store (take 1208) to reconstruction store (take 1207)
  have e9659 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10007 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1207 1208 (by omega) (by decide) (by decide)).symm
  have e9660 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10008 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1207 1208 (by omega) (by decide) (by decide)).symm
  have e5343 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 5441 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5441 1207 1208 (by omega) (by decide) (by decide)).symm
  have e5344 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 5442 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5442 1207 1208 (by omega) (by decide) (by decide)).symm
  have e5345 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5443
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 5443 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5443 1207 1208 (by omega) (by decide) (by decide)).symm
  have e5346 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444
      = (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 5444 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5444 1207 1208 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_14
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_14 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_14]; intro m hm; fin_cases hm
      · exact e9659
      · exact e9660
    · rw [buddy_r1_14]; intro m hm; fin_cases hm
      · exact e5343
      · exact e5343
    · rw [buddy_r1_14]; intro m hm; fin_cases hm
      · exact e5344
      · exact e5344
    · exact e5345
    · exact e5346
  -- shape-length hyps in folded-store form
  have bSM5342 : (sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5440
      = denoteGraph_ringAttn sm_goal_3 initSM 5440 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5440 574 (by decide) (by decide)).symm
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_14.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5440).shape.length
    rw [bSM5342]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_14.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5441).shape.length
    rw [bSM5343]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_14.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM 5442).shape.length
    rw [bSM5344]; exact hv_sm
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 574).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_14 nR0_14 nR1_14 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_14 buddy_r0_14 buddy_r1_14 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hkfull hvfull hk_shape hv_shape h_bound
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L14_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L14_r0_bridge, ← denote_pm_attn_L14_r1_bridge]
-- === L14 attention commute' (shape hyps discharged; L14 carry-in as hypothesis) ===
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L14_commute' (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5436 : denoteGraph_ringAttn sm_goal_3 initSM 5436 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10001,
         denoteGraph_ringAttn pm_goal_3 initPM 10002])
    (h10001 : (denoteGraph_ringAttn pm_goal_3 initPM 10001).shape = [2048, 1024])
    (h10002 : (denoteGraph_ringAttn pm_goal_3 initPM 10002).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5444)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5445
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10031,
           denoteGraph_ringAttn pm_goal_3 initPM 10032] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9626 initPM hPM
  have hw5439 : (initPM 5439).shape = [16, 64, 1024] := hPM 5439 [16, 64, 1024] (by decide)
  -- L14 Q-path shard shapes (no maybe_shuffle: direct multiref→rms→per_head)
  have h10005 : (denoteGraph_ringAttn pm_goal_3 initPM 10005).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10005, rms_sh]; exact h10001
  have h10007 : (denoteGraph_ringAttn pm_goal_3 initPM 10007).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10007]; exact ph_lin_shape_gen _ _ 2048 16 h10005 hw5439
  have h10006 : (denoteGraph_ringAttn pm_goal_3 initPM 10006).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10006, rms_sh]; exact h10002
  have h10008 : (denoteGraph_ringAttn pm_goal_3 initPM 10008).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10008]; exact ph_lin_shape_gen _ _ 2048 16 h10006 hw5439
  -- Shared K/V (replicated) shapes [4096,4,64] via shared rms 5332
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  have hPM5441 : (denoteGraph_ringAttn pm_goal_3 initPM 5441).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5441, denote_pm_goal_3_5334]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))
  have hPM5442 : (denoteGraph_ringAttn pm_goal_3 initPM 5442).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5442, denote_pm_goal_3_5336]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))
  have hqfull := sm_pm_qfull_L14_commute initSM initPM hInit hcarry5436 h10001 h10002 hw5439
  have hkrepl := sm_pm_krepl_L14_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L14_commute initSM initPM hInit hcarry5330
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5440).shape = [4096, 16, 64] := by
    rw [hqfull]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10007)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5440).shape.length := by
    rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5441).shape.length := by
    rw [hkrepl, hPM5441]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5442).shape.length := by
    rw [hvrepl, hPM5442]; decide
  have bPM5441 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441
      = denoteGraph_ringAttn pm_goal_3 initPM 5441 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5441 1207 (by decide) (by decide)).symm
  have bPM5442 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442
      = denoteGraph_ringAttn pm_goal_3 initPM 5442 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5442 1207 (by decide) (by decide)).symm
  have bPM10007 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
      = denoteGraph_ringAttn pm_goal_3 initPM 10007 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1207 (by decide) (by decide)).symm
  have bPM10008 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
      = denoteGraph_ringAttn pm_goal_3 initPM 10008 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1207 (by decide) (by decide)).symm
  have hk_shape : ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441).shape
      = [4096, 4, 64] := by rw [bPM5441]; exact hPM5441
  have hv_shape : ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442).shape
      = [4096, 4, 64] := by rw [bPM5442]; exact hPM5442
  have hP5444 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444 = initPM 5444 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1207) initPM 5444 (by decide) (by decide)
  have h_bound' : ∀ t, (decodeCuSeqlens
      ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444)).getD (t+1) 0 ≤ 4096 := by
    intro t; rw [hP5444]; exact h_bound t
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5441])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442,
           (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5442])
        ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5443)
        ((pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 5444)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007,
         (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008]).shape
        = [4096, 16, 64] := by
      rw [bPM10007, bPM10008]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10007)
    rw [hq]; rfl
  exact sm_pm_attention_L14_commute initSM initPM hInit hcarry5330 hcarry5436 h10001 h10002
    hq_sm hk_sm hv_sm h9625 h9626 hw5439 hk_shape hv_shape h_bound' hfull_shape

-- === L14 residual carry-aux (multiref passthrough; no shuffle) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_carryaux_L14_commute (initSM initPM : Store)
    (hcarry5436 : denoteGraph_ringAttn sm_goal_3 initSM 5436 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10001,
         denoteGraph_ringAttn pm_goal_3 initPM 10002]) :
    denoteGraph_ringAttn sm_goal_3 initSM 8221 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 16129,
         denoteGraph_ringAttn pm_goal_3 initPM 16137] := by
  rw [denote_sm_goal_3_8221, denote_pm_goal_3_16129, denote_pm_goal_3_16137]
  exact hcarry5436

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_5451_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5445 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10031,
         denoteGraph_ringAttn pm_goal_3 initPM 10032])
    (h9687 : (denoteGraph_ringAttn pm_goal_3 initPM 10031).shape = [2048, 16, 64])
    (h9688 : (denoteGraph_ringAttn pm_goal_3 initPM 10032).shape = [2048, 16, 64])
    (hw5350 : (initPM 5448).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5451 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10057,
         denoteGraph_ringAttn pm_goal_3 initPM 10058] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5448 = initPM 5448 := hb initGoal_5448 (by decide) rfl
  rw [denote_sm_goal_3_5451, denote_sm_goal_3_5450, denote_sm_goal_3_5449,
      denote_sm_goal_3_5447, denote_sm_goal_3_5446,
      denote_pm_goal_3_10057, denote_pm_goal_3_10053, denote_pm_goal_3_10043,
      denote_pm_goal_3_10039, denote_pm_goal_3_10033,
      denote_pm_goal_3_10058, denote_pm_goal_3_10054, denote_pm_goal_3_10044,
      denote_pm_goal_3_10040, denote_pm_goal_3_10034]
  rw [hattn, hw]
  -- merge the two reshapes through the all-gather
  rw [carry_view_commute _ _ h9687 h9688]
  -- shapes of the view² shards
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10031))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10032))).shape = [2048, 1024] := rfl
  -- push the linear through the all-gather
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5448) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5350]
  -- linear-output shapes
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10031))) (initPM 5448)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5350]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10032))) (initPM 5448)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5350]; rfl
  -- closing view is identity-shaped on both sides
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10031))) (initPM 5448),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10032))) (initPM 5448)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5452_commute (initSM initPM : Store)
    (hshuffle : denoteGraph_ringAttn sm_goal_3 initSM 8221 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 16129,
         denoteGraph_ringAttn pm_goal_3 initPM 16137])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5451 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10057,
         denoteGraph_ringAttn pm_goal_3 initPM 10058])
    (h15973 : (denoteGraph_ringAttn pm_goal_3 initPM 16129).shape = [2048, 1024])
    (h15981 : (denoteGraph_ringAttn pm_goal_3 initPM 16137).shape = [2048, 1024])
    (h9713 : (denoteGraph_ringAttn pm_goal_3 initPM 10057).shape = [2048, 1024])
    (h9714 : (denoteGraph_ringAttn pm_goal_3 initPM 10058).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5452 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10061,
         denoteGraph_ringAttn pm_goal_3 initPM 10062] := by
  rw [denote_sm_goal_3_5452, denote_pm_goal_3_10061, denote_pm_goal_3_10062]
  rw [hshuffle, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h15973 h15981 h9713 h9714]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5452 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10061,
         denoteGraph_ringAttn pm_goal_3 initPM 10062])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5457 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10073,
         denoteGraph_ringAttn pm_goal_3 initPM 10074] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5453 = initPM 5453 := hb initGoal_5453 (by decide) rfl
  have hw5358 : initSM 5456 = initPM 5456 := hb initGoal_5456 (by decide) rfl
  have hw5358sh : (initPM 5456).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5456 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5456] using hsh
  rw [denote_sm_goal_3_5457, denote_sm_goal_3_5455, denote_sm_goal_3_5454,
      denote_pm_goal_3_10073, denote_pm_goal_3_10067, denote_pm_goal_3_10065,
      denote_pm_goal_3_10074, denote_pm_goal_3_10068, denote_pm_goal_3_10066]
  rw [hw5355, hw5358, hcarry5354]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5453) 2048 1024 (by omega) (by omega) h9717 h9718]
  have hrms9717 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10061) (initPM 5453)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9717
  have hrms9718 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10062) (initPM 5453)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9718
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5456) 2048 1024 64 (by omega) (by omega) (by omega) hrms9717 hrms9718 hw5358sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L14 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5452 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10061,
         denoteGraph_ringAttn pm_goal_3 initPM 10062])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5459 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10077,
         denoteGraph_ringAttn pm_goal_3 initPM 10078] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5453 = initPM 5453 := hb initGoal_5453 (by decide) rfl
  have hw5358sh : (initPM 5456).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5456 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5456] using hsh
  have hnl := sm_pm_nl_L14_commute initSM initPM hInit hcarry5354 h9717 h9718
  -- PM nl-output shapes [2048, 64]
  have hs9729 : (denoteGraph_ringAttn pm_goal_3 initPM 10073).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10073, denote_pm_goal_3_10067, denote_pm_goal_3_10065]
    exact nl_sh 2048 1024 64 _ (initPM 5456) (by rw [rms_sh]; exact h9717) hw5358sh
  have hs9730 : (denoteGraph_ringAttn pm_goal_3 initPM 10074).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10074, denote_pm_goal_3_10068, denote_pm_goal_3_10066]
    exact nl_sh 2048 1024 64 _ (initPM 5456) (by rw [rms_sh]; exact h9718) hw5358sh
  have hSM5359sh : (denoteGraph_ringAttn sm_goal_3 initSM 5457).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs9729
  rw [denote_sm_goal_3_5459, denote_pm_goal_3_10077, denote_pm_goal_3_10078]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5457).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5359sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10073).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9729]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10074).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9730]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs9729 hs9730
-- === L14 router from attention (post-attention residual + router assembly) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L14_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5436 : denoteGraph_ringAttn sm_goal_3 initSM 5436 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10001,
         denoteGraph_ringAttn pm_goal_3 initPM 10002])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5445 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10031,
         denoteGraph_ringAttn pm_goal_3 initPM 10032])
    (h10031 : (denoteGraph_ringAttn pm_goal_3 initPM 10031).shape = [2048, 16, 64])
    (h10032 : (denoteGraph_ringAttn pm_goal_3 initPM 10032).shape = [2048, 16, 64])
    (h10001 : (denoteGraph_ringAttn pm_goal_3 initPM 10001).shape = [2048, 1024])
    (h10002 : (denoteGraph_ringAttn pm_goal_3 initPM 10002).shape = [2048, 1024])
    (hw5448 : (initPM 5448).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5459 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10077,
         denoteGraph_ringAttn pm_goal_3 initPM 10078] := by
  have hcarryaux := sm_pm_carryaux_L14_commute initSM initPM hcarry5436
  have hreshape := sm_pm_reshape_float_5451_commute initSM initPM hInit hattn h10031 h10032 hw5448
  have h16129 : (denoteGraph_ringAttn pm_goal_3 initPM 16129).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16129]; exact h10001
  have h16137 : (denoteGraph_ringAttn pm_goal_3 initPM 16137).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16137]; exact h10002
  have h10057 : (denoteGraph_ringAttn pm_goal_3 initPM 10057).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10057, denote_pm_goal_3_10053]; rfl
  have h10058 : (denoteGraph_ringAttn pm_goal_3 initPM 10058).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10058, denote_pm_goal_3_10054]; rfl
  have hcarry5452 := sm_pm_carry_5452_commute initSM initPM hcarryaux hreshape h16129 h16137 h10057 h10058
  have h10061 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10061]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16129 h10057
  have h10062 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10062]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16137 h10058
  exact sm_pm_router_commute_L14 initSM initPM hInit hcarry5452 h10061 h10062

/-! ## L14 router capstone

`sm_pm_router_commute_L14_full` is kernel-clean (`[propext, Classical.choice,
Quot.sound]`).  L14 is a *generic* band layer, so its incoming residual carry
`SM 5436` is the L13 layer's carry-out; L13 is not yet on `main`.  Per AGENTS.md
rule 4 / #29 the carry-in commute (`hcarry5436`) and its two PM shard-shape facts
(`h10001`, `h10002`) are kept as *statement-level hypotheses*, not axioms — the
axiom footprint is unaffected.  They are the exact conclusion-form of the same
`sm_pm_carry_*` mechanism already proven on `main` for the L11/L12 boundary
(`sm_pm_carry_5330_commute`, discharged internally here for the shared K/V path),
so the bundle is consistent (allGather of two `[2048,1024]` shards is the true
`[4096,1024]` shape of `SM 5436`) and non-vacuous.  The well-formed-input
`h_bound` contract carries its own vacuity witness below. -/
-- === L14 router capstone (attention output shapes via CP buddy reconstruction) ===
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L14_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5436 : denoteGraph_ringAttn sm_goal_3 initSM 5436 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10001,
         denoteGraph_ringAttn pm_goal_3 initPM 10002])
    (h10001 : (denoteGraph_ringAttn pm_goal_3 initPM 10001).shape = [2048, 1024])
    (h10002 : (denoteGraph_ringAttn pm_goal_3 initPM 10002).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5444)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5459 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10077,
         denoteGraph_ringAttn pm_goal_3 initPM 10078] := by
  have hattn := sm_pm_attention_L14_commute' initSM initPM hSM hPM hInit hcarry5436 h10001 h10002 h_bound
  have hw5439 : (initPM 5439).shape = [16, 64, 1024] := hPM 5439 [16, 64, 1024] (by decide)
  have hw5448 : (initPM 5448).shape = [1024, 1024] := hPM 5448 [1024, 1024] (by decide)
  have h10005 : (denoteGraph_ringAttn pm_goal_3 initPM 10005).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10005, rms_sh]; exact h10001
  have h10007d : (denoteGraph_ringAttn pm_goal_3 initPM 10007).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10007]; exact ph_lin_shape_gen _ _ 2048 16 h10005 hw5439
  have h10006 : (denoteGraph_ringAttn pm_goal_3 initPM 10006).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10006, rms_sh]; exact h10002
  have h10008d : (denoteGraph_ringAttn pm_goal_3 initPM 10008).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10008]; exact ph_lin_shape_gen _ _ 2048 16 h10006 hw5439
  have b1207_10007 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
      = denoteGraph_ringAttn pm_goal_3 initPM 10007 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1207 (by decide) (by decide)).symm
  have b1207_10008 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
      = denoteGraph_ringAttn pm_goal_3 initPM 10008 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1207 (by decide) (by decide)).symm
  have b1208_10007 : (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
      = denoteGraph_ringAttn pm_goal_3 initPM 10007 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1208 (by decide) (by decide)).symm
  have b1208_10008 : (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
      = denoteGraph_ringAttn pm_goal_3 initPM 10008 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1208 (by decide) (by decide)).symm
  have h10031 : (denoteGraph_ringAttn pm_goal_3 initPM 10031).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L14_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_14 nR0_14 nR1_14 0 buddy_r0_14 (by decide)]
    have e0 : nR0_14.ins.getD 0 0 = 10007 := by decide
    have e1 : nR1_14.ins.getD 0 0 = 10008 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_14.ins.getD 0 0),
         (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_14.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1207_10007, b1207_10008]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10007d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10032 : (denoteGraph_ringAttn pm_goal_3 initPM 10032).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L14_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_14 nR0_14 nR1_14 1 buddy_r1_14 (by decide)]
    have e0 : nR0_14.ins.getD 0 0 = 10007 := by decide
    have e1 : nR1_14.ins.getD 0 0 = 10008 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_14.ins.getD 0 0),
         (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_14.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1208_10007, b1208_10008]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10007d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L14_from_attention initSM initPM hInit hcarry5436 hattn
    h10031 h10032 h10001 h10002 hw5448
-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29):
-- the all-zero cu_seqlens store satisfies the bound, so the hypothesis is not vacuous.
theorem sm_pm_router_L14_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5444)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _


-- ============ L14→L15 boundary carry (sm_pm_carry_5485_commute) ============
-- Auto-ported denote bridges for the L14 MoE sublayer + final residual.
-- ==== L14 PM bridges ====
-- L13 port of pm 9731 -> 10075
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10075 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10075 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10073) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10073).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10075 10073 1243
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10073], outs := [10075, 10077, 10079], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 10073 10075 10077 10079 [8])
    rfl


-- L13 port of pm 9732 -> 10076
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10076 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10076 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10074) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10074).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10076 10074 1247
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10074], outs := [10076, 10078, 10080], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 10074 10076 10078 10080 [8])
    rfl


-- L13 port of pm 9741 -> 10085
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10085 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10085 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16164)
        (denoteGraph_ringAttn pm_goal_3 initPM 10075)
        (denoteGraph_ringAttn pm_goal_3 initPM 10077)
        [initPM 10081, initPM 10082] [initPM 10083, initPM 10084]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10085 16164 10075 10077 10081 10082 10083 10084 1251
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16164, 10075, 10077, 10081, 10082, 10083, 10084], outs := [10085], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16164 10075 10077 10081 10082 10083 10084 10085 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10081 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10082 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10083 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10084 (by decide) (by decide))


-- L13 port of pm 9742 -> 10086
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10086 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10086 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16187)
        (denoteGraph_ringAttn pm_goal_3 initPM 10076)
        (denoteGraph_ringAttn pm_goal_3 initPM 10078)
        [initPM 10081, initPM 10082] [initPM 10083, initPM 10084]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10086 16187 10076 10078 10081 10082 10083 10084 1254
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16187, 10076, 10078, 10081, 10082, 10083, 10084], outs := [10086], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16187 10076 10078 10081 10082 10083 10084 10086 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10081 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10082 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10083 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10084 (by decide) (by decide))


-- L13 port of pm 9743 -> 10087
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10087 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10087 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16168) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10087 16168 1228
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16168], outs := [10087], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16168 10087 [2048, 1024])
    rfl


-- L13 port of pm 9744 -> 10088
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10088 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10088 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16191) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10088 16191 1232
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16191], outs := [10088], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16191 10088 [2048, 1024])
    rfl


-- L13 port of pm 9747 -> 10091
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10091 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10091 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10087) (initPM 5465) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10091 10087 5465 1236
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10087, 5465], outs := [10091] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10087 5465 10091)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5465 (by decide) (by decide))


-- L13 port of pm 9748 -> 10092
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10092 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10092 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10088) (initPM 5465) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10092 10088 5465 1240
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10088, 5465], outs := [10092] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10088 5465 10092)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5465 (by decide) (by decide))


-- L13 port of pm 9753 -> 10097
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10097 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10097 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10091) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10097 10091 1244
    ({ rank := 0, op := "OpName.FW_view", ins := [10091], outs := [10097], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 10091 10097)
    rfl


-- L13 port of pm 9754 -> 10098
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10098 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10098 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10092) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10098 10092 1248
    ({ rank := 1, op := "OpName.FW_view", ins := [10092], outs := [10098], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 10092 10098)
    rfl


-- L13 port of pm 9755 -> 10099
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10099 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10099 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10097) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10099 10097 1252
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [10097], outs := [10099] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 10097 10099])
    rfl


-- L13 port of pm 9756 -> 10100
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10100 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10100 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10098) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10100 10098 1255
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [10098], outs := [10100] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 10098 10100])
    rfl


-- L13 port of pm 9757 -> 10101
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10101 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10101 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16172) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10101 16172 1229
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16172], outs := [10101], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16172 10101 [2048, 1024])
    rfl


-- L13 port of pm 9758 -> 10102
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10102 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10102 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16195) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10102 16195 1233
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16195], outs := [10102], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16195 10102 [2048, 1024])
    rfl


-- L13 port of pm 9761 -> 10105
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10105 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10105 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10101) (initPM 5470) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10105 10101 5470 1237
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10101, 5470], outs := [10105] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10101 5470 10105)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5470 (by decide) (by decide))


-- L13 port of pm 9762 -> 10106
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10106 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10106 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10102) (initPM 5470) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10106 10102 5470 1241
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10102, 5470], outs := [10106] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10102 5470 10106)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5470 (by decide) (by decide))


-- L13 port of pm 9771 -> 10115
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10115 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10115 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10105) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10115 10105 1245
    ({ rank := 0, op := "OpName.FW_view", ins := [10105], outs := [10115], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10105 10115)
    rfl


-- L13 port of pm 9772 -> 10116
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10116 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10116 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10106) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10116 10106 1249
    ({ rank := 1, op := "OpName.FW_view", ins := [10106], outs := [10116], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10106 10116)
    rfl


-- L13 port of pm 9775 -> 10119
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10119 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10119 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16176) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10119 16176 1230
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16176], outs := [10119], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16176 10119 [2048, 1024])
    rfl


-- L13 port of pm 9776 -> 10120
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10120 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10120 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16199) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10120 16199 1234
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16199], outs := [10120], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16199 10120 [2048, 1024])
    rfl


-- L13 port of pm 9779 -> 10123
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10123 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10123 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10119) (initPM 5474) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10123 10119 5474 1238
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10119, 5474], outs := [10123] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10119 5474 10123)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5474 (by decide) (by decide))


-- L13 port of pm 9780 -> 10124
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10124 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10124 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10120) (initPM 5474) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10124 10120 5474 1242
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10120, 5474], outs := [10124] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10120 5474 10124)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5474 (by decide) (by decide))


-- L13 port of pm 9789 -> 10133
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10133 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10133 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10123) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10133 10123 1246
    ({ rank := 0, op := "OpName.FW_view", ins := [10123], outs := [10133], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10123 10133)
    rfl


-- L13 port of pm 9790 -> 10134
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10134 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10134 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10124) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10134 10124 1250
    ({ rank := 1, op := "OpName.FW_view", ins := [10124], outs := [10134], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10124 10134)
    rfl


-- L13 port of pm 9793 -> 10137
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10137 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10137 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10115) (denoteGraph_ringAttn pm_goal_3 initPM 10133) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10137 10115 10133 1253
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [10115, 10133], outs := [10137] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 10115 10133 10137])
    rfl rfl


-- L13 port of pm 9794 -> 10138
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10138 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10138 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10116) (denoteGraph_ringAttn pm_goal_3 initPM 10134) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10138 10116 10134 1256
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [10116, 10134], outs := [10138] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 10116 10134 10138])
    rfl rfl


-- L13 port of pm 9795 -> 10139
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10139 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10139 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10137) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10139 10137 1257
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10137], outs := [10139], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10137 10139 [2048, 512])
    rfl


-- L13 port of pm 9796 -> 10140
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10140 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10140 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10138) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10140 10138 1258
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10138], outs := [10140], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10138 10140 [2048, 512])
    rfl


-- L13 port of pm 9801 -> 10145
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10145 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10145 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10139) (initPM 5479) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10145 10139 5479 1259
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10139, 5479], outs := [10145] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10139 5479 10145)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5479 (by decide) (by decide))


-- L13 port of pm 9802 -> 10146
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10146 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10146 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10140) (initPM 5479) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10146 10140 5479 1260
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10140, 5479], outs := [10146] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10140 5479 10146)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5479 (by decide) (by decide))


-- L13 port of pm 9811 -> 10155
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10155 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10155 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10145) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10155 10145 1261
    ({ rank := 0, op := "OpName.FW_view", ins := [10145], outs := [10155], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10145 10155)
    rfl


-- L13 port of pm 9812 -> 10156
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10156 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10156 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10146) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10156 10146 1262
    ({ rank := 1, op := "OpName.FW_view", ins := [10146], outs := [10156], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10146 10156)
    rfl


-- L13 port of pm 9815 -> 10159
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10159 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10159 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10099) (denoteGraph_ringAttn pm_goal_3 initPM 10155) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10159 10099 10155 1263
    ({ rank := 0, op := "OpName.FW_mul", ins := [10099, 10155], outs := [10159] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 10099 10155 10159])
    rfl rfl


-- L13 port of pm 9816 -> 10160
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10160 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10160 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10100) (denoteGraph_ringAttn pm_goal_3 initPM 10156) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10160 10100 10156 1264
    ({ rank := 1, op := "OpName.FW_mul", ins := [10100, 10156], outs := [10160] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 10100 10156 10160])
    rfl rfl


-- L13 port of pm 9819 -> 10163
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10163 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10163 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10085) (denoteGraph_ringAttn pm_goal_3 initPM 10159) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10163 10085 10159 1265
    ({ rank := 0, op := "OpName.FW_add", ins := [10085, 10159], outs := [10163] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 10085 10159 10163)
    rfl rfl


-- L13 port of pm 9820 -> 10164
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10164 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10164 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10086) (denoteGraph_ringAttn pm_goal_3 initPM 10160) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10164 10086 10160 1266
    ({ rank := 1, op := "OpName.FW_add", ins := [10086, 10160], outs := [10164] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 10086 10160 10164)
    rfl rfl


-- L13 port of pm 9825 -> 10169
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10169 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10169 =
      denoteGraph_ringAttn pm_goal_3 initPM 10163 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10169 10163 1267
    ({ rank := 0, op := "OpName.FW_float", ins := [10163], outs := [10169] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10163 10169 [])
    rfl


-- L13 port of pm 9826 -> 10170
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10170 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10170 =
      denoteGraph_ringAttn pm_goal_3 initPM 10164 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10170 10164 1268
    ({ rank := 1, op := "OpName.FW_float", ins := [10164], outs := [10170] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10164 10170 [])
    rfl


-- L13 port of pm 10001 -> 10173
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10173 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10173 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16145) (denoteGraph_ringAttn pm_goal_3 initPM 10169) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10173 16145 10169 1269
    ({ rank := 0, op := "OpName.FW_add", ins := [16145, 10169], outs := [10173] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16145 10169 10173)
    rfl rfl


-- L13 port of pm 10002 -> 10174
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10174 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10174 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16153) (denoteGraph_ringAttn pm_goal_3 initPM 10170) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10174 16153 10170 1270
    ({ rank := 1, op := "OpName.FW_add", ins := [16153, 10170], outs := [10174] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16153 10170 10174)
    rfl rfl


-- L13 port of pm 15989 -> 16145
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16145 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16145 =
      denoteGraph_ringAttn pm_goal_3 initPM 10061 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16145 10061 1221
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10061], outs := [16141, 16145], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 10061 16141 16145 (by decide))
    rfl


-- L13 port of pm 15997 -> 16153
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16153 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16153 =
      denoteGraph_ringAttn pm_goal_3 initPM 10062 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16153 10062 1222
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10062], outs := [16149, 16153], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 10062 16149 16153 (by decide))
    rfl


-- L13 port of pm 16008 -> 16164
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16164 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16164 =
      denoteGraph_ringAttn pm_goal_3 initPM 10065 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16164 10065 1225
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 10065 16160 16164 16168 16172 16176 (by decide))
    rfl


-- L13 port of pm 16012 -> 16168
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16168 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16168 =
      denoteGraph_ringAttn pm_goal_3 initPM 10065 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16168 10065 1225
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 10065 16160 16164 16168 16172 16176 (by decide) (by decide))
    rfl


-- L13 port of pm 16016 -> 16172
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16172 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16172 =
      denoteGraph_ringAttn pm_goal_3 initPM 10065 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16172 10065 1225
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 10065 16160 16164 16168 16172 16176 (by decide) (by decide) (by decide))
    rfl


-- L13 port of pm 16020 -> 16176
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16176 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16176 =
      denoteGraph_ringAttn pm_goal_3 initPM 10065 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16176 10065 1225
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 10065 16160 16164 16168 16172 16176 (by decide) (by decide) (by decide) (by decide))
    rfl


-- L13 port of pm 16031 -> 16187
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16187 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16187 =
      denoteGraph_ringAttn pm_goal_3 initPM 10066 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16187 10066 1226
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 10066 16183 16187 16191 16195 16199 (by decide))
    rfl


-- L13 port of pm 16035 -> 16191
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16191 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16191 =
      denoteGraph_ringAttn pm_goal_3 initPM 10066 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16191 10066 1226
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 10066 16183 16187 16191 16195 16199 (by decide) (by decide))
    rfl


-- L13 port of pm 16039 -> 16195
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16195 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16195 =
      denoteGraph_ringAttn pm_goal_3 initPM 10066 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16195 10066 1226
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 10066 16183 16187 16191 16195 16199 (by decide) (by decide) (by decide))
    rfl


-- L13 port of pm 16043 -> 16199
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16199 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16199 =
      denoteGraph_ringAttn pm_goal_3 initPM 10066 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16199 10066 1226
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 10066 16183 16187 16191 16195 16199 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ==== L14 SM bridges ====
-- L13 port of sm 5360 -> 5458
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5458 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5458 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5457) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5457).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5458 5457 592
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5457], outs := [5458, 5459, 5460], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5457 5458 5459 5460 [8])
    rfl


-- L13 port of sm 5365 -> 5463
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5463 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5463 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8240)
        (denoteGraph_ringAttn sm_goal_3 initSM 5458)
        (denoteGraph_ringAttn sm_goal_3 initSM 5459)
        (initSM 5461) (initSM 5462) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5463 8240 5458 5459 5461 5462 596
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8240, 5458, 5459, 5461, 5462], outs := [5463], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8240 5458 5459 5461 5462 5463 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5461 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5462 (by decide) (by decide))


-- L13 port of sm 5366 -> 5464
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5464 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5464 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8244) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5464 8244 585
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8244], outs := [5464], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8244 5464 [4096, 1024])
    rfl


-- L13 port of sm 5368 -> 5466
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5466 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5466 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5464) (initSM 5465) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5466 5464 5465 589
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5464, 5465], outs := [5466] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5464 5465 5466)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5465 (by decide) (by decide))


-- L13 port of sm 5369 -> 5467
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5467 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5467 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5466) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5467 5466 593
    ({ rank := 0, op := "OpName.FW_view", ins := [5466], outs := [5467], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5466 5467)
    rfl


-- L13 port of sm 5370 -> 5468
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5468 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5468 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5467) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5468 5467 597
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5467], outs := [5468] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5467 5468])
    rfl


-- L13 port of sm 5371 -> 5469
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5469 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5469 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8248) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5469 8248 586
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8248], outs := [5469], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8248 5469 [4096, 1024])
    rfl


-- L13 port of sm 5373 -> 5471
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5471 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5471 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5469) (initSM 5470) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5471 5469 5470 590
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5469, 5470], outs := [5471] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5469 5470 5471)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5470 (by decide) (by decide))


-- L13 port of sm 5374 -> 5472
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5472 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5472 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5471) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5472 5471 594
    ({ rank := 0, op := "OpName.FW_view", ins := [5471], outs := [5472], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5471 5472)
    rfl


-- L13 port of sm 5375 -> 5473
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5473 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5473 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8252) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5473 8252 587
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8252], outs := [5473], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8252 5473 [4096, 1024])
    rfl


-- L13 port of sm 5377 -> 5475
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5475 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5475 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5473) (initSM 5474) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5475 5473 5474 591
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5473, 5474], outs := [5475] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5473 5474 5475)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5474 (by decide) (by decide))


-- L13 port of sm 5378 -> 5476
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5476 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5476 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5475) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5476 5475 595
    ({ rank := 0, op := "OpName.FW_view", ins := [5475], outs := [5476], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5475 5476)
    rfl


-- L13 port of sm 5379 -> 5477
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5477 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5477 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5472) (denoteGraph_ringAttn sm_goal_3 initSM 5476) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5477 5472 5476 598
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5472, 5476], outs := [5477] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5472 5476 5477])
    rfl rfl


-- L13 port of sm 5380 -> 5478
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5478 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5478 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5477) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5478 5477 599
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5477], outs := [5478], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5477 5478 [4096, 512])
    rfl


-- L13 port of sm 5382 -> 5480
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5480 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5480 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5478) (initSM 5479) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5480 5478 5479 600
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5478, 5479], outs := [5480] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5478 5479 5480)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5479 (by decide) (by decide))


-- L13 port of sm 5383 -> 5481
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5481 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5481 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5480) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5481 5480 601
    ({ rank := 0, op := "OpName.FW_view", ins := [5480], outs := [5481], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5480 5481)
    rfl


-- L13 port of sm 5384 -> 5482
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5482 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5482 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5468) (denoteGraph_ringAttn sm_goal_3 initSM 5481) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5482 5468 5481 602
    ({ rank := 0, op := "OpName.FW_mul", ins := [5468, 5481], outs := [5482] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5468 5481 5482])
    rfl rfl


-- L13 port of sm 5385 -> 5483
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5483 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5483 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5463) (denoteGraph_ringAttn sm_goal_3 initSM 5482) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5483 5463 5482 603
    ({ rank := 0, op := "OpName.FW_add", ins := [5463, 5482], outs := [5483] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5463 5482 5483)
    rfl rfl


-- L13 port of sm 5386 -> 5484
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5484 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5484 =
      denoteGraph_ringAttn sm_goal_3 initSM 5483 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5484 5483 604
    ({ rank := 0, op := "OpName.FW_float", ins := [5483], outs := [5484] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5483 5484 [])
    rfl


-- L13 port of sm 5436 -> 5485
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5485 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8229) (denoteGraph_ringAttn sm_goal_3 initSM 5484) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5485 8229 5484 605
    ({ rank := 0, op := "OpName.FW_add", ins := [8229, 5484], outs := [5485] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8229 5484 5485)
    rfl rfl


-- L13 port of sm 8151 -> 8229
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8229 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8229 =
      denoteGraph_ringAttn sm_goal_3 initSM 5452 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8229 5452 581
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5452], outs := [8225, 8229], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5452 8225 8229 (by decide))
    rfl


-- L13 port of sm 8162 -> 8240
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8240 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8240 =
      denoteGraph_ringAttn sm_goal_3 initSM 5454 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8240 5454 583
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5454 8236 8240 8244 8248 8252 (by decide))
    rfl


-- L13 port of sm 8166 -> 8244
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8244 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8244 =
      denoteGraph_ringAttn sm_goal_3 initSM 5454 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8244 5454 583
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5454 8236 8240 8244 8248 8252 (by decide) (by decide))
    rfl


-- L13 port of sm 8170 -> 8248
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8248 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8248 =
      denoteGraph_ringAttn sm_goal_3 initSM 5454 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8248 5454 583
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5454 8236 8240 8244 8248 8252 (by decide) (by decide) (by decide))
    rfl


-- L13 port of sm 8174 -> 8252
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8252 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8252 =
      denoteGraph_ringAttn sm_goal_3 initSM 5454 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8252 5454 583
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5454 8236 8240 8244 8248 8252 (by decide) (by decide) (by decide) (by decide))
    rfl






-- ==== L14 MoE commute lemmas + boundary carry + shape helpers ====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5452 : denoteGraph_ringAttn sm_goal_3 initSM 5452 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10061,
         denoteGraph_ringAttn pm_goal_3 initPM 10062])
    (h10061 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024])
    (h10062 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5463 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10085,
         denoteGraph_ringAttn pm_goal_3 initPM 10086] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5453 : initSM 5453 = initPM 5453 := hb initGoal_5453 (by decide) rfl
  have hw5456sh : (initPM 5456).shape = [64, 1024] := by
    have hgh := hII initGoal_5456 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5456] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5461 : initSM 5461 = allGatherPrimDimN 0 2 0 [initPM 10081, initPM 10082] := by
    have hg := hII initGoal_5461 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5461, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10081) (initPM 10082) []
        (by rw [h_ss_pm 10081 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5462 : initSM 5462 = allGatherPrimDimN 0 2 0 [initPM 10083, initPM 10084] := by
    have hg := hII initGoal_5462 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5462, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10083) (initPM 10084) []
        (by rw [h_ss_pm 10083 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L14_commute initSM initPM hInit hcarry5452 h10061 h10062
  have hrouter := sm_pm_router_commute_L14 initSM initPM hInit hcarry5452 h10061 h10062
  -- PM rms output shapes [2048, 1024]
  have h10065sh : (denoteGraph_ringAttn pm_goal_3 initPM 10065).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10065, rms_sh]; exact h10061
  have h10066sh : (denoteGraph_ringAttn pm_goal_3 initPM 10066).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10066, rms_sh]; exact h10062
  -- PM nl output shapes [2048, 64]
  have h10073sh : (denoteGraph_ringAttn pm_goal_3 initPM 10073).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10073, denote_pm_goal_3_10067, denote_pm_goal_3_10065]
    exact nl_sh 2048 1024 64 _ (initPM 5456) (by rw [rms_sh]; exact h10061) hw5456sh
  have h10074sh : (denoteGraph_ringAttn pm_goal_3 initPM 10074).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10074, denote_pm_goal_3_10068, denote_pm_goal_3_10066]
    exact nl_sh 2048 1024 64 _ (initPM 5456) (by rw [rms_sh]; exact h10062) hw5456sh
  have hSM5457sh : (denoteGraph_ringAttn sm_goal_3 initSM 5457).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10073sh
  -- MoE weight shapes
  have hw10081 : (initPM 10081).shape = [32,1024,1024] := h_ss_pm 10081 [32,1024,1024] (by decide)
  have hw10082 : (initPM 10082).shape = [32,1024,1024] := h_ss_pm 10082 [32,1024,1024] (by decide)
  have hw10083 : (initPM 10083).shape = [32,1024,512] := h_ss_pm 10083 [32,1024,512] (by decide)
  have hw10084 : (initPM 10084).shape = [32,1024,512] := h_ss_pm 10084 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10075canon : denoteGraph_ringAttn pm_goal_3 initPM 10075
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10073) 8 64).fst := by
    rw [denote_pm_goal_3_10075,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10073).shape.reverse.head?).getD 1 = 64 from by rw [h10073sh]; rfl]
  have h10076canon : denoteGraph_ringAttn pm_goal_3 initPM 10076
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10074) 8 64).fst := by
    rw [denote_pm_goal_3_10076,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10074).shape.reverse.head?).getD 1 = 64 from by rw [h10074sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10075sh : (denoteGraph_ringAttn pm_goal_3 initPM 10075).shape = [2048, 64] := by
    rw [h10075canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10073sh]; rfl)
  have h10076sh : (denoteGraph_ringAttn pm_goal_3 initPM 10076).shape = [2048, 64] := by
    rw [h10076canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10074sh]; rfl)
  have h10077canon : denoteGraph_ringAttn pm_goal_3 initPM 10077
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10073) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10077,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10073).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10073sh]; rfl]
  have h10078canon : denoteGraph_ringAttn pm_goal_3 initPM 10078
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10074) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10078,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10074).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10074sh]; rfl]
  have h10077sh : (denoteGraph_ringAttn pm_goal_3 initPM 10077).shape = [2048, 64] := by
    rw [h10077canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10073sh
  have h10078sh : (denoteGraph_ringAttn pm_goal_3 initPM 10078).shape = [2048, 64] := by
    rw [h10078canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10074sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 10065) (denoteGraph_ringAttn pm_goal_3 initPM 10066)
    (denoteGraph_ringAttn pm_goal_3 initPM 10075) (denoteGraph_ringAttn pm_goal_3 initPM 10076)
    (denoteGraph_ringAttn pm_goal_3 initPM 10077) (denoteGraph_ringAttn pm_goal_3 initPM 10078)
    (initPM 10081) (initPM 10082) (initPM 10083) (initPM 10084)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10065sh h10066sh h10075sh h10076sh h10077sh h10078sh hw10081 hw10082 hw10083 hw10084
  -- Rewrite RHS via denote unfolds + key
  rw [denote_pm_goal_3_10085, denote_pm_goal_3_10086, denote_pm_goal_3_16164, denote_pm_goal_3_16187,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [denote_sm_goal_3_5463, denote_sm_goal_3_8240, denote_sm_goal_3_5454, denote_sm_goal_3_5458]
  rw [hrouter, h5461, h5462]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5457).shape.reverse.head?).getD 1 = 64 from by rw [hSM5457sh]; rfl]
  rw [hw5453, hcarry5452, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5453) 2048 1024 (by omega) (by omega) h10061 h10062]
  rw [← denote_pm_goal_3_10065, ← denote_pm_goal_3_10066]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10073sh h10074sh]
  rw [← h10075canon, ← h10076canon]
  unfold fw_all2all_moe_gmm_full
  rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L14_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5452 : denoteGraph_ringAttn sm_goal_3 initSM 5452 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10061,
         denoteGraph_ringAttn pm_goal_3 initPM 10062])
    (h10061 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024])
    (h10062 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5482
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10159,
           denoteGraph_ringAttn pm_goal_3 initPM 10160] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5453 : initSM 5453 = initPM 5453 := hb initGoal_5453 (by decide) rfl
  have hw5465 : initSM 5465 = initPM 5465 := hb initGoal_5465 (by decide) rfl
  have hw5470 : initSM 5470 = initPM 5470 := hb initGoal_5470 (by decide) rfl
  have hw5474 : initSM 5474 = initPM 5474 := hb initGoal_5474 (by decide) rfl
  have hw5479 : initSM 5479 = initPM 5479 := hb initGoal_5479 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5452) (initSM 5453)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10065,
           denoteGraph_ringAttn pm_goal_3 initPM 10066] := by
    rw [hcarry5452, hw5453,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5453) 2048 1024 (by omega) (by omega) h10061 h10062,
        ← denote_pm_goal_3_10065, ← denote_pm_goal_3_10066]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 10065 / 10066
  rw [denote_pm_goal_3_10159, denote_pm_goal_3_10160,
      denote_pm_goal_3_10099, denote_pm_goal_3_10097, denote_pm_goal_3_10091, denote_pm_goal_3_10087, denote_pm_goal_3_16168,
      denote_pm_goal_3_10155, denote_pm_goal_3_10145, denote_pm_goal_3_10139, denote_pm_goal_3_10137,
      denote_pm_goal_3_10115, denote_pm_goal_3_10105, denote_pm_goal_3_10101, denote_pm_goal_3_16172,
      denote_pm_goal_3_10133, denote_pm_goal_3_10123, denote_pm_goal_3_10119, denote_pm_goal_3_16176,
      denote_pm_goal_3_10100, denote_pm_goal_3_10098, denote_pm_goal_3_10092, denote_pm_goal_3_10088, denote_pm_goal_3_16191,
      denote_pm_goal_3_10156, denote_pm_goal_3_10146, denote_pm_goal_3_10140, denote_pm_goal_3_10138,
      denote_pm_goal_3_10116, denote_pm_goal_3_10106, denote_pm_goal_3_10102, denote_pm_goal_3_16195,
      denote_pm_goal_3_10134, denote_pm_goal_3_10124, denote_pm_goal_3_10120, denote_pm_goal_3_16199]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5454
  rw [denote_sm_goal_3_5482, denote_sm_goal_3_5468, denote_sm_goal_3_5467, denote_sm_goal_3_5466,
      denote_sm_goal_3_5464, denote_sm_goal_3_8244,
      denote_sm_goal_3_5481, denote_sm_goal_3_5480, denote_sm_goal_3_5478, denote_sm_goal_3_5477,
      denote_sm_goal_3_5472, denote_sm_goal_3_5471, denote_sm_goal_3_5469, denote_sm_goal_3_8248,
      denote_sm_goal_3_5476, denote_sm_goal_3_5475, denote_sm_goal_3_5473, denote_sm_goal_3_8252,
      denote_sm_goal_3_5454]
  rw [hRMS, hw5465, hw5470, hw5474, hw5479]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 10065 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 10066 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10065, rms_sh]; exact h10061
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10066, rms_sh]; exact h10062
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5465).shape = [1, 1024] := h_ss_pm 5465 [1, 1024] (by decide)
  have hw29 : (initPM 5470).shape = [512, 1024] := h_ss_pm 5470 [512, 1024] (by decide)
  have hw33 : (initPM 5474).shape = [512, 1024] := h_ss_pm 5474 [512, 1024] (by decide)
  have hw38 : (initPM 5479).shape = [1024, 512] := h_ss_pm 5479 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5465) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5470) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5474) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5465)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5465)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5470)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5470)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5474)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5474)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5465), fw_linear (fw_view [2048, 1024] B) (initPM 5465)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5465)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5465))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5470), fw_linear (fw_view [2048, 1024] B) (initPM 5470)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5474), fw_linear (fw_view [2048, 1024] B) (initPM 5474)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5465)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5465)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5479) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474))))) (initPM 5479)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))))) (initPM 5479)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474))))) (initPM 5479), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))))) (initPM 5479)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474))))) (initPM 5479)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))))) (initPM 5479))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5465))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5465))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5474))))) (initPM 5479)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5470))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5474))))) (initPM 5479)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]


theorem sm_pm_carry_5485_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hp5346 : initPM 5346 = cu_pin_value)
    (hp5395 : initPM 5395 = cu_pin_value)
    (hp5444 : initPM 5444 = cu_pin_value) :
    denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174] := by
  have h_bound := cu_bound_of_value_pin (initPM 5444) hp5444
  have hcarry5436 := sm_pm_carry_5436_commute initSM initPM hSM hPM hInit hp5346 hp5395
  have h10001 := pm_goal_3_10001_shape initPM hPM
  have h10002 := pm_goal_3_10002_shape initPM hPM
  have hattn := sm_pm_attention_L14_commute' initSM initPM hSM hPM hInit hcarry5436 h10001 h10002 h_bound
  have hw5439 : (initPM 5439).shape = [16, 64, 1024] := hPM 5439 [16, 64, 1024] (by decide)
  have hw5448 : (initPM 5448).shape = [1024, 1024] := hPM 5448 [1024, 1024] (by decide)
  have h10005 : (denoteGraph_ringAttn pm_goal_3 initPM 10005).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10005, rms_sh]; exact h10001
  have h10006 : (denoteGraph_ringAttn pm_goal_3 initPM 10006).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10006, rms_sh]; exact h10002
  have h10007d : (denoteGraph_ringAttn pm_goal_3 initPM 10007).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10007]; exact ph_lin_shape_gen _ _ 2048 16 h10005 hw5439
  have h10008d : (denoteGraph_ringAttn pm_goal_3 initPM 10008).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10008]; exact ph_lin_shape_gen _ _ 2048 16 h10006 hw5439
  -- folded-store ↔ denote bridges at the two attention Q tids
  have b1207_10007 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
      = denoteGraph_ringAttn pm_goal_3 initPM 10007 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1207 (by decide) (by decide)).symm
  have b1207_10008 : (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
      = denoteGraph_ringAttn pm_goal_3 initPM 10008 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1207 (by decide) (by decide)).symm
  have b1208_10007 : (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10007
      = denoteGraph_ringAttn pm_goal_3 initPM 10007 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10007 1208 (by decide) (by decide)).symm
  have b1208_10008 : (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM 10008
      = denoteGraph_ringAttn pm_goal_3 initPM 10008 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10008 1208 (by decide) (by decide)).symm
  -- PM attention output shapes [2048,16,64] (chunk of the full [4096,16,64])
  have h10031 : (denoteGraph_ringAttn pm_goal_3 initPM 10031).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L14_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_14 nR0_14 nR1_14 0 buddy_r0_14 (by decide)]
    have e0 : nR0_14.ins.getD 0 0 = 10007 := by decide
    have e1 : nR1_14.ins.getD 0 0 = 10008 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_14.ins.getD 0 0),
         (pm_goal_3.nodes.take 1207).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_14.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1207_10007, b1207_10008]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10007d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10032 : (denoteGraph_ringAttn pm_goal_3 initPM 10032).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L14_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_14 nR0_14 nR1_14 1 buddy_r1_14 (by decide)]
    have e0 : nR0_14.ins.getD 0 0 = 10007 := by decide
    have e1 : nR1_14.ins.getD 0 0 = 10008 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_14.ins.getD 0 0),
         (pm_goal_3.nodes.take 1208).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_14.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1208_10007, b1208_10008]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10007d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl

  have hreshape := sm_pm_reshape_float_5451_commute initSM initPM hInit hattn h10031 h10032 hw5448
  have h10057 : (denoteGraph_ringAttn pm_goal_3 initPM 10057).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10057, denote_pm_goal_3_10053]; rfl
  have h10058 : (denoteGraph_ringAttn pm_goal_3 initPM 10058).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10058, denote_pm_goal_3_10054]; rfl
  have hshuffle := sm_pm_carryaux_L14_commute initSM initPM hcarry5436
  have h16129 : (denoteGraph_ringAttn pm_goal_3 initPM 16129).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16129]; exact h10001
  have h16137 : (denoteGraph_ringAttn pm_goal_3 initPM 16137).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16137]; exact h10002
  have hcarry5452 := sm_pm_carry_5452_commute initSM initPM hshuffle hreshape h16129 h16137 h10057 h10058
  have h10061 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10061]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16129]; exact h10001) h10057
  have h10062 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10062]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16137]; exact h10002) h10058
  have hgmm := sm_pm_moe_gmm_L14_commute initSM initPM hInit hPM hcarry5452 h10061 h10062
  have hgate := sm_pm_gate_mul_L14_commute initSM initPM hInit hPM hcarry5452 h10061 h10062
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h10065sh : (denoteGraph_ringAttn pm_goal_3 initPM 10065).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10065, rms_sh]; exact h10061
  have h10066sh : (denoteGraph_ringAttn pm_goal_3 initPM 10066).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10066, rms_sh]; exact h10062
  have h10085sh : (denoteGraph_ringAttn pm_goal_3 initPM 10085).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10085, denote_pm_goal_3_16164]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10065sh]; rfl) (by rw [h10065sh]; rfl)
  have h10086sh : (denoteGraph_ringAttn pm_goal_3 initPM 10086).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10086, denote_pm_goal_3_16187]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10066sh]; rfl) (by rw [h10066sh]; rfl)
  have h10099sh : (denoteGraph_ringAttn pm_goal_3 initPM 10099).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10099, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10097]
    exact fw_view_shape_eq _ _
  have h10155sh : (denoteGraph_ringAttn pm_goal_3 initPM 10155).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10155]; exact fw_view_shape_eq _ _
  have h10159sh : (denoteGraph_ringAttn pm_goal_3 initPM 10159).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10159, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10099sh h10155sh]; rfl
  have h10100sh : (denoteGraph_ringAttn pm_goal_3 initPM 10100).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10100, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10098]
    exact fw_view_shape_eq _ _
  have h10156sh : (denoteGraph_ringAttn pm_goal_3 initPM 10156).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10156]; exact fw_view_shape_eq _ _
  have h10160sh : (denoteGraph_ringAttn pm_goal_3 initPM 10160).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10160, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10100sh h10156sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10085) (denoteGraph_ringAttn pm_goal_3 initPM 10159)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10085sh h10159sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10086) (denoteGraph_ringAttn pm_goal_3 initPM 10160)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10086sh h10160sh
  -- === assemble ===
  rw [denote_pm_goal_3_10173, denote_pm_goal_3_16145, denote_pm_goal_3_10169, denote_pm_goal_3_10163,
      denote_pm_goal_3_10174, denote_pm_goal_3_16153, denote_pm_goal_3_10170, denote_pm_goal_3_10164]
  rw [denote_sm_goal_3_5485, denote_sm_goal_3_8229, denote_sm_goal_3_5484, denote_sm_goal_3_5483]
  rw [hcarry5452, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10085) (denoteGraph_ringAttn pm_goal_3 initPM 10086)
        (denoteGraph_ringAttn pm_goal_3 initPM 10159) (denoteGraph_ringAttn pm_goal_3 initPM 10160)
        h10085sh h10086sh h10159sh h10160sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10061) (denoteGraph_ringAttn pm_goal_3 initPM 10062)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10085) (denoteGraph_ringAttn pm_goal_3 initPM 10159))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10086) (denoteGraph_ringAttn pm_goal_3 initPM 10160))
        h10061 h10062 hinnerA hinnerB]



set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10173_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024] := by
  have h10001 := pm_goal_3_10001_shape initPM hPM
  have h10057 : (denoteGraph_ringAttn pm_goal_3 initPM 10057).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10057, denote_pm_goal_3_10053]; rfl
  have h10061 : (denoteGraph_ringAttn pm_goal_3 initPM 10061).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10061]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16129]; exact h10001) h10057
  have h10065sh : (denoteGraph_ringAttn pm_goal_3 initPM 10065).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10065, rms_sh]; exact h10061
  have h10085sh : (denoteGraph_ringAttn pm_goal_3 initPM 10085).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10085, denote_pm_goal_3_16164]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10065sh]; rfl) (by rw [h10065sh]; rfl)
  have h10099sh : (denoteGraph_ringAttn pm_goal_3 initPM 10099).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10099, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10097]
    exact fw_view_shape_eq _ _
  have h10155sh : (denoteGraph_ringAttn pm_goal_3 initPM 10155).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10155]; exact fw_view_shape_eq _ _
  have h10159sh : (denoteGraph_ringAttn pm_goal_3 initPM 10159).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10159, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10099sh h10155sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10085) (denoteGraph_ringAttn pm_goal_3 initPM 10159)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10085sh h10159sh
  have h16145sh : (denoteGraph_ringAttn pm_goal_3 initPM 16145).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16145]; exact h10061
  have h10169sh : (denoteGraph_ringAttn pm_goal_3 initPM 10169).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10169, denote_pm_goal_3_10163]; exact hinnerA
  rw [denote_pm_goal_3_10173]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16145sh h10169sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10174_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024] := by
  have h10002 := pm_goal_3_10002_shape initPM hPM
  have h10058 : (denoteGraph_ringAttn pm_goal_3 initPM 10058).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10058, denote_pm_goal_3_10054]; rfl
  have h10062 : (denoteGraph_ringAttn pm_goal_3 initPM 10062).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10062]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16137]; exact h10002) h10058
  have h10066sh : (denoteGraph_ringAttn pm_goal_3 initPM 10066).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10066, rms_sh]; exact h10062
  have h10086sh : (denoteGraph_ringAttn pm_goal_3 initPM 10086).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10086, denote_pm_goal_3_16187]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10066sh]; rfl) (by rw [h10066sh]; rfl)
  have h10100sh : (denoteGraph_ringAttn pm_goal_3 initPM 10100).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10100, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10098]
    exact fw_view_shape_eq _ _
  have h10156sh : (denoteGraph_ringAttn pm_goal_3 initPM 10156).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10156]; exact fw_view_shape_eq _ _
  have h10160sh : (denoteGraph_ringAttn pm_goal_3 initPM 10160).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10160, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10100sh h10156sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10086) (denoteGraph_ringAttn pm_goal_3 initPM 10160)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10086sh h10160sh
  have h16153sh : (denoteGraph_ringAttn pm_goal_3 initPM 16153).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16153]; exact h10062
  have h10170sh : (denoteGraph_ringAttn pm_goal_3 initPM 10170).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10170, denote_pm_goal_3_10164]; exact hinnerB
  rw [denote_pm_goal_3_10174]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16153sh h10170sh




end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L14_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L14_commute'
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L14_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5485_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10173_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10174_shape
