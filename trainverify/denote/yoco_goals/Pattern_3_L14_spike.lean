/-
  Pattern_3_L14_spike.lean — L14 zigzag-band proof (generic layer).
-/
import denote.yoco_goals.Pattern_3_L12_spike
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

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L14_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L14_commute'
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L14_hbound_witness
