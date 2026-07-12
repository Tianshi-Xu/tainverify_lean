/-
  Pattern_3_L15_spike.lean — L15 zigzag-band proof (generic layer).
-/
import denote.yoco_goals.Pattern_3_L12_spike
import denote.yoco_goals.Pattern_3_L14_spike
set_option maxRecDepth 100000
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
namespace TrainVerify.Denote.GeneratedPatterns
-- Node definitions for L12
def nSM_15 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5489, 5490, 5491, 5492, 5493], outs := [5494],
    params := [16, 4, 64, 64, 1, 0] }
def nR0_15 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10179, 5490, 5491, 5492, 5493], outs := [10203],
    params := [16, 4, 64, 64, 1, 0] }
def nR1_15 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10180, 5490, 5491, 5492, 5493], outs := [10204],
    params := [16, 4, 64, 64, 1, 0] }
-- Buddy proofs (ring attention requires proving nodes are buddies)
set_option maxRecDepth 1000000 in
theorem buddy_sm_15 : ringAttnBuddies sm_goal_3 nSM_15 = [nSM_15] := by
  show (List.filter (fun m => decide (m.op = nSM_15.op) && decide (m.params = nSM_15.params) &&
      decide (m.ins.getD 3 0 = nSM_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_15.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_15]
  rw [show (List.filter (fun m => decide (m.op = nSM_15.op) && decide (m.params = nSM_15.params) &&
      decide (m.ins.getD 3 0 = nSM_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_15.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_15] from by rfl]
  simp
set_option maxRecDepth 1000000 in
theorem buddy_r0_15 : ringAttnBuddies pm_goal_3 nR0_15 = [nR0_15, nR1_15] := by
  show (List.filter (fun m => decide (m.op = nR0_15.op) && decide (m.params = nR0_15.params) &&
      decide (m.ins.getD 3 0 = nR0_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_15.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_15, nR1_15]
  rw [show (List.filter (fun m => decide (m.op = nR0_15.op) && decide (m.params = nR0_15.params) &&
      decide (m.ins.getD 3 0 = nR0_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_15.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_15, nR1_15] from by rfl]
  apply List.mergeSort_of_pairwise; decide
set_option maxRecDepth 1000000 in
theorem buddy_r1_15 : ringAttnBuddies pm_goal_3 nR1_15 = [nR0_15, nR1_15] := by
  show (List.filter (fun m => decide (m.op = nR1_15.op) && decide (m.params = nR1_15.params) &&
      decide (m.ins.getD 3 0 = nR1_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_15.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_15, nR1_15]
  rw [show (List.filter (fun m => decide (m.op = nR1_15.op) && decide (m.params = nR1_15.params) &&
      decide (m.ins.getD 3 0 = nR1_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_15.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_15, nR1_15] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L12 TID Lookup Table

Based on extraction from Goal_3.lean, here are the confirmed L12 tids:
-/

-- === hand-written K/V + Q-path denote ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5490 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5490 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5490 8045 483
    ({ rank := 0, op := "OpName.FW_to", ins := [8045], outs := [5490] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8045 5490 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8045 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8045 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5491 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5491 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5491 8103 495
    ({ rank := 0, op := "OpName.FW_to", ins := [8103], outs := [5491] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8103 5491 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8103 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8103 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8260 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8260 =
      denoteGraph_ringAttn sm_goal_3 initSM 5485 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8260 5485 606
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8256, 8260], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5485 8260 [8256, 8260] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5487 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5487 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5485) (initSM 5486) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5487 8256 5486 607
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8256, 5486], outs := [5487] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8256 5486 5487)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8256 5485 606
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8256, 8260], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5485 8256 [8256, 8260] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5486 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5489 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5489 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5487) (initSM 5488) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5489 5487 5488 608
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5487, 5488], outs := [5489] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5487 5488 5489 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5488 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5490 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5490 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5490 15827 1034
    ({ rank := 1, op := "OpName.FW_to", ins := [15827], outs := [5490] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15827 5490 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15827 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15827 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5491 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5491 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5491 15933 1058
    ({ rank := 1, op := "OpName.FW_to", ins := [15933], outs := [5491] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15933 5491 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15933 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15933 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16207 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16207 =
      denoteGraph_ringAttn pm_goal_3 initPM 10173 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16207 10173 1271
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10173], outs := [16203, 16207], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10173 16207 [16203, 16207] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16215 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16215 =
      denoteGraph_ringAttn pm_goal_3 initPM 10174 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16215 10174 1272
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10174], outs := [16211, 16215], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10174 16215 [16211, 16215] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10177 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10177 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10173) (initPM 5486) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10177 16203 5486 1273
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16203, 5486], outs := [10177] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16203 5486 10177)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16203 10173 1271
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10173], outs := [16203, 16207], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10173 16203 [16203, 16207] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5486 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10179 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10179 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10177) (initPM 5488) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10179 10177 5488 1275
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10177, 5488], outs := [10179] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 10177 5488 10179 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5488 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10178 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10178 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10174) (initPM 5486) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10178 16211 5486 1274
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16211, 5486], outs := [10178] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16211 5486 10178)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16211 10174 1272
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10174], outs := [16211, 16215], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10174 16211 [16211, 16215] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5486 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10180 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10180 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10178) (initPM 5488) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10180 10178 5488 1276
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10178, 5488], outs := [10180] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 10178 5488 10180 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5488 (by decide) (by decide))

-- === auto-ported generic denote ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5495 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5495 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5494) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5495 5494 610
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5494], outs := [5495], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5494 5495 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5496 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5496 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5495) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5496 5495 611
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5495], outs := [5496], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5495 5496 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5498 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5498 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5496) (initSM 5497) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5498 5496 5497 612
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5496, 5497], outs := [5498] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5496 5497 5498)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5497 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5499 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5499 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5498) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5499 5498 613
    ({ rank := 0, op := "OpName.FW_view", ins := [5498], outs := [5499], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5498 5499)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5500 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5500 =
      denoteGraph_ringAttn sm_goal_3 initSM 5499 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5500 5499 614
    ({ rank := 0, op := "OpName.FW_float", ins := [5499], outs := [5500] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5499 5500 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5501 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5501 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8260)
        (denoteGraph_ringAttn sm_goal_3 initSM 5500) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5501 8260 5500 615
    ({ rank := 0, op := "OpName.FW_add", ins := [8260, 5500], outs := [5501] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8260 5500 5501)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5503 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5503 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5501) (initSM 5502) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5503 8264 5502 617
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8264, 5502], outs := [5503] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8264 5502 5503)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8264 5501 616
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5501], outs := [8264, 8268], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5501 8264 [8264, 8268] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5502 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5504 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5504 =
      denoteGraph_ringAttn sm_goal_3 initSM 5503 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5504 8275 619
    ({ rank := 0, op := "OpName.FW_float", ins := [8275], outs := [5504] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8275 5504 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8275 5503 618
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5503 8275 [8275, 8279, 8283, 8287, 8291] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5506 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5506 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5504) (initSM 5505) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5506 5504 5505 623
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5504, 5505], outs := [5506] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5504 5505 5506 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5505 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5508 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5508 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5506) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5506).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5508 5506 627
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5506], outs := [5507, 5508, 5509], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5506 5507 5508 5509 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10205 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10205 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10203) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10205 10203 1279
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10203], outs := [10205], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10203 10205 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10211 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10211 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10205) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10211 10205 1281
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10205], outs := [10211], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10205 10211 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10215 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10215 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10211) (initPM 5497) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10215 10211 5497 1283
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10211, 5497], outs := [10215] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10211 5497 10215)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5497 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10225 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10225 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10215) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10225 10215 1285
    ({ rank := 0, op := "OpName.FW_view", ins := [10215], outs := [10225], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10215 10225)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10229 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10229 =
      denoteGraph_ringAttn pm_goal_3 initPM 10225 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10229 10225 1287
    ({ rank := 0, op := "OpName.FW_float", ins := [10225], outs := [10229] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10225 10229 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10206 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10206 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10204) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10206 10204 1280
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10204], outs := [10206], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10204 10206 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10212 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10212 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10206) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10212 10206 1282
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10206], outs := [10212], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10206 10212 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10216 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10216 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10212) (initPM 5497) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10216 10212 5497 1284
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10212, 5497], outs := [10216] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10212 5497 10216)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5497 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10226 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10226 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10216) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10226 10216 1286
    ({ rank := 1, op := "OpName.FW_view", ins := [10216], outs := [10226], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10216 10226)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10230 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10230 =
      denoteGraph_ringAttn pm_goal_3 initPM 10226 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10230 10226 1288
    ({ rank := 1, op := "OpName.FW_float", ins := [10226], outs := [10230] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10226 10230 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10233 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10233 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16207)
        (denoteGraph_ringAttn pm_goal_3 initPM 10229) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10233 16207 10229 1289
    ({ rank := 0, op := "OpName.FW_add", ins := [16207, 10229], outs := [10233] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16207 10229 10233)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10234 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10234 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16215)
        (denoteGraph_ringAttn pm_goal_3 initPM 10230) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10234 16215 10230 1290
    ({ rank := 1, op := "OpName.FW_add", ins := [16215, 10230], outs := [10234] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16215 10230 10234)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10237 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10237 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10233) (initPM 5502) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10237 16219 5502 1293
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16219, 5502], outs := [10237] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16219 5502 10237)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16219 10233 1291
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10233], outs := [16219, 16223], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10233 16219 [16219, 16223] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5502 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10239 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10239 =
      denoteGraph_ringAttn pm_goal_3 initPM 10237 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10239 16238 1297
    ({ rank := 0, op := "OpName.FW_float", ins := [16238], outs := [10239] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16238 10239 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16238 10237 1295
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10237 16238 [16238, 16242, 16246, 16250, 16254] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10245 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10245 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10239) (initPM 5505) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10245 10239 5505 1305
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [10239, 5505], outs := [10245] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 10239 5505 10245 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5505 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10249 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10249 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10245) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10245).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10249 10245 1313
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10245], outs := [10247, 10249, 10251], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 10245 10247 10249 10251 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10238 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10238 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10234) (initPM 5502) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10238 16227 5502 1294
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16227, 5502], outs := [10238] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16227 5502 10238)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16227 10234 1292
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10234], outs := [16227, 16231], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10234 16227 [16227, 16231] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5502 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10240 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10240 =
      denoteGraph_ringAttn pm_goal_3 initPM 10238 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10240 16261 1301
    ({ rank := 1, op := "OpName.FW_float", ins := [16261], outs := [10240] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16261 10240 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16261 10238 1296
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10238 16261 [16261, 16265, 16269, 16273, 16277] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10246 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10246 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10240) (initPM 5505) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10246 10240 5505 1309
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [10240, 5505], outs := [10246] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 10240 5505 10246 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5505 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10250 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10250 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10246) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10246).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10250 10246 1317
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10246], outs := [10248, 10250, 10252], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 10246 10248 10250 10252 [8] (by decide))
    rfl
-- === L15 attention denote↔applyNode bridges ===
set_option maxRecDepth 20000 in
theorem denote_sm_attn_L15_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5494
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_15 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5494
      = (sm_goal_3.nodes.take 610).foldl (applyNodeRingAttn sm_goal_3) initSM 5494 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5494 610 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 610 = sm_goal_3.nodes.take 609 ++ [nSM_15] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5489 5490 5491 5492 5493 5494 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L15_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10203
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_15 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10203
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10203 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10203 1278 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1278 = pm_goal_3.nodes.take 1277 ++ [nR0_15] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10179 5490 5491 5492 5493 10203 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L15_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10204
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_15 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10204
      = (pm_goal_3.nodes.take 1279).foldl (applyNodeRingAttn pm_goal_3) initPM 10204 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10204 1279 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1279 = pm_goal_3.nodes.take 1278 ++ [nR1_15] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10180 5490 5491 5492 5493 10204 [16, 4, 64, 64, 1, 0]

-- === L15 K/V replication commutes (reuse shared rms 5332 via sm_pm_rms_L12_commute) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5490 =
      denoteGraph_ringAttn pm_goal_3 initPM 5490 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5333 : initSM 5333 = initPM 5333 := hb initGoal_5333 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5490, denote_sm_goal_3_5334, hrms, hw5333,
      denote_pm_goal_3_5490, denote_pm_goal_3_5334]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5491 =
      denoteGraph_ringAttn pm_goal_3 initPM 5491 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5335 : initSM 5335 = initPM 5335 := hb initGoal_5335 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5491, denote_sm_goal_3_5336, hrms, hw5335,
      denote_pm_goal_3_5491, denote_pm_goal_3_5336]

-- === L15 Q full-sharding commute (no maybe_shuffle; direct multiref→rms→per_head) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5485 : denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174])
    (h10173 : (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024])
    (h10174 : (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024])
    (hw5488 : (initPM 5488).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5489 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10179,
         denoteGraph_ringAttn pm_goal_3 initPM 10180] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5486 : initSM 5486 = initPM 5486 := hb initGoal_5486 (by decide) rfl
  have hw5488e : initSM 5488 = initPM 5488 := hb initGoal_5488 (by decide) rfl
  rw [denote_sm_goal_3_5489, denote_sm_goal_3_5487,
      denote_pm_goal_3_10179, denote_pm_goal_3_10177,
      denote_pm_goal_3_10180, denote_pm_goal_3_10178]
  rw [hcarry5485, hw5486, hw5488e]
  have hrms10173 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10173) (initPM 5486)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h10173]
  have hrms10174 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10174) (initPM 5486)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h10174]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5486) 2048 1024 (by omega) (by omega) h10173 h10174,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5488) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms10173 hrms10174 hw5488]

-- === L15 attention commute ===
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626])
    (hcarry5485 : denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174])
    (h10173 : (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024])
    (h10174 : (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024])
    (hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5489).shape.length)
    (hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5490).shape.length)
    (hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5491).shape.length)
    (h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024])
    (h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024])
    (hw5341 : (initPM 5488).shape = [16, 64, 1024])
    (hk_shape :
      ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490).shape
        = [4096, 4, 64])
    (hv_shape :
      ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491])
        ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5492)
        ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5494
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10203,
           denoteGraph_ringAttn pm_goal_3 initPM 10204] := by
  -- folded-store bridges for the K/V replication commutes (denote ↔ prefix fold)
  have hkrepl := sm_pm_krepl_L15_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L15_commute initSM initPM hInit hcarry5330
  -- Q full-sharding commute (Blocker B) lifted into folded-prefix form
  have hq_full :
      (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5489 =
        allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180] := by
    have bq5342 : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5489
        = denoteGraph_ringAttn sm_goal_3 initSM 5489 :=
      (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5489 609 (by decide) (by decide)).symm
    have bq9659 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
        = denoteGraph_ringAttn pm_goal_3 initPM 10179 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1277 (by decide) (by decide)).symm
    have bq9660 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
        = denoteGraph_ringAttn pm_goal_3 initPM 10180 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1277 (by decide) (by decide)).symm
    rw [bq5342, bq9659, bq9660]
    exact sm_pm_qfull_L15_commute initSM initPM hInit hcarry5485 h10173 h10174 hw5341
  -- SM-side folded ↔ denote at K/V tids
  have bSM5343 : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5490
      = denoteGraph_ringAttn sm_goal_3 initSM 5490 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5490 609 (by decide) (by decide)).symm
  have bSM5344 : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5491
      = denoteGraph_ringAttn sm_goal_3 initSM 5491 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5491 609 (by decide) (by decide)).symm
  have bPM5343 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490
      = denoteGraph_ringAttn pm_goal_3 initPM 5490 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5490 1277 (by decide) (by decide)).symm
  have bPM5344 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491
      = denoteGraph_ringAttn pm_goal_3 initPM 5491 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5491 1277 (by decide) (by decide)).symm
  -- cu_seqlens folded = init (not written in prefix) then SM = PM via cut goals
  have hb := L12_weight_eq initSM initPM hInit
  have hS5345 : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5492 = initSM 5492 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 609) initSM 5492 (by decide) (by decide)
  have hS5346 : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5493 = initSM 5493 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 609) initSM 5493 (by decide) (by decide)
  have hP5345 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5492 = initPM 5492 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1277) initPM 5492 (by decide) (by decide)
  have hP5346 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493 = initPM 5493 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1277) initPM 5493 (by decide) (by decide)
  have hw5345 : initSM 5492 = initPM 5492 := hb initGoal_5492 (by decide) rfl
  have hw5346 : initSM 5493 = initPM 5493 := hb initGoal_5493 (by decide) rfl
  -- reconstruction inputs
  have hkfull : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5490
      = (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490 := by
    rw [bSM5343, bPM5343, hkrepl]
  have hvfull : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5491
      = (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491 := by
    rw [bSM5344, bPM5344, hvrepl]
  have hcuQ : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5492
      = (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5492 := by
    rw [hS5345, hP5345, hw5345]
  have hcuK : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5493
      = (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493 := by
    rw [hS5346, hP5346, hw5346]
  -- align rank-1 buddy folded store (take 1278) to reconstruction store (take 1277)
  have e9659 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10179 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1277 1278 (by omega) (by decide) (by decide)).symm
  have e9660 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10180 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1277 1278 (by omega) (by decide) (by decide)).symm
  have e5343 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 5490 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5490 1277 1278 (by omega) (by decide) (by decide)).symm
  have e5344 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 5491 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5491 1277 1278 (by omega) (by decide) (by decide)).symm
  have e5345 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5492
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 5492 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5492 1277 1278 (by omega) (by decide) (by decide)).symm
  have e5346 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 5493 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5493 1277 1278 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_15
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_15 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_15]; intro m hm; fin_cases hm
      · exact e9659
      · exact e9660
    · rw [buddy_r1_15]; intro m hm; fin_cases hm
      · exact e5343
      · exact e5343
    · rw [buddy_r1_15]; intro m hm; fin_cases hm
      · exact e5344
      · exact e5344
    · exact e5345
    · exact e5346
  -- shape-length hyps in folded-store form
  have bSM5342 : (sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5489
      = denoteGraph_ringAttn sm_goal_3 initSM 5489 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5489 609 (by decide) (by decide)).symm
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_15.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5489).shape.length
    rw [bSM5342]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_15.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5490).shape.length
    rw [bSM5343]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_15.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM 5491).shape.length
    rw [bSM5344]; exact hv_sm
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_15 nR0_15 nR1_15 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_15 buddy_r0_15 buddy_r1_15 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hkfull hvfull hk_shape hv_shape h_bound
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L15_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L15_r0_bridge, ← denote_pm_attn_L15_r1_bridge]
-- === L15 attention commute' (shape hyps discharged; L15 carry-in as hypothesis) ===
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L15_commute' (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5485 : denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174])
    (h10173 : (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024])
    (h10174 : (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5493)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5494
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10203,
           denoteGraph_ringAttn pm_goal_3 initPM 10204] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9626 initPM hPM
  have hw5488 : (initPM 5488).shape = [16, 64, 1024] := hPM 5488 [16, 64, 1024] (by decide)
  -- L15 Q-path shard shapes (no maybe_shuffle: direct multiref→rms→per_head)
  have h10177 : (denoteGraph_ringAttn pm_goal_3 initPM 10177).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10177, rms_sh]; exact h10173
  have h10179 : (denoteGraph_ringAttn pm_goal_3 initPM 10179).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10179]; exact ph_lin_shape_gen _ _ 2048 16 h10177 hw5488
  have h10178 : (denoteGraph_ringAttn pm_goal_3 initPM 10178).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10178, rms_sh]; exact h10174
  have h10180 : (denoteGraph_ringAttn pm_goal_3 initPM 10180).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10180]; exact ph_lin_shape_gen _ _ 2048 16 h10178 hw5488
  -- Shared K/V (replicated) shapes [4096,4,64] via shared rms 5332
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  have hPM5490 : (denoteGraph_ringAttn pm_goal_3 initPM 5490).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5490, denote_pm_goal_3_5334]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))
  have hPM5491 : (denoteGraph_ringAttn pm_goal_3 initPM 5491).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5491, denote_pm_goal_3_5336]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))
  have hqfull := sm_pm_qfull_L15_commute initSM initPM hInit hcarry5485 h10173 h10174 hw5488
  have hkrepl := sm_pm_krepl_L15_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L15_commute initSM initPM hInit hcarry5330
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5489).shape = [4096, 16, 64] := by
    rw [hqfull]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10179)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5489).shape.length := by
    rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5490).shape.length := by
    rw [hkrepl, hPM5490]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5491).shape.length := by
    rw [hvrepl, hPM5491]; decide
  have bPM5490 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490
      = denoteGraph_ringAttn pm_goal_3 initPM 5490 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5490 1277 (by decide) (by decide)).symm
  have bPM5491 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491
      = denoteGraph_ringAttn pm_goal_3 initPM 5491 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5491 1277 (by decide) (by decide)).symm
  have bPM10179 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
      = denoteGraph_ringAttn pm_goal_3 initPM 10179 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1277 (by decide) (by decide)).symm
  have bPM10180 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
      = denoteGraph_ringAttn pm_goal_3 initPM 10180 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1277 (by decide) (by decide)).symm
  have hk_shape : ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490).shape
      = [4096, 4, 64] := by rw [bPM5490]; exact hPM5490
  have hv_shape : ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491).shape
      = [4096, 4, 64] := by rw [bPM5491]; exact hPM5491
  have hP5493 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493 = initPM 5493 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1277) initPM 5493 (by decide) (by decide)
  have h_bound' : ∀ t, (decodeCuSeqlens
      ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493)).getD (t+1) 0 ≤ 4096 := by
    intro t; rw [hP5493]; exact h_bound t
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5490])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491,
           (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5491])
        ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5492)
        ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 5493)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179,
         (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180]).shape
        = [4096, 16, 64] := by
      rw [bPM10179, bPM10180]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10179)
    rw [hq]; rfl
  exact sm_pm_attention_L15_commute initSM initPM hInit hcarry5330 hcarry5485 h10173 h10174
    hq_sm hk_sm hv_sm h9625 h9626 hw5488 hk_shape hv_shape h_bound' hfull_shape

-- === L15 residual carry-aux (multiref passthrough; no shuffle) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_carryaux_L15_commute (initSM initPM : Store)
    (hcarry5485 : denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174]) :
    denoteGraph_ringAttn sm_goal_3 initSM 8260 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 16207,
         denoteGraph_ringAttn pm_goal_3 initPM 16215] := by
  rw [denote_sm_goal_3_8260, denote_pm_goal_3_16207, denote_pm_goal_3_16215]
  exact hcarry5485

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_5500_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5494 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10203,
         denoteGraph_ringAttn pm_goal_3 initPM 10204])
    (h9687 : (denoteGraph_ringAttn pm_goal_3 initPM 10203).shape = [2048, 16, 64])
    (h9688 : (denoteGraph_ringAttn pm_goal_3 initPM 10204).shape = [2048, 16, 64])
    (hw5350 : (initPM 5497).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5500 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10229,
         denoteGraph_ringAttn pm_goal_3 initPM 10230] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5497 = initPM 5497 := hb initGoal_5497 (by decide) rfl
  rw [denote_sm_goal_3_5500, denote_sm_goal_3_5499, denote_sm_goal_3_5498,
      denote_sm_goal_3_5496, denote_sm_goal_3_5495,
      denote_pm_goal_3_10229, denote_pm_goal_3_10225, denote_pm_goal_3_10215,
      denote_pm_goal_3_10211, denote_pm_goal_3_10205,
      denote_pm_goal_3_10230, denote_pm_goal_3_10226, denote_pm_goal_3_10216,
      denote_pm_goal_3_10212, denote_pm_goal_3_10206]
  rw [hattn, hw]
  -- merge the two reshapes through the all-gather
  rw [carry_view_commute _ _ h9687 h9688]
  -- shapes of the view² shards
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10203))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10204))).shape = [2048, 1024] := rfl
  -- push the linear through the all-gather
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5497) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5350]
  -- linear-output shapes
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10203))) (initPM 5497)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5350]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10204))) (initPM 5497)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5350]; rfl
  -- closing view is identity-shaped on both sides
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10203))) (initPM 5497),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10204))) (initPM 5497)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5501_commute (initSM initPM : Store)
    (hshuffle : denoteGraph_ringAttn sm_goal_3 initSM 8260 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 16207,
         denoteGraph_ringAttn pm_goal_3 initPM 16215])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5500 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10229,
         denoteGraph_ringAttn pm_goal_3 initPM 10230])
    (h15973 : (denoteGraph_ringAttn pm_goal_3 initPM 16207).shape = [2048, 1024])
    (h15981 : (denoteGraph_ringAttn pm_goal_3 initPM 16215).shape = [2048, 1024])
    (h9713 : (denoteGraph_ringAttn pm_goal_3 initPM 10229).shape = [2048, 1024])
    (h9714 : (denoteGraph_ringAttn pm_goal_3 initPM 10230).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5501 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10233,
         denoteGraph_ringAttn pm_goal_3 initPM 10234] := by
  rw [denote_sm_goal_3_5501, denote_pm_goal_3_10233, denote_pm_goal_3_10234]
  rw [hshuffle, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h15973 h15981 h9713 h9714]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5501 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10233,
         denoteGraph_ringAttn pm_goal_3 initPM 10234])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5506 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10245,
         denoteGraph_ringAttn pm_goal_3 initPM 10246] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5502 = initPM 5502 := hb initGoal_5502 (by decide) rfl
  have hw5358 : initSM 5505 = initPM 5505 := hb initGoal_5505 (by decide) rfl
  have hw5358sh : (initPM 5505).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5505 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5505] using hsh
  rw [denote_sm_goal_3_5506, denote_sm_goal_3_5504, denote_sm_goal_3_5503,
      denote_pm_goal_3_10245, denote_pm_goal_3_10239, denote_pm_goal_3_10237,
      denote_pm_goal_3_10246, denote_pm_goal_3_10240, denote_pm_goal_3_10238]
  rw [hw5355, hw5358, hcarry5354]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5502) 2048 1024 (by omega) (by omega) h9717 h9718]
  have hrms9717 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10233) (initPM 5502)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9717
  have hrms9718 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10234) (initPM 5502)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9718
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5505) 2048 1024 64 (by omega) (by omega) (by omega) hrms9717 hrms9718 hw5358sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L15 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5501 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10233,
         denoteGraph_ringAttn pm_goal_3 initPM 10234])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5508 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10249,
         denoteGraph_ringAttn pm_goal_3 initPM 10250] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5502 = initPM 5502 := hb initGoal_5502 (by decide) rfl
  have hw5358sh : (initPM 5505).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5505 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5505] using hsh
  have hnl := sm_pm_nl_L15_commute initSM initPM hInit hcarry5354 h9717 h9718
  -- PM nl-output shapes [2048, 64]
  have hs9729 : (denoteGraph_ringAttn pm_goal_3 initPM 10245).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10245, denote_pm_goal_3_10239, denote_pm_goal_3_10237]
    exact nl_sh 2048 1024 64 _ (initPM 5505) (by rw [rms_sh]; exact h9717) hw5358sh
  have hs9730 : (denoteGraph_ringAttn pm_goal_3 initPM 10246).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10246, denote_pm_goal_3_10240, denote_pm_goal_3_10238]
    exact nl_sh 2048 1024 64 _ (initPM 5505) (by rw [rms_sh]; exact h9718) hw5358sh
  have hSM5359sh : (denoteGraph_ringAttn sm_goal_3 initSM 5506).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs9729
  rw [denote_sm_goal_3_5508, denote_pm_goal_3_10249, denote_pm_goal_3_10250]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5506).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5359sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10245).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9729]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10246).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9730]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs9729 hs9730
-- === L15 router from attention (post-attention residual + router assembly) ===
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L15_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5485 : denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5494 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10203,
         denoteGraph_ringAttn pm_goal_3 initPM 10204])
    (h10203 : (denoteGraph_ringAttn pm_goal_3 initPM 10203).shape = [2048, 16, 64])
    (h10204 : (denoteGraph_ringAttn pm_goal_3 initPM 10204).shape = [2048, 16, 64])
    (h10173 : (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024])
    (h10174 : (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024])
    (hw5497 : (initPM 5497).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5508 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10249,
         denoteGraph_ringAttn pm_goal_3 initPM 10250] := by
  have hcarryaux := sm_pm_carryaux_L15_commute initSM initPM hcarry5485
  have hreshape := sm_pm_reshape_float_5500_commute initSM initPM hInit hattn h10203 h10204 hw5497
  have h16207 : (denoteGraph_ringAttn pm_goal_3 initPM 16207).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16207]; exact h10173
  have h16215 : (denoteGraph_ringAttn pm_goal_3 initPM 16215).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16215]; exact h10174
  have h10229 : (denoteGraph_ringAttn pm_goal_3 initPM 10229).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10229, denote_pm_goal_3_10225]; rfl
  have h10230 : (denoteGraph_ringAttn pm_goal_3 initPM 10230).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10230, denote_pm_goal_3_10226]; rfl
  have hcarry5501 := sm_pm_carry_5501_commute initSM initPM hcarryaux hreshape h16207 h16215 h10229 h10230
  have h10233 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10233]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16207 h10229
  have h10234 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10234]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16215 h10230
  exact sm_pm_router_commute_L15 initSM initPM hInit hcarry5501 h10233 h10234

/-! ## L15 router capstone

`sm_pm_router_commute_L15_full` is kernel-clean (`[propext, Classical.choice,
Quot.sound]`).  L15 is a *generic* band layer, so its incoming residual carry
`SM 5485` is the L13 layer's carry-out; L13 is not yet on `main`.  Per AGENTS.md
rule 4 / #29 the carry-in commute (`hcarry5485`) and its two PM shard-shape facts
(`h10173`, `h10174`) are kept as *statement-level hypotheses*, not axioms — the
axiom footprint is unaffected.  They are the exact conclusion-form of the same
`sm_pm_carry_*` mechanism already proven on `main` for the L11/L12 boundary
(`sm_pm_carry_5330_commute`, discharged internally here for the shared K/V path),
so the bundle is consistent (allGather of two `[2048,1024]` shards is the true
`[4096,1024]` shape of `SM 5485`) and non-vacuous.  The well-formed-input
`h_bound` contract carries its own vacuity witness below. -/
-- === L15 router capstone (attention output shapes via CP buddy reconstruction) ===
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L15_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5485 : denoteGraph_ringAttn sm_goal_3 initSM 5485 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10173,
         denoteGraph_ringAttn pm_goal_3 initPM 10174])
    (h10173 : (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024])
    (h10174 : (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5493)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5508 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10249,
         denoteGraph_ringAttn pm_goal_3 initPM 10250] := by
  have hattn := sm_pm_attention_L15_commute' initSM initPM hSM hPM hInit hcarry5485 h10173 h10174 h_bound
  have hw5488 : (initPM 5488).shape = [16, 64, 1024] := hPM 5488 [16, 64, 1024] (by decide)
  have hw5497 : (initPM 5497).shape = [1024, 1024] := hPM 5497 [1024, 1024] (by decide)
  have h10177 : (denoteGraph_ringAttn pm_goal_3 initPM 10177).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10177, rms_sh]; exact h10173
  have h10179d : (denoteGraph_ringAttn pm_goal_3 initPM 10179).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10179]; exact ph_lin_shape_gen _ _ 2048 16 h10177 hw5488
  have h10178 : (denoteGraph_ringAttn pm_goal_3 initPM 10178).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10178, rms_sh]; exact h10174
  have h10180d : (denoteGraph_ringAttn pm_goal_3 initPM 10180).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10180]; exact ph_lin_shape_gen _ _ 2048 16 h10178 hw5488
  have b1277_10179 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
      = denoteGraph_ringAttn pm_goal_3 initPM 10179 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1277 (by decide) (by decide)).symm
  have b1277_10180 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
      = denoteGraph_ringAttn pm_goal_3 initPM 10180 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1277 (by decide) (by decide)).symm
  have b1278_10179 : (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
      = denoteGraph_ringAttn pm_goal_3 initPM 10179 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1278 (by decide) (by decide)).symm
  have b1278_10180 : (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
      = denoteGraph_ringAttn pm_goal_3 initPM 10180 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1278 (by decide) (by decide)).symm
  have h10203 : (denoteGraph_ringAttn pm_goal_3 initPM 10203).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L15_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_15 nR0_15 nR1_15 0 buddy_r0_15 (by decide)]
    have e0 : nR0_15.ins.getD 0 0 = 10179 := by decide
    have e1 : nR1_15.ins.getD 0 0 = 10180 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_15.ins.getD 0 0),
         (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_15.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1277_10179, b1277_10180]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10179d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10204 : (denoteGraph_ringAttn pm_goal_3 initPM 10204).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L15_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_15 nR0_15 nR1_15 1 buddy_r1_15 (by decide)]
    have e0 : nR0_15.ins.getD 0 0 = 10179 := by decide
    have e1 : nR1_15.ins.getD 0 0 = 10180 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_15.ins.getD 0 0),
         (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_15.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1278_10179, b1278_10180]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10179d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L15_from_attention initSM initPM hInit hcarry5485 hattn
    h10203 h10204 h10173 h10174 hw5497
-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29):
-- the all-zero cu_seqlens store satisfies the bound, so the hypothesis is not vacuous.
theorem sm_pm_router_L15_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5493)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _



-- ============ L15->L16 MoE-bridge boundary carry (sm_pm_carry_5534_commute) ============
-- ============ L14→L15 boundary carry (sm_pm_carry_5534_commute) ============
-- Auto-ported denote bridges for the L14 MoE sublayer + final residual.
-- ==== L14 PM bridges ====
-- L13 port of pm 9903 -> 10247
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10247 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10247 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10245) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10245).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10247 10245 1313
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10245], outs := [10247, 10249, 10251], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 10245 10247 10249 10251 [8])
    rfl


-- L13 port of pm 9904 -> 10248
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10248 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10248 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10246) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10246).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10248 10246 1317
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10246], outs := [10248, 10250, 10252], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 10246 10248 10250 10252 [8])
    rfl


-- L13 port of pm 9913 -> 10257
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10257 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10257 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16242)
        (denoteGraph_ringAttn pm_goal_3 initPM 10247)
        (denoteGraph_ringAttn pm_goal_3 initPM 10249)
        [initPM 10253, initPM 10254] [initPM 10255, initPM 10256]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10257 16242 10247 10249 10253 10254 10255 10256 1321
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16242, 10247, 10249, 10253, 10254, 10255, 10256], outs := [10257], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16242 10247 10249 10253 10254 10255 10256 10257 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10253 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10254 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10255 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10256 (by decide) (by decide))


-- L13 port of pm 9914 -> 10258
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10258 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10258 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16265)
        (denoteGraph_ringAttn pm_goal_3 initPM 10248)
        (denoteGraph_ringAttn pm_goal_3 initPM 10250)
        [initPM 10253, initPM 10254] [initPM 10255, initPM 10256]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10258 16265 10248 10250 10253 10254 10255 10256 1324
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16265, 10248, 10250, 10253, 10254, 10255, 10256], outs := [10258], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16265 10248 10250 10253 10254 10255 10256 10258 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10253 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10254 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10255 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10256 (by decide) (by decide))


-- L13 port of pm 9915 -> 10259
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10259 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10259 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16246) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10259 16246 1298
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16246], outs := [10259], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16246 10259 [2048, 1024])
    rfl


-- L13 port of pm 9916 -> 10260
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10260 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10260 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16269) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10260 16269 1302
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16269], outs := [10260], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16269 10260 [2048, 1024])
    rfl


-- L13 port of pm 9919 -> 10263
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10263 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10263 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10259) (initPM 5514) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10263 10259 5514 1306
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10259, 5514], outs := [10263] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10259 5514 10263)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5514 (by decide) (by decide))


-- L13 port of pm 9920 -> 10264
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10264 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10264 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10260) (initPM 5514) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10264 10260 5514 1310
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10260, 5514], outs := [10264] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10260 5514 10264)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5514 (by decide) (by decide))


-- L13 port of pm 9925 -> 10269
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10269 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10269 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10263) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10269 10263 1314
    ({ rank := 0, op := "OpName.FW_view", ins := [10263], outs := [10269], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 10263 10269)
    rfl


-- L13 port of pm 9926 -> 10270
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10270 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10270 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10264) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10270 10264 1318
    ({ rank := 1, op := "OpName.FW_view", ins := [10264], outs := [10270], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 10264 10270)
    rfl


-- L13 port of pm 9927 -> 10271
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10271 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10271 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10269) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10271 10269 1322
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [10269], outs := [10271] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 10269 10271])
    rfl


-- L13 port of pm 9928 -> 10272
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10272 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10272 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10270) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10272 10270 1325
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [10270], outs := [10272] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 10270 10272])
    rfl


-- L13 port of pm 9929 -> 10273
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10273 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10273 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16250) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10273 16250 1299
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16250], outs := [10273], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16250 10273 [2048, 1024])
    rfl


-- L13 port of pm 9930 -> 10274
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10274 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10274 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16273) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10274 16273 1303
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16273], outs := [10274], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16273 10274 [2048, 1024])
    rfl


-- L13 port of pm 9933 -> 10277
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10277 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10277 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10273) (initPM 5519) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10277 10273 5519 1307
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10273, 5519], outs := [10277] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10273 5519 10277)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5519 (by decide) (by decide))


-- L13 port of pm 9934 -> 10278
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10278 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10278 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10274) (initPM 5519) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10278 10274 5519 1311
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10274, 5519], outs := [10278] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10274 5519 10278)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5519 (by decide) (by decide))


-- L13 port of pm 9943 -> 10287
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10287 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10287 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10277) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10287 10277 1315
    ({ rank := 0, op := "OpName.FW_view", ins := [10277], outs := [10287], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10277 10287)
    rfl


-- L13 port of pm 9944 -> 10288
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10288 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10288 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10278) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10288 10278 1319
    ({ rank := 1, op := "OpName.FW_view", ins := [10278], outs := [10288], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10278 10288)
    rfl


-- L13 port of pm 9947 -> 10291
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10291 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10291 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16254) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10291 16254 1300
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16254], outs := [10291], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16254 10291 [2048, 1024])
    rfl


-- L13 port of pm 9948 -> 10292
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10292 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10292 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16277) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10292 16277 1304
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16277], outs := [10292], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16277 10292 [2048, 1024])
    rfl


-- L13 port of pm 9951 -> 10295
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10295 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10295 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10291) (initPM 5523) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10295 10291 5523 1308
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10291, 5523], outs := [10295] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10291 5523 10295)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5523 (by decide) (by decide))


-- L13 port of pm 9952 -> 10296
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10296 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10296 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10292) (initPM 5523) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10296 10292 5523 1312
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10292, 5523], outs := [10296] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10292 5523 10296)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5523 (by decide) (by decide))


-- L13 port of pm 9961 -> 10305
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10305 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10305 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10295) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10305 10295 1316
    ({ rank := 0, op := "OpName.FW_view", ins := [10295], outs := [10305], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10295 10305)
    rfl


-- L13 port of pm 9962 -> 10306
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10306 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10306 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10296) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10306 10296 1320
    ({ rank := 1, op := "OpName.FW_view", ins := [10296], outs := [10306], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10296 10306)
    rfl


-- L13 port of pm 9965 -> 10309
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10309 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10309 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10287) (denoteGraph_ringAttn pm_goal_3 initPM 10305) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10309 10287 10305 1323
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [10287, 10305], outs := [10309] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 10287 10305 10309])
    rfl rfl


-- L13 port of pm 9966 -> 10310
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10310 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10310 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10288) (denoteGraph_ringAttn pm_goal_3 initPM 10306) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10310 10288 10306 1326
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [10288, 10306], outs := [10310] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 10288 10306 10310])
    rfl rfl


-- L13 port of pm 9967 -> 10311
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10311 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10311 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10309) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10311 10309 1327
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10309], outs := [10311], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10309 10311 [2048, 512])
    rfl


-- L13 port of pm 9968 -> 10312
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10312 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10312 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10310) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10312 10310 1328
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10310], outs := [10312], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10310 10312 [2048, 512])
    rfl


-- L13 port of pm 9973 -> 10317
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10317 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10317 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10311) (initPM 5528) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10317 10311 5528 1329
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10311, 5528], outs := [10317] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10311 5528 10317)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5528 (by decide) (by decide))


-- L13 port of pm 9974 -> 10318
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10318 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10318 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10312) (initPM 5528) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10318 10312 5528 1330
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10312, 5528], outs := [10318] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10312 5528 10318)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5528 (by decide) (by decide))


-- L13 port of pm 9983 -> 10327
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10327 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10327 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10317) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10327 10317 1331
    ({ rank := 0, op := "OpName.FW_view", ins := [10317], outs := [10327], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10317 10327)
    rfl


-- L13 port of pm 9984 -> 10328
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10328 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10328 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10318) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10328 10318 1332
    ({ rank := 1, op := "OpName.FW_view", ins := [10318], outs := [10328], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10318 10328)
    rfl


-- L13 port of pm 9987 -> 10331
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10331 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10331 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10271) (denoteGraph_ringAttn pm_goal_3 initPM 10327) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10331 10271 10327 1333
    ({ rank := 0, op := "OpName.FW_mul", ins := [10271, 10327], outs := [10331] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 10271 10327 10331])
    rfl rfl


-- L13 port of pm 9988 -> 10332
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10332 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10332 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10272) (denoteGraph_ringAttn pm_goal_3 initPM 10328) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10332 10272 10328 1334
    ({ rank := 1, op := "OpName.FW_mul", ins := [10272, 10328], outs := [10332] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 10272 10328 10332])
    rfl rfl


-- L13 port of pm 9991 -> 10335
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10335 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10335 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10257) (denoteGraph_ringAttn pm_goal_3 initPM 10331) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10335 10257 10331 1335
    ({ rank := 0, op := "OpName.FW_add", ins := [10257, 10331], outs := [10335] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 10257 10331 10335)
    rfl rfl


-- L13 port of pm 9992 -> 10336
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10336 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10336 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10258) (denoteGraph_ringAttn pm_goal_3 initPM 10332) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10336 10258 10332 1336
    ({ rank := 1, op := "OpName.FW_add", ins := [10258, 10332], outs := [10336] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 10258 10332 10336)
    rfl rfl


-- L13 port of pm 9997 -> 10341
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10341 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10341 =
      denoteGraph_ringAttn pm_goal_3 initPM 10335 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10341 10335 1337
    ({ rank := 0, op := "OpName.FW_float", ins := [10335], outs := [10341] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10335 10341 [])
    rfl


-- L13 port of pm 9998 -> 10342
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10342 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10342 =
      denoteGraph_ringAttn pm_goal_3 initPM 10336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10342 10336 1338
    ({ rank := 1, op := "OpName.FW_float", ins := [10336], outs := [10342] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10336 10342 [])
    rfl


-- L13 port of pm 10173 -> 10345
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10345 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10345 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16223) (denoteGraph_ringAttn pm_goal_3 initPM 10341) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10345 16223 10341 1339
    ({ rank := 0, op := "OpName.FW_add", ins := [16223, 10341], outs := [10345] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16223 10341 10345)
    rfl rfl


-- L13 port of pm 10174 -> 10346
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10346 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10346 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16231) (denoteGraph_ringAttn pm_goal_3 initPM 10342) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10346 16231 10342 1340
    ({ rank := 1, op := "OpName.FW_add", ins := [16231, 10342], outs := [10346] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16231 10342 10346)
    rfl rfl


-- L13 port of pm 16067 -> 16223
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16223 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16223 =
      denoteGraph_ringAttn pm_goal_3 initPM 10233 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16223 10233 1291
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10233], outs := [16219, 16223], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 10233 16219 16223 (by decide))
    rfl


-- L13 port of pm 16075 -> 16231
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16231 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16231 =
      denoteGraph_ringAttn pm_goal_3 initPM 10234 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16231 10234 1292
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10234], outs := [16227, 16231], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 10234 16227 16231 (by decide))
    rfl


-- L13 port of pm 16086 -> 16242
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16242 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16242 =
      denoteGraph_ringAttn pm_goal_3 initPM 10237 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16242 10237 1295
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 10237 16238 16242 16246 16250 16254 (by decide))
    rfl


-- L13 port of pm 16090 -> 16246
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16246 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16246 =
      denoteGraph_ringAttn pm_goal_3 initPM 10237 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16246 10237 1295
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 10237 16238 16242 16246 16250 16254 (by decide) (by decide))
    rfl


-- L13 port of pm 16094 -> 16250
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16250 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16250 =
      denoteGraph_ringAttn pm_goal_3 initPM 10237 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16250 10237 1295
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 10237 16238 16242 16246 16250 16254 (by decide) (by decide) (by decide))
    rfl


-- L13 port of pm 16098 -> 16254
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16254 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16254 =
      denoteGraph_ringAttn pm_goal_3 initPM 10237 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16254 10237 1295
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 10237 16238 16242 16246 16250 16254 (by decide) (by decide) (by decide) (by decide))
    rfl


-- L13 port of pm 16109 -> 16265
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16265 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16265 =
      denoteGraph_ringAttn pm_goal_3 initPM 10238 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16265 10238 1296
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 10238 16261 16265 16269 16273 16277 (by decide))
    rfl


-- L13 port of pm 16113 -> 16269
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16269 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16269 =
      denoteGraph_ringAttn pm_goal_3 initPM 10238 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16269 10238 1296
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 10238 16261 16265 16269 16273 16277 (by decide) (by decide))
    rfl


-- L13 port of pm 16117 -> 16273
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16273 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16273 =
      denoteGraph_ringAttn pm_goal_3 initPM 10238 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16273 10238 1296
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 10238 16261 16265 16269 16273 16277 (by decide) (by decide) (by decide))
    rfl


-- L13 port of pm 16121 -> 16277
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16277 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16277 =
      denoteGraph_ringAttn pm_goal_3 initPM 10238 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16277 10238 1296
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 10238 16261 16265 16269 16273 16277 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ==== L14 SM bridges ====
-- L13 port of sm 5409 -> 5507
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5507 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5507 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5506) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5506).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5507 5506 627
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5506], outs := [5507, 5508, 5509], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5506 5507 5508 5509 [8])
    rfl


-- L13 port of sm 5414 -> 5512
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5512 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5512 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8279)
        (denoteGraph_ringAttn sm_goal_3 initSM 5507)
        (denoteGraph_ringAttn sm_goal_3 initSM 5508)
        (initSM 5510) (initSM 5511) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5512 8279 5507 5508 5510 5511 631
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8279, 5507, 5508, 5510, 5511], outs := [5512], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8279 5507 5508 5510 5511 5512 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5510 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5511 (by decide) (by decide))


-- L13 port of sm 5415 -> 5513
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5513 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5513 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8283) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5513 8283 620
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8283], outs := [5513], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8283 5513 [4096, 1024])
    rfl


-- L13 port of sm 5417 -> 5515
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5515 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5515 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5513) (initSM 5514) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5515 5513 5514 624
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5513, 5514], outs := [5515] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5513 5514 5515)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5514 (by decide) (by decide))


-- L13 port of sm 5418 -> 5516
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5516 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5516 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5515) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5516 5515 628
    ({ rank := 0, op := "OpName.FW_view", ins := [5515], outs := [5516], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5515 5516)
    rfl


-- L13 port of sm 5419 -> 5517
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5517 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5517 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5516) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5517 5516 632
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5516], outs := [5517] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5516 5517])
    rfl


-- L13 port of sm 5420 -> 5518
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5518 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5518 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8287) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5518 8287 621
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [5518], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8287 5518 [4096, 1024])
    rfl


-- L13 port of sm 5422 -> 5520
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5520 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5520 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5518) (initSM 5519) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5520 5518 5519 625
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5518, 5519], outs := [5520] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5518 5519 5520)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5519 (by decide) (by decide))


-- L13 port of sm 5423 -> 5521
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5521 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5521 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5520) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5521 5520 629
    ({ rank := 0, op := "OpName.FW_view", ins := [5520], outs := [5521], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5520 5521)
    rfl


-- L13 port of sm 5424 -> 5522
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5522 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5522 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8291) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5522 8291 622
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8291], outs := [5522], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8291 5522 [4096, 1024])
    rfl


-- L13 port of sm 5426 -> 5524
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5524 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5524 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5522) (initSM 5523) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5524 5522 5523 626
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5522, 5523], outs := [5524] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5522 5523 5524)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5523 (by decide) (by decide))


-- L13 port of sm 5427 -> 5525
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5525 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5525 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5524) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5525 5524 630
    ({ rank := 0, op := "OpName.FW_view", ins := [5524], outs := [5525], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5524 5525)
    rfl


-- L13 port of sm 5428 -> 5526
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5526 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5526 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5521) (denoteGraph_ringAttn sm_goal_3 initSM 5525) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5526 5521 5525 633
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5521, 5525], outs := [5526] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5521 5525 5526])
    rfl rfl


-- L13 port of sm 5429 -> 5527
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5527 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5527 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5526) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5527 5526 634
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5526], outs := [5527], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5526 5527 [4096, 512])
    rfl


-- L13 port of sm 5431 -> 5529
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5529 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5529 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5527) (initSM 5528) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5529 5527 5528 635
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5527, 5528], outs := [5529] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5527 5528 5529)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5528 (by decide) (by decide))


-- L13 port of sm 5432 -> 5530
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5530 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5530 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5529) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5530 5529 636
    ({ rank := 0, op := "OpName.FW_view", ins := [5529], outs := [5530], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5529 5530)
    rfl


-- L13 port of sm 5433 -> 5531
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5531 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5531 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5517) (denoteGraph_ringAttn sm_goal_3 initSM 5530) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5531 5517 5530 637
    ({ rank := 0, op := "OpName.FW_mul", ins := [5517, 5530], outs := [5531] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5517 5530 5531])
    rfl rfl


-- L13 port of sm 5434 -> 5532
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5532 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5532 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5512) (denoteGraph_ringAttn sm_goal_3 initSM 5531) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5532 5512 5531 638
    ({ rank := 0, op := "OpName.FW_add", ins := [5512, 5531], outs := [5532] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5512 5531 5532)
    rfl rfl


-- L13 port of sm 5435 -> 5533
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5533 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5533 =
      denoteGraph_ringAttn sm_goal_3 initSM 5532 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5533 5532 639
    ({ rank := 0, op := "OpName.FW_float", ins := [5532], outs := [5533] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5532 5533 [])
    rfl


-- L13 port of sm 5485 -> 5534
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5534 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8268) (denoteGraph_ringAttn sm_goal_3 initSM 5533) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5534 8268 5533 640
    ({ rank := 0, op := "OpName.FW_add", ins := [8268, 5533], outs := [5534] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8268 5533 5534)
    rfl rfl


-- L13 port of sm 8190 -> 8268
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8268 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8268 =
      denoteGraph_ringAttn sm_goal_3 initSM 5501 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8268 5501 616
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5501], outs := [8264, 8268], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5501 8264 8268 (by decide))
    rfl


-- L13 port of sm 8201 -> 8279
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8279 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8279 =
      denoteGraph_ringAttn sm_goal_3 initSM 5503 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8279 5503 618
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5503 8275 8279 8283 8287 8291 (by decide))
    rfl


-- L13 port of sm 8205 -> 8283
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8283 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8283 =
      denoteGraph_ringAttn sm_goal_3 initSM 5503 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8283 5503 618
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5503 8275 8279 8283 8287 8291 (by decide) (by decide))
    rfl


-- L13 port of sm 8209 -> 8287
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8287 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8287 =
      denoteGraph_ringAttn sm_goal_3 initSM 5503 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8287 5503 618
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5503 8275 8279 8283 8287 8291 (by decide) (by decide) (by decide))
    rfl


-- L13 port of sm 8213 -> 8291
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8291 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8291 =
      denoteGraph_ringAttn sm_goal_3 initSM 5503 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8291 5503 618
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5503 8275 8279 8283 8287 8291 (by decide) (by decide) (by decide) (by decide))
    rfl






-- ==== L14 MoE commute lemmas + boundary carry + shape helpers ====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5501 : denoteGraph_ringAttn sm_goal_3 initSM 5501 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10233,
         denoteGraph_ringAttn pm_goal_3 initPM 10234])
    (h10233 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024])
    (h10234 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5512 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10257,
         denoteGraph_ringAttn pm_goal_3 initPM 10258] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5502 : initSM 5502 = initPM 5502 := hb initGoal_5502 (by decide) rfl
  have hw5505sh : (initPM 5505).shape = [64, 1024] := by
    have hgh := hII initGoal_5505 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5505] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5510 : initSM 5510 = allGatherPrimDimN 0 2 0 [initPM 10253, initPM 10254] := by
    have hg := hII initGoal_5510 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5510, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10253) (initPM 10254) []
        (by rw [h_ss_pm 10253 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5511 : initSM 5511 = allGatherPrimDimN 0 2 0 [initPM 10255, initPM 10256] := by
    have hg := hII initGoal_5511 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5511, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10255) (initPM 10256) []
        (by rw [h_ss_pm 10255 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L15_commute initSM initPM hInit hcarry5501 h10233 h10234
  have hrouter := sm_pm_router_commute_L15 initSM initPM hInit hcarry5501 h10233 h10234
  -- PM rms output shapes [2048, 1024]
  have h10237sh : (denoteGraph_ringAttn pm_goal_3 initPM 10237).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10237, rms_sh]; exact h10233
  have h10238sh : (denoteGraph_ringAttn pm_goal_3 initPM 10238).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10238, rms_sh]; exact h10234
  -- PM nl output shapes [2048, 64]
  have h10245sh : (denoteGraph_ringAttn pm_goal_3 initPM 10245).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10245, denote_pm_goal_3_10239, denote_pm_goal_3_10237]
    exact nl_sh 2048 1024 64 _ (initPM 5505) (by rw [rms_sh]; exact h10233) hw5505sh
  have h10246sh : (denoteGraph_ringAttn pm_goal_3 initPM 10246).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10246, denote_pm_goal_3_10240, denote_pm_goal_3_10238]
    exact nl_sh 2048 1024 64 _ (initPM 5505) (by rw [rms_sh]; exact h10234) hw5505sh
  have hSM5506sh : (denoteGraph_ringAttn sm_goal_3 initSM 5506).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10245sh
  -- MoE weight shapes
  have hw10253 : (initPM 10253).shape = [32,1024,1024] := h_ss_pm 10253 [32,1024,1024] (by decide)
  have hw10254 : (initPM 10254).shape = [32,1024,1024] := h_ss_pm 10254 [32,1024,1024] (by decide)
  have hw10255 : (initPM 10255).shape = [32,1024,512] := h_ss_pm 10255 [32,1024,512] (by decide)
  have hw10256 : (initPM 10256).shape = [32,1024,512] := h_ss_pm 10256 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10247canon : denoteGraph_ringAttn pm_goal_3 initPM 10247
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10245) 8 64).fst := by
    rw [denote_pm_goal_3_10247,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10245).shape.reverse.head?).getD 1 = 64 from by rw [h10245sh]; rfl]
  have h10248canon : denoteGraph_ringAttn pm_goal_3 initPM 10248
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10246) 8 64).fst := by
    rw [denote_pm_goal_3_10248,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10246).shape.reverse.head?).getD 1 = 64 from by rw [h10246sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10247sh : (denoteGraph_ringAttn pm_goal_3 initPM 10247).shape = [2048, 64] := by
    rw [h10247canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10245sh]; rfl)
  have h10248sh : (denoteGraph_ringAttn pm_goal_3 initPM 10248).shape = [2048, 64] := by
    rw [h10248canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10246sh]; rfl)
  have h10249canon : denoteGraph_ringAttn pm_goal_3 initPM 10249
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10245) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10249,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10245).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10245sh]; rfl]
  have h10250canon : denoteGraph_ringAttn pm_goal_3 initPM 10250
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10246) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10250,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10246).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10246sh]; rfl]
  have h10249sh : (denoteGraph_ringAttn pm_goal_3 initPM 10249).shape = [2048, 64] := by
    rw [h10249canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10245sh
  have h10250sh : (denoteGraph_ringAttn pm_goal_3 initPM 10250).shape = [2048, 64] := by
    rw [h10250canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10246sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 10237) (denoteGraph_ringAttn pm_goal_3 initPM 10238)
    (denoteGraph_ringAttn pm_goal_3 initPM 10247) (denoteGraph_ringAttn pm_goal_3 initPM 10248)
    (denoteGraph_ringAttn pm_goal_3 initPM 10249) (denoteGraph_ringAttn pm_goal_3 initPM 10250)
    (initPM 10253) (initPM 10254) (initPM 10255) (initPM 10256)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10237sh h10238sh h10247sh h10248sh h10249sh h10250sh hw10253 hw10254 hw10255 hw10256
  -- Rewrite RHS via denote unfolds + key
  rw [denote_pm_goal_3_10257, denote_pm_goal_3_10258, denote_pm_goal_3_16242, denote_pm_goal_3_16265,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [denote_sm_goal_3_5512, denote_sm_goal_3_8279, denote_sm_goal_3_5503, denote_sm_goal_3_5507]
  rw [hrouter, h5510, h5511]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5506).shape.reverse.head?).getD 1 = 64 from by rw [hSM5506sh]; rfl]
  rw [hw5502, hcarry5501, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5502) 2048 1024 (by omega) (by omega) h10233 h10234]
  rw [← denote_pm_goal_3_10237, ← denote_pm_goal_3_10238]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10245sh h10246sh]
  rw [← h10247canon, ← h10248canon]
  unfold fw_all2all_moe_gmm_full
  rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L15_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5501 : denoteGraph_ringAttn sm_goal_3 initSM 5501 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10233,
         denoteGraph_ringAttn pm_goal_3 initPM 10234])
    (h10233 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024])
    (h10234 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5531
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10331,
           denoteGraph_ringAttn pm_goal_3 initPM 10332] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5502 : initSM 5502 = initPM 5502 := hb initGoal_5502 (by decide) rfl
  have hw5514 : initSM 5514 = initPM 5514 := hb initGoal_5514 (by decide) rfl
  have hw5519 : initSM 5519 = initPM 5519 := hb initGoal_5519 (by decide) rfl
  have hw5523 : initSM 5523 = initPM 5523 := hb initGoal_5523 (by decide) rfl
  have hw5528 : initSM 5528 = initPM 5528 := hb initGoal_5528 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5501) (initSM 5502)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10237,
           denoteGraph_ringAttn pm_goal_3 initPM 10238] := by
    rw [hcarry5501, hw5502,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5502) 2048 1024 (by omega) (by omega) h10233 h10234,
        ← denote_pm_goal_3_10237, ← denote_pm_goal_3_10238]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 10237 / 10238
  rw [denote_pm_goal_3_10331, denote_pm_goal_3_10332,
      denote_pm_goal_3_10271, denote_pm_goal_3_10269, denote_pm_goal_3_10263, denote_pm_goal_3_10259, denote_pm_goal_3_16246,
      denote_pm_goal_3_10327, denote_pm_goal_3_10317, denote_pm_goal_3_10311, denote_pm_goal_3_10309,
      denote_pm_goal_3_10287, denote_pm_goal_3_10277, denote_pm_goal_3_10273, denote_pm_goal_3_16250,
      denote_pm_goal_3_10305, denote_pm_goal_3_10295, denote_pm_goal_3_10291, denote_pm_goal_3_16254,
      denote_pm_goal_3_10272, denote_pm_goal_3_10270, denote_pm_goal_3_10264, denote_pm_goal_3_10260, denote_pm_goal_3_16269,
      denote_pm_goal_3_10328, denote_pm_goal_3_10318, denote_pm_goal_3_10312, denote_pm_goal_3_10310,
      denote_pm_goal_3_10288, denote_pm_goal_3_10278, denote_pm_goal_3_10274, denote_pm_goal_3_16273,
      denote_pm_goal_3_10306, denote_pm_goal_3_10296, denote_pm_goal_3_10292, denote_pm_goal_3_16277]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5503
  rw [denote_sm_goal_3_5531, denote_sm_goal_3_5517, denote_sm_goal_3_5516, denote_sm_goal_3_5515,
      denote_sm_goal_3_5513, denote_sm_goal_3_8283,
      denote_sm_goal_3_5530, denote_sm_goal_3_5529, denote_sm_goal_3_5527, denote_sm_goal_3_5526,
      denote_sm_goal_3_5521, denote_sm_goal_3_5520, denote_sm_goal_3_5518, denote_sm_goal_3_8287,
      denote_sm_goal_3_5525, denote_sm_goal_3_5524, denote_sm_goal_3_5522, denote_sm_goal_3_8291,
      denote_sm_goal_3_5503]
  rw [hRMS, hw5514, hw5519, hw5523, hw5528]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 10237 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 10238 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10237, rms_sh]; exact h10233
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10238, rms_sh]; exact h10234
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5514).shape = [1, 1024] := h_ss_pm 5514 [1, 1024] (by decide)
  have hw29 : (initPM 5519).shape = [512, 1024] := h_ss_pm 5519 [512, 1024] (by decide)
  have hw33 : (initPM 5523).shape = [512, 1024] := h_ss_pm 5523 [512, 1024] (by decide)
  have hw38 : (initPM 5528).shape = [1024, 512] := h_ss_pm 5528 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5514) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5519) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5523) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5514)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5514)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5519)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5519)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5523)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5523)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5514), fw_linear (fw_view [2048, 1024] B) (initPM 5514)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5514)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5514))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5519), fw_linear (fw_view [2048, 1024] B) (initPM 5519)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5523), fw_linear (fw_view [2048, 1024] B) (initPM 5523)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5514)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5514)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5528) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523))))) (initPM 5528)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))))) (initPM 5528)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523))))) (initPM 5528), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))))) (initPM 5528)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523))))) (initPM 5528)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))))) (initPM 5528))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5514))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5514))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5523))))) (initPM 5528)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5519))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5523))))) (initPM 5528)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]



set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10345_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] := by
  have h10173 := pm_goal_3_10173_shape initPM hPM
  have h10229 : (denoteGraph_ringAttn pm_goal_3 initPM 10229).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10229, denote_pm_goal_3_10225]; rfl
  have h10233 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10233]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16207]; exact h10173) h10229
  have h10237sh : (denoteGraph_ringAttn pm_goal_3 initPM 10237).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10237, rms_sh]; exact h10233
  have h10257sh : (denoteGraph_ringAttn pm_goal_3 initPM 10257).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10257, denote_pm_goal_3_16242]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10237sh]; rfl) (by rw [h10237sh]; rfl)
  have h10271sh : (denoteGraph_ringAttn pm_goal_3 initPM 10271).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10271, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10269]
    exact fw_view_shape_eq _ _
  have h10327sh : (denoteGraph_ringAttn pm_goal_3 initPM 10327).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10327]; exact fw_view_shape_eq _ _
  have h10331sh : (denoteGraph_ringAttn pm_goal_3 initPM 10331).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10331, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10271sh h10327sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10257) (denoteGraph_ringAttn pm_goal_3 initPM 10331)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10257sh h10331sh
  have h16223sh : (denoteGraph_ringAttn pm_goal_3 initPM 16223).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16223]; exact h10233
  have h10341sh : (denoteGraph_ringAttn pm_goal_3 initPM 10341).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10341, denote_pm_goal_3_10335]; exact hinnerA
  rw [denote_pm_goal_3_10345]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16223sh h10341sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10346_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] := by
  have h10174 := pm_goal_3_10174_shape initPM hPM
  have h10230 : (denoteGraph_ringAttn pm_goal_3 initPM 10230).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10230, denote_pm_goal_3_10226]; rfl
  have h10234 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10234]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16215]; exact h10174) h10230
  have h10238sh : (denoteGraph_ringAttn pm_goal_3 initPM 10238).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10238, rms_sh]; exact h10234
  have h10258sh : (denoteGraph_ringAttn pm_goal_3 initPM 10258).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10258, denote_pm_goal_3_16265]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10238sh]; rfl) (by rw [h10238sh]; rfl)
  have h10272sh : (denoteGraph_ringAttn pm_goal_3 initPM 10272).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10272, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10270]
    exact fw_view_shape_eq _ _
  have h10328sh : (denoteGraph_ringAttn pm_goal_3 initPM 10328).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10328]; exact fw_view_shape_eq _ _
  have h10332sh : (denoteGraph_ringAttn pm_goal_3 initPM 10332).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10332, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10272sh h10328sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10258) (denoteGraph_ringAttn pm_goal_3 initPM 10332)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10258sh h10332sh
  have h16231sh : (denoteGraph_ringAttn pm_goal_3 initPM 16231).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16231]; exact h10234
  have h10342sh : (denoteGraph_ringAttn pm_goal_3 initPM 10342).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10342, denote_pm_goal_3_10336]; exact hinnerB
  rw [denote_pm_goal_3_10346]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16231sh h10342sh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sm_pm_carry_5534_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hp5346 : initPM 5346 = cu_pin_value)
    (hp5395 : initPM 5395 = cu_pin_value)
    (hp5444 : initPM 5444 = cu_pin_value)
    (hp5493 : initPM 5493 = cu_pin_value) :
    denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346] := by
  have h_bound := cu_bound_of_value_pin (initPM 5493) hp5493
  have hcarry5485 := sm_pm_carry_5485_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444
  have h10173 := pm_goal_3_10173_shape initPM hPM
  have h10174 := pm_goal_3_10174_shape initPM hPM
  have hattn := sm_pm_attention_L15_commute' initSM initPM hSM hPM hInit hcarry5485 h10173 h10174 h_bound
  have hw5488 : (initPM 5488).shape = [16, 64, 1024] := hPM 5488 [16, 64, 1024] (by decide)
  have hw5497 : (initPM 5497).shape = [1024, 1024] := hPM 5497 [1024, 1024] (by decide)
  have h10177 : (denoteGraph_ringAttn pm_goal_3 initPM 10177).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10177, rms_sh]; exact h10173
  have h10178 : (denoteGraph_ringAttn pm_goal_3 initPM 10178).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10178, rms_sh]; exact h10174
  have h10179d : (denoteGraph_ringAttn pm_goal_3 initPM 10179).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10179]; exact ph_lin_shape_gen _ _ 2048 16 h10177 hw5488
  have h10180d : (denoteGraph_ringAttn pm_goal_3 initPM 10180).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10180]; exact ph_lin_shape_gen _ _ 2048 16 h10178 hw5488
  -- folded-store ↔ denote bridges at the two attention Q tids
  have b1277_10179 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
      = denoteGraph_ringAttn pm_goal_3 initPM 10179 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1277 (by decide) (by decide)).symm
  have b1277_10180 : (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
      = denoteGraph_ringAttn pm_goal_3 initPM 10180 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1277 (by decide) (by decide)).symm
  have b1278_10179 : (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10179
      = denoteGraph_ringAttn pm_goal_3 initPM 10179 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10179 1278 (by decide) (by decide)).symm
  have b1278_10180 : (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10180
      = denoteGraph_ringAttn pm_goal_3 initPM 10180 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10180 1278 (by decide) (by decide)).symm
  -- PM attention output shapes [2048,16,64] (chunk of the full [4096,16,64])
  have h10203 : (denoteGraph_ringAttn pm_goal_3 initPM 10203).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L15_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_15 nR0_15 nR1_15 0 buddy_r0_15 (by decide)]
    have e0 : nR0_15.ins.getD 0 0 = 10179 := by decide
    have e1 : nR1_15.ins.getD 0 0 = 10180 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_15.ins.getD 0 0),
         (pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_15.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1277_10179, b1277_10180]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10179d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10204 : (denoteGraph_ringAttn pm_goal_3 initPM 10204).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L15_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_15 nR0_15 nR1_15 1 buddy_r1_15 (by decide)]
    have e0 : nR0_15.ins.getD 0 0 = 10179 := by decide
    have e1 : nR1_15.ins.getD 0 0 = 10180 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_15.ins.getD 0 0),
         (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_15.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1278_10179, b1278_10180]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10179d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl

  have hreshape := sm_pm_reshape_float_5500_commute initSM initPM hInit hattn h10203 h10204 hw5497
  have h10229 : (denoteGraph_ringAttn pm_goal_3 initPM 10229).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10229, denote_pm_goal_3_10225]; rfl
  have h10230 : (denoteGraph_ringAttn pm_goal_3 initPM 10230).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10230, denote_pm_goal_3_10226]; rfl
  have hshuffle := sm_pm_carryaux_L15_commute initSM initPM hcarry5485
  have h16207 : (denoteGraph_ringAttn pm_goal_3 initPM 16207).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16207]; exact h10173
  have h16215 : (denoteGraph_ringAttn pm_goal_3 initPM 16215).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_16215]; exact h10174
  have hcarry5501 := sm_pm_carry_5501_commute initSM initPM hshuffle hreshape h16207 h16215 h10229 h10230
  have h10233 : (denoteGraph_ringAttn pm_goal_3 initPM 10233).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10233]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16207]; exact h10173) h10229
  have h10234 : (denoteGraph_ringAttn pm_goal_3 initPM 10234).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10234]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16215]; exact h10174) h10230
  have hgmm := sm_pm_moe_gmm_L15_commute initSM initPM hInit hPM hcarry5501 h10233 h10234
  have hgate := sm_pm_gate_mul_L15_commute initSM initPM hInit hPM hcarry5501 h10233 h10234
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h10237sh : (denoteGraph_ringAttn pm_goal_3 initPM 10237).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10237, rms_sh]; exact h10233
  have h10238sh : (denoteGraph_ringAttn pm_goal_3 initPM 10238).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10238, rms_sh]; exact h10234
  have h10257sh : (denoteGraph_ringAttn pm_goal_3 initPM 10257).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10257, denote_pm_goal_3_16242]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10237sh]; rfl) (by rw [h10237sh]; rfl)
  have h10258sh : (denoteGraph_ringAttn pm_goal_3 initPM 10258).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10258, denote_pm_goal_3_16265]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10238sh]; rfl) (by rw [h10238sh]; rfl)
  have h10271sh : (denoteGraph_ringAttn pm_goal_3 initPM 10271).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10271, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10269]
    exact fw_view_shape_eq _ _
  have h10327sh : (denoteGraph_ringAttn pm_goal_3 initPM 10327).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10327]; exact fw_view_shape_eq _ _
  have h10331sh : (denoteGraph_ringAttn pm_goal_3 initPM 10331).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10331, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10271sh h10327sh]; rfl
  have h10272sh : (denoteGraph_ringAttn pm_goal_3 initPM 10272).shape = [2048, 1] := by
    rw [denote_pm_goal_3_10272, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_10270]
    exact fw_view_shape_eq _ _
  have h10328sh : (denoteGraph_ringAttn pm_goal_3 initPM 10328).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10328]; exact fw_view_shape_eq _ _
  have h10332sh : (denoteGraph_ringAttn pm_goal_3 initPM 10332).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10332, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10272sh h10328sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10257) (denoteGraph_ringAttn pm_goal_3 initPM 10331)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10257sh h10331sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10258) (denoteGraph_ringAttn pm_goal_3 initPM 10332)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10258sh h10332sh
  -- === assemble ===
  rw [denote_pm_goal_3_10345, denote_pm_goal_3_16223, denote_pm_goal_3_10341, denote_pm_goal_3_10335,
      denote_pm_goal_3_10346, denote_pm_goal_3_16231, denote_pm_goal_3_10342, denote_pm_goal_3_10336]
  rw [denote_sm_goal_3_5534, denote_sm_goal_3_8268, denote_sm_goal_3_5533, denote_sm_goal_3_5532]
  rw [hcarry5501, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10257) (denoteGraph_ringAttn pm_goal_3 initPM 10258)
        (denoteGraph_ringAttn pm_goal_3 initPM 10331) (denoteGraph_ringAttn pm_goal_3 initPM 10332)
        h10257sh h10258sh h10331sh h10332sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10233) (denoteGraph_ringAttn pm_goal_3 initPM 10234)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10257) (denoteGraph_ringAttn pm_goal_3 initPM 10331))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10258) (denoteGraph_ringAttn pm_goal_3 initPM 10332))
        h10233 h10234 hinnerA hinnerB]



end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L15_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L15_commute'
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L15_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5534_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10345_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10346_shape
