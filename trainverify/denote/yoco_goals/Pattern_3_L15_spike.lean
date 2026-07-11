/-
  Pattern_3_L15_spike.lean — L15 zigzag-band proof (generic layer).
-/
import denote.yoco_goals.Pattern_3_L12_spike
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

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L15_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L15_commute'
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L15_hbound_witness
