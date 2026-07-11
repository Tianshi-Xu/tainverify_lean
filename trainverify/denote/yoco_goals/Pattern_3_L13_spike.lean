/-
  Pattern_3_L13_spike.lean — L13 zigzag-band proof.

  Structurally analogous to Pattern_3_L12_spike (imported for its op-parametric
  zigzag reconstruction primitives and the shared K/V-projection denote chain).

  L13 is a *normal* CP layer: unlike L12 (a shuffle-boundary layer) its
  pre-attention path is just `carry → rms_norm → per_head_linear`, with NO
  `fw_maybe_shuffle` machinery.  The post-attention router head is a clean
  +49 (SM) / +172 (PM) tid-shift of L12's.

  L13 input carry is SM 5387 (= L12 block output, PM r0/r1 = 9829/9830); it is
  not proven on `main`, so it is threaded as a statement-level hypothesis with a
  vacuity witness (AGENTS.md #29).
-/
import denote.yoco_goals.Pattern_3_L12_spike

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

/-! ## L13 attention NodeDecls -/

def nSM_13 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5391, 5392, 5393, 5394, 5395], outs := [5396],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_13 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9835, 5392, 5393, 5394, 5395], outs := [9859],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_13 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9836, 5392, 5393, 5394, 5395], outs := [9860],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_13 : ringAttnBuddies sm_goal_3 nSM_13 = [nSM_13] := by
  show (List.filter (fun m => decide (m.op = nSM_13.op) && decide (m.params = nSM_13.params) &&
      decide (m.ins.getD 3 0 = nSM_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_13.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_13]
  rw [show (List.filter (fun m => decide (m.op = nSM_13.op) && decide (m.params = nSM_13.params) &&
      decide (m.ins.getD 3 0 = nSM_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_13.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_13] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_13 : ringAttnBuddies pm_goal_3 nR0_13 = [nR0_13, nR1_13] := by
  show (List.filter (fun m => decide (m.op = nR0_13.op) && decide (m.params = nR0_13.params) &&
      decide (m.ins.getD 3 0 = nR0_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_13.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_13, nR1_13]
  rw [show (List.filter (fun m => decide (m.op = nR0_13.op) && decide (m.params = nR0_13.params) &&
      decide (m.ins.getD 3 0 = nR0_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_13.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_13, nR1_13] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_13 : ringAttnBuddies pm_goal_3 nR1_13 = [nR0_13, nR1_13] := by
  show (List.filter (fun m => decide (m.op = nR1_13.op) && decide (m.params = nR1_13.params) &&
      decide (m.ins.getD 3 0 = nR1_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_13.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_13, nR1_13]
  rw [show (List.filter (fun m => decide (m.op = nR1_13.op) && decide (m.params = nR1_13.params) &&
      decide (m.ins.getD 3 0 = nR1_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_13.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_13, nR1_13] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L13 pre-attention denote-unfold chain (SM side)

L13 is a normal CP layer: the Q path is `carry 5387 → rms 5389 → per_head 5391`
(no `fw_maybe_shuffle`).  K/V (`5392`/`5393`) are the *same* projections used by
L12 (`5334`/`5336`, produced in the L12 block), so their replication commutes
reuse `sm_pm_rms_L12_commute`. -/

-- SM 5389 = rms(carry 5387, 5388); multiref 5387→[8178,8182] node idx 536, rms node idx 537.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5389 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5389 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5387) (initSM 5388) := by
  refine DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5389 8178 5388 537
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8178, 5388], outs := [5389] })
    (fun a1 a2 => fw_rms_norm (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8178 5388 5389)
    ?_ ?_
  · refine DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8178 5387 536
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5387 8178 [8178, 8182] 2 (by decide) (by decide)])
      rfl
  · exact DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5388 (by decide) (by decide)

-- SM 5391 = per_head_linear(rms 5389, 5390); node idx 538.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5391 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5391 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5389) (initSM 5390) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5391 5389 5390 538
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5389, 5390], outs := [5391] })
    (fun a1 a2 => fw_per_head_linear (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5389 5390 5391 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5390 (by decide) (by decide))

-- SM 5392 = to(8037); 8037 = multiref(5334) pos 1. to node idx 481, multiref idx 477.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5392 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5392 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5392 8037 481
    ({ rank := 0, op := "OpName.FW_to", ins := [8037], outs := [5392] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8037 5392 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8037 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8037 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

-- SM 5393 = to(8095); 8095 = multiref(5336) pos 1. to node idx 493, multiref idx 478.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5393 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5393 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5393 8095 493
    ({ rank := 0, op := "OpName.FW_to", ins := [8095], outs := [5393] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8095 5393 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8095 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8095 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ## L13 pre-attention denote-unfold chain (PM side, rank 0 + rank 1) -/

-- PM 9835 = per_head(rms(multiref(9829)), 5390); rms 9833 idx 1133, multiref 16047 idx 1131, q idx 1135.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9833 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9833 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9829) (initPM 5388) := by
  refine DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9833 16047 5388 1133
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16047, 5388], outs := [9833] })
    (fun a1 a2 => fw_rms_norm (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16047 5388 9833)
    ?_ ?_
  · refine DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16047 9829 1131
      ({ rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_multiref_out pm_goal_3 s 0 9829 16047 [16047, 16051] 2 (by decide) (by decide)])
      rfl
  · exact DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5388 (by decide) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9835 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9835 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 9833) (initPM 5390) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9835 9833 5390 1135
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9833, 5390], outs := [9835] })
    (fun a1 a2 => fw_per_head_linear (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 9833 5390 9835 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5390 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9834 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9834 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9830) (initPM 5388) := by
  refine DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9834 16055 5388 1134
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16055, 5388], outs := [9834] })
    (fun a1 a2 => fw_rms_norm (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16055 5388 9834)
    ?_ ?_
  · refine DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16055 9830 1132
      ({ rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_multiref_out pm_goal_3 s 1 9830 16055 [16055, 16059] 2 (by decide) (by decide)])
      rfl
  · exact DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5388 (by decide) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9836 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9836 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 9834) (initPM 5390) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9836 9834 5390 1136
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9834, 5390], outs := [9836] })
    (fun a1 a2 => fw_per_head_linear (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 9834 5390 9836 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5390 (by decide) (by decide))

-- PM 5392 = to(15819) (rank-1 last writer); 15819 = multiref(5334) pos 1. to idx 1032, multiref idx 1016.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5392 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5392 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5392 15819 1032
    ({ rank := 1, op := "OpName.FW_to", ins := [15819], outs := [5392] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15819 5392 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15819 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15819 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

-- PM 5393 = to(15925) (rank-1 last writer); 15925 = multiref(5336) pos 1. to idx 1056, multiref idx 1018.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5393 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5393 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5393 15925 1056
    ({ rank := 1, op := "OpName.FW_to", ins := [15925], outs := [5393] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15925 5393 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15925 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15925 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)

/-! ## L13 K/V replication commutes (reuse `sm_pm_rms_L12_commute`) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L13_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5392 =
      denoteGraph_ringAttn pm_goal_3 initPM 5392 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5333 : initSM 5333 = initPM 5333 := hb initGoal_5333 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5392, denote_sm_goal_3_5334, hrms, hw5333,
      denote_pm_goal_3_5392, denote_pm_goal_3_5334]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L13_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5393 =
      denoteGraph_ringAttn pm_goal_3 initPM 5393 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5335 : initSM 5335 = initPM 5335 := hb initGoal_5335 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5393, denote_sm_goal_3_5336, hrms, hw5335,
      denote_pm_goal_3_5393, denote_pm_goal_3_5336]

/-! ## L13 Q full-sharding commute (no shuffle; Q path = per_head ∘ rms) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L13_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5387 : denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830])
    (h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024])
    (h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024])
    (hw5390 : (initPM 5390).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5391 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9835,
         denoteGraph_ringAttn pm_goal_3 initPM 9836] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5388 : initSM 5388 = initPM 5388 := hb initGoal_5388 (by decide) rfl
  have hw5390e : initSM 5390 = initPM 5390 := hb initGoal_5390 (by decide) rfl
  rw [denote_sm_goal_3_5391, denote_sm_goal_3_5389,
      denote_pm_goal_3_9835, denote_pm_goal_3_9833,
      denote_pm_goal_3_9836, denote_pm_goal_3_9834]
  rw [hcarry5387, hw5388, hw5390e]
  have hrms9829 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9829) (initPM 5388)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h9829]
  have hrms9830 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9830) (initPM 5388)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h9830]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5388) 2048 1024 (by omega) (by omega) h9829 h9830,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5390) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms9829 hrms9830 hw5390]

/-! ## L13 attention denote ↔ applyNodeRingAttn_zigzag bridges
SM attn node idx = 539; PM r0 = 1137, r1 = 1138. -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L13_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5396
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_13 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5396
      = (sm_goal_3.nodes.take 540).foldl (applyNodeRingAttn sm_goal_3) initSM 5396 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5396 540 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 540 = sm_goal_3.nodes.take 539 ++ [nSM_13] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5391 5392 5393 5394 5395 5396 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L13_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9859
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_13 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 9859
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 9859 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9859 1138 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1138 = pm_goal_3.nodes.take 1137 ++ [nR0_13] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 9835 5392 5393 5394 5395 9859 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L13_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9860
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_13 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 9860
      = (pm_goal_3.nodes.take 1139).foldl (applyNodeRingAttn pm_goal_3) initPM 9860 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9860 1139 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1139 = pm_goal_3.nodes.take 1138 ++ [nR1_13] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 9836 5392 5393 5394 5395 9860 [16, 4, 64, 64, 1, 0]

/-! ## L13 attention commute (reuse `applyNodeRingAttn_zigzag_reconstruction_2_cp`) -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L13_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626])
    (hcarry5387 : denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830])
    (hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5391).shape.length)
    (hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5392).shape.length)
    (hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5393).shape.length)
    (h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024])
    (h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024])
    (hw5390 : (initPM 5390).shape = [16, 64, 1024])
    (hk_shape :
      ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392).shape
        = [4096, 4, 64])
    (hv_shape :
      ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393])
        ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5394)
        ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5396
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9859,
           denoteGraph_ringAttn pm_goal_3 initPM 9860] := by
  have hkrepl := sm_pm_krepl_L13_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L13_commute initSM initPM hInit hcarry5330
  have hq_full :
      (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5391 =
        allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836] := by
    have bq5391 : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5391
        = denoteGraph_ringAttn sm_goal_3 initSM 5391 :=
      (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5391 539 (by decide) (by decide)).symm
    have bq9835 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835
        = denoteGraph_ringAttn pm_goal_3 initPM 9835 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9835 1137 (by decide) (by decide)).symm
    have bq9836 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836
        = denoteGraph_ringAttn pm_goal_3 initPM 9836 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9836 1137 (by decide) (by decide)).symm
    rw [bq5391, bq9835, bq9836]
    exact sm_pm_qfull_L13_commute initSM initPM hInit hcarry5387 h9829 h9830 hw5390
  have bSM5392 : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5392
      = denoteGraph_ringAttn sm_goal_3 initSM 5392 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5392 539 (by decide) (by decide)).symm
  have bSM5393 : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5393
      = denoteGraph_ringAttn sm_goal_3 initSM 5393 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5393 539 (by decide) (by decide)).symm
  have bPM5392 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392
      = denoteGraph_ringAttn pm_goal_3 initPM 5392 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5392 1137 (by decide) (by decide)).symm
  have bPM5393 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393
      = denoteGraph_ringAttn pm_goal_3 initPM 5393 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5393 1137 (by decide) (by decide)).symm
  have hb := L12_weight_eq initSM initPM hInit
  have hS5394 : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5394 = initSM 5394 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 539) initSM 5394 (by decide) (by decide)
  have hS5395 : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5395 = initSM 5395 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 539) initSM 5395 (by decide) (by decide)
  have hP5394 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5394 = initPM 5394 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1137) initPM 5394 (by decide) (by decide)
  have hP5395 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395 = initPM 5395 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1137) initPM 5395 (by decide) (by decide)
  have hw5394 : initSM 5394 = initPM 5394 := hb initGoal_5394 (by decide) rfl
  have hw5395 : initSM 5395 = initPM 5395 := hb initGoal_5395 (by decide) rfl
  have hkfull : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5392
      = (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392 := by
    rw [bSM5392, bPM5392, hkrepl]
  have hvfull : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5393
      = (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393 := by
    rw [bSM5393, bPM5393, hvrepl]
  have hcuQ : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5394
      = (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5394 := by
    rw [hS5394, hP5394, hw5394]
  have hcuK : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5395
      = (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395 := by
    rw [hS5395, hP5395, hw5395]
  have e9835 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 9835 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9835 1137 1138 (by omega) (by decide) (by decide)).symm
  have e9836 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 9836 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9836 1137 1138 (by omega) (by decide) (by decide)).symm
  have e5392 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 5392 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5392 1137 1138 (by omega) (by decide) (by decide)).symm
  have e5393 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 5393 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5393 1137 1138 (by omega) (by decide) (by decide)).symm
  have e5394 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5394
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 5394 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5394 1137 1138 (by omega) (by decide) (by decide)).symm
  have e5395 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395
      = (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 5395 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5395 1137 1138 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_13
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_13 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_13]; intro m hm; fin_cases hm
      · exact e9835
      · exact e9836
    · rw [buddy_r1_13]; intro m hm; fin_cases hm
      · exact e5392
      · exact e5392
    · rw [buddy_r1_13]; intro m hm; fin_cases hm
      · exact e5393
      · exact e5393
    · exact e5394
    · exact e5395
  have bSM5391 : (sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5391
      = denoteGraph_ringAttn sm_goal_3 initSM 5391 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5391 539 (by decide) (by decide)).symm
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_13.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5391).shape.length
    rw [bSM5391]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_13.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5392).shape.length
    rw [bSM5392]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_13.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM 5393).shape.length
    rw [bSM5393]; exact hv_sm
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 539).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_13 nR0_13 nR1_13 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_13 buddy_r0_13 buddy_r1_13 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hkfull hvfull hk_shape hv_shape h_bound
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L13_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L13_r0_bridge, ← denote_pm_attn_L13_r1_bridge]

/-! ## L13 attention commute — shapes discharged from `StoreShapesHold`

The only L13-boundary facts kept as hypotheses are the input-carry commute
(`hcarry5387`) and the two PM carry-shard shapes (`h9829`/`h9830`); the L12 block
output is not proven on `main`.  Everything else (K/V shapes, SM length facts) is
discharged internally, reusing the shared L12 K/V-projection chain. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L13_commute' (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5395)).getD (t+1) 0 ≤ 4096)
    (hcarry5387 : denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830])
    (h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024])
    (h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5396
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9859,
           denoteGraph_ringAttn pm_goal_3 initPM 9860] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have hw5390 : (initPM 5390).shape = [16, 64, 1024] := hPM 5390 [16, 64, 1024] (by decide)
  -- PM Q-path shard shapes [2048,16,64] (no shuffle)
  have h9833 : (denoteGraph_ringAttn pm_goal_3 initPM 9833).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9833, rms_sh]; exact h9829
  have h9834 : (denoteGraph_ringAttn pm_goal_3 initPM 9834).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9834, rms_sh]; exact h9830
  have h9835 : (denoteGraph_ringAttn pm_goal_3 initPM 9835).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9835]; exact ph_lin_shape_gen _ _ 2048 16 h9833 hw5390
  have h9836 : (denoteGraph_ringAttn pm_goal_3 initPM 9836).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9836]; exact ph_lin_shape_gen _ _ 2048 16 h9834 hw5390
  -- PM K/V full (replicated) shapes [4096,4,64] (shared L12 projections)
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  have hPM5392 : (denoteGraph_ringAttn pm_goal_3 initPM 5392).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5392, denote_pm_goal_3_5334]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))
  have hPM5393 : (denoteGraph_ringAttn pm_goal_3 initPM 5393).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5393, denote_pm_goal_3_5336]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))
  have hqfull := sm_pm_qfull_L13_commute initSM initPM hInit hcarry5387 h9829 h9830 hw5390
  have hkrepl := sm_pm_krepl_L13_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L13_commute initSM initPM hInit hcarry5330
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5391).shape = [4096, 16, 64] := by
    rw [hqfull]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9835)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5391).shape.length := by
    rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5392).shape.length := by
    rw [hkrepl, hPM5392]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5393).shape.length := by
    rw [hvrepl, hPM5393]; decide
  have bPM5392 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392
      = denoteGraph_ringAttn pm_goal_3 initPM 5392 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5392 1137 (by decide) (by decide)).symm
  have bPM5393 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393
      = denoteGraph_ringAttn pm_goal_3 initPM 5393 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5393 1137 (by decide) (by decide)).symm
  have bPM9835 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835
      = denoteGraph_ringAttn pm_goal_3 initPM 9835 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9835 1137 (by decide) (by decide)).symm
  have bPM9836 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836
      = denoteGraph_ringAttn pm_goal_3 initPM 9836 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9836 1137 (by decide) (by decide)).symm
  have hk_shape : ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392).shape
      = [4096, 4, 64] := by rw [bPM5392]; exact hPM5392
  have hv_shape : ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393).shape
      = [4096, 4, 64] := by rw [bPM5393]; exact hPM5393
  have hP5395 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395 = initPM 5395 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1137) initPM 5395 (by decide) (by decide)
  have h_bound' : ∀ t, (decodeCuSeqlens
      ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395)).getD (t+1) 0 ≤ 4096 := by
    intro t; rw [hP5395]; exact h_bound t
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5392])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393,
           (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5393])
        ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5394)
        ((pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 5395)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835,
         (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836]).shape
        = [4096, 16, 64] := by
      rw [bPM9835, bPM9836]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9835)
    rw [hq]; rfl
  exact sm_pm_attention_L13_commute initSM initPM hInit hcarry5330 hcarry5387
    hq_sm hk_sm hv_sm h9829 h9830 hw5390 hk_shape hv_shape h_bound' hfull_shape

/-! ## L13 post-attention reshape/linear/view/float denote chain -/

-- SM post-attn: 5396 → 5397 → 5398 → 5400(w5399) → 5401 → 5402
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5397 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5397 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5396) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5397 5396 540
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5396], outs := [5397], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5396 5397 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5398 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5398 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5397) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5398 5397 541
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5397], outs := [5398], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5397 5398 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5400 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5400 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5398) (initSM 5399) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5400 5398 5399 542
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5398, 5399], outs := [5400] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5398 5399 5400)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5399 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5401 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5401 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5400) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5401 5400 543
    ({ rank := 0, op := "OpName.FW_view", ins := [5400], outs := [5401], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5400 5401)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5402 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5402 =
      denoteGraph_ringAttn sm_goal_3 initSM 5401 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5402 5401 544
    ({ rank := 0, op := "OpName.FW_float", ins := [5401], outs := [5402] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5401 5402 [])
    rfl

-- PM r0 post-attn: 9859 → 9861 → 9867 → 9871(w5399) → 9881 → 9885
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9861 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9861 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9859) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9861 9859 1139
    ({ rank := 0, op := "OpName.FW_reshape", ins := [9859], outs := [9861], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 9859 9861 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9867 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9867 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9861) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9867 9861 1141
    ({ rank := 0, op := "OpName.FW_reshape", ins := [9861], outs := [9867], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 9861 9867 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9871 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9871 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9867) (initPM 5399) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9871 9867 5399 1143
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9867, 5399], outs := [9871] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9867 5399 9871)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5399 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9881 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9881 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9871) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9881 9871 1145
    ({ rank := 0, op := "OpName.FW_view", ins := [9871], outs := [9881], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 9871 9881)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9885 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9885 =
      denoteGraph_ringAttn pm_goal_3 initPM 9881 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9885 9881 1147
    ({ rank := 0, op := "OpName.FW_float", ins := [9881], outs := [9885] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 9881 9885 [])
    rfl

-- PM r1 post-attn: 9860 → 9862 → 9868 → 9872(w5399) → 9882 → 9886
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9862 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9862 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9860) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9862 9860 1140
    ({ rank := 1, op := "OpName.FW_reshape", ins := [9860], outs := [9862], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 9860 9862 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9868 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9868 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9862) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9868 9862 1142
    ({ rank := 1, op := "OpName.FW_reshape", ins := [9862], outs := [9868], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 9862 9868 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9872 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9872 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9868) (initPM 5399) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9872 9868 5399 1144
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9868, 5399], outs := [9872] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9868 5399 9872)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5399 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9882 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9882 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9872) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9882 9872 1146
    ({ rank := 1, op := "OpName.FW_view", ins := [9872], outs := [9882], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 9872 9882)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9886 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9886 =
      denoteGraph_ringAttn pm_goal_3 initPM 9882 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9886 9882 1148
    ({ rank := 1, op := "OpName.FW_float", ins := [9882], outs := [9886] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 9882 9886 [])
    rfl

/-! ## L13 residual carry + rms/float/norm_linear/topk denote chain -/

-- Multiref passthroughs feeding the residual add (left = carry, no shuffle).
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_8182 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8182 =
      denoteGraph_ringAttn sm_goal_3 initSM 5387 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8182 5387 536
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5387 8182 [8178, 8182] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_16051 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16051 =
      denoteGraph_ringAttn pm_goal_3 initPM 9829 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16051 9829 1131
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9829 16051 [16047, 16051] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_16059 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16059 =
      denoteGraph_ringAttn pm_goal_3 initPM 9830 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16059 9830 1132
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9830 16059 [16055, 16059] 2 (by decide) (by decide))
    rfl

-- Residual adds: 5403 = add(8182, 5402); PM 9889 = add(16051, 9885), 9890 = add(16059, 9886).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5403 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5403 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8182)
        (denoteGraph_ringAttn sm_goal_3 initSM 5402) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5403 8182 5402 545
    ({ rank := 0, op := "OpName.FW_add", ins := [8182, 5402], outs := [5403] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8182 5402 5403)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9889 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9889 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16051)
        (denoteGraph_ringAttn pm_goal_3 initPM 9885) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9889 16051 9885 1149
    ({ rank := 0, op := "OpName.FW_add", ins := [16051, 9885], outs := [9889] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16051 9885 9889)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9890 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9890 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16059)
        (denoteGraph_ringAttn pm_goal_3 initPM 9886) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9890 16059 9886 1150
    ({ rank := 1, op := "OpName.FW_add", ins := [16059, 9886], outs := [9890] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16059 9886 9890)
    rfl rfl

-- RMS: 5405 = rms(mr 5403, 5404); PM 9893/9894.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5405 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5405 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5403) (initSM 5404) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5405 8186 5404 547
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8186, 5404], outs := [5405] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8186 5404 5405)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8186 5403 546
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5403], outs := [8186, 8190], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5403 8186 [8186, 8190] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5404 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9893 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9893 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9889) (initPM 5404) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9893 16063 5404 1153
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16063, 5404], outs := [9893] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16063 5404 9893)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16063 9889 1151
      ({ rank := 0, op := "OpName.FW_multiref", ins := [9889], outs := [16063, 16067], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9889 16063 [16063, 16067] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5404 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9894 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9894 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9890) (initPM 5404) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9894 16071 5404 1154
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16071, 5404], outs := [9894] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16071 5404 9894)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16071 9890 1152
      ({ rank := 1, op := "OpName.FW_multiref", ins := [9890], outs := [16071, 16075], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9890 16071 [16071, 16075] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5404 (by decide) (by decide))

-- Float (through the 5-way multiref): 5406 = float(mr 5405); PM 9895/9896.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5406 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5406 =
      denoteGraph_ringAttn sm_goal_3 initSM 5405 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5406 8197 549
    ({ rank := 0, op := "OpName.FW_float", ins := [8197], outs := [5406] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8197 5406 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8197 5405 548
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5405 8197 [8197, 8201, 8205, 8209, 8213] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9895 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9895 =
      denoteGraph_ringAttn pm_goal_3 initPM 9893 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9895 16082 1157
    ({ rank := 0, op := "OpName.FW_float", ins := [16082], outs := [9895] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16082 9895 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16082 9893 1155
      ({ rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9893 16082 [16082, 16086, 16090, 16094, 16098] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9896 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9896 =
      denoteGraph_ringAttn pm_goal_3 initPM 9894 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9896 16105 1161
    ({ rank := 1, op := "OpName.FW_float", ins := [16105], outs := [9896] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16105 9896 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16105 9894 1156
      ({ rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9894 16105 [16105, 16109, 16113, 16117, 16121] 5 (by decide) (by decide))
      rfl)

-- Norm-linear: 5408 = nl(5406, 5407); PM 9901/9902.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5408 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5408 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5406) (initSM 5407) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5408 5406 5407 553
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5406, 5407], outs := [5408] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5406 5407 5408 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5407 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9901 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9901 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 9895) (initPM 5407) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9901 9895 5407 1165
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [9895, 5407], outs := [9901] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 9895 5407 9901 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5407 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9902 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9902 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 9896) (initPM 5407) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9902 9896 5407 1169
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [9896, 5407], outs := [9902] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 9896 5407 9902 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5407 (by decide) (by decide))

-- Topk (2nd output = router logits map): 5410; PM 9905/9906.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5410 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5410 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5408) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5408).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5410 5408 557
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5408], outs := [5409, 5410, 5411], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5408 5409 5410 5411 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9905 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9905 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9901) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 9901).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9905 9901 1173
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [9901], outs := [9903, 9905, 9907], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 9901 9903 9905 9907 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9906 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9906 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9902) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 9902).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9906 9902 1177
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [9902], outs := [9904, 9906, 9908], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 9902 9904 9906 9908 [8] (by decide))
    rfl

/-! ## L13 post-attention reshape-float + residual carry commutes -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_5402_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5396 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9859,
         denoteGraph_ringAttn pm_goal_3 initPM 9860])
    (h9859 : (denoteGraph_ringAttn pm_goal_3 initPM 9859).shape = [2048, 16, 64])
    (h9860 : (denoteGraph_ringAttn pm_goal_3 initPM 9860).shape = [2048, 16, 64])
    (hw5399 : (initPM 5399).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5402 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9885,
         denoteGraph_ringAttn pm_goal_3 initPM 9886] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5399 = initPM 5399 := hb initGoal_5399 (by decide) rfl
  rw [denote_sm_goal_3_5402, denote_sm_goal_3_5401, denote_sm_goal_3_5400,
      denote_sm_goal_3_5398, denote_sm_goal_3_5397,
      denote_pm_goal_3_9885, denote_pm_goal_3_9881, denote_pm_goal_3_9871,
      denote_pm_goal_3_9867, denote_pm_goal_3_9861,
      denote_pm_goal_3_9886, denote_pm_goal_3_9882, denote_pm_goal_3_9872,
      denote_pm_goal_3_9868, denote_pm_goal_3_9862]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h9859 h9860]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9859))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9860))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5399) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5399]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9859))) (initPM 5399)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5399]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9860))) (initPM 5399)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5399]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9859))) (initPM 5399),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9860))) (initPM 5399)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5403_commute (initSM initPM : Store)
    (hcarry5387 : denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5402 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9885,
         denoteGraph_ringAttn pm_goal_3 initPM 9886])
    (h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024])
    (h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024])
    (h9885 : (denoteGraph_ringAttn pm_goal_3 initPM 9885).shape = [2048, 1024])
    (h9886 : (denoteGraph_ringAttn pm_goal_3 initPM 9886).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5403 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9889,
         denoteGraph_ringAttn pm_goal_3 initPM 9890] := by
  rw [denote_sm_goal_3_5403, denote_pm_goal_3_9889, denote_pm_goal_3_9890,
      denote_sm_goal_3_8182, denote_pm_goal_3_16051, denote_pm_goal_3_16059]
  rw [hcarry5387, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h9829 h9830 h9885 h9886]

/-! ## L13 router head: rms → norm_linear → topk commute -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L13_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5403 : denoteGraph_ringAttn sm_goal_3 initSM 5403 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9889,
         denoteGraph_ringAttn pm_goal_3 initPM 9890])
    (h9889 : (denoteGraph_ringAttn pm_goal_3 initPM 9889).shape = [2048, 1024])
    (h9890 : (denoteGraph_ringAttn pm_goal_3 initPM 9890).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5408 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9901,
         denoteGraph_ringAttn pm_goal_3 initPM 9902] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5404 : initSM 5404 = initPM 5404 := hb initGoal_5404 (by decide) rfl
  have hw5407 : initSM 5407 = initPM 5407 := hb initGoal_5407 (by decide) rfl
  have hw5407sh : (initPM 5407).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5407 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5407] using hsh
  rw [denote_sm_goal_3_5408, denote_sm_goal_3_5406, denote_sm_goal_3_5405,
      denote_pm_goal_3_9901, denote_pm_goal_3_9895, denote_pm_goal_3_9893,
      denote_pm_goal_3_9902, denote_pm_goal_3_9896, denote_pm_goal_3_9894]
  rw [hw5404, hw5407, hcarry5403]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5404) 2048 1024 (by omega) (by omega) h9889 h9890]
  have hrms9889 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9889) (initPM 5404)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9889
  have hrms9890 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9890) (initPM 5404)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9890
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5407) 2048 1024 64 (by omega) (by omega) (by omega) hrms9889 hrms9890 hw5407sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L13 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5403 : denoteGraph_ringAttn sm_goal_3 initSM 5403 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9889,
         denoteGraph_ringAttn pm_goal_3 initPM 9890])
    (h9889 : (denoteGraph_ringAttn pm_goal_3 initPM 9889).shape = [2048, 1024])
    (h9890 : (denoteGraph_ringAttn pm_goal_3 initPM 9890).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5410 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9905,
         denoteGraph_ringAttn pm_goal_3 initPM 9906] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5407sh : (initPM 5407).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5407 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5407] using hsh
  have hnl := sm_pm_nl_L13_commute initSM initPM hInit hcarry5403 h9889 h9890
  have hs9901 : (denoteGraph_ringAttn pm_goal_3 initPM 9901).shape = [2048, 64] := by
    rw [denote_pm_goal_3_9901, denote_pm_goal_3_9895, denote_pm_goal_3_9893]
    exact nl_sh 2048 1024 64 _ (initPM 5407) (by rw [rms_sh]; exact h9889) hw5407sh
  have hs9902 : (denoteGraph_ringAttn pm_goal_3 initPM 9902).shape = [2048, 64] := by
    rw [denote_pm_goal_3_9902, denote_pm_goal_3_9896, denote_pm_goal_3_9894]
    exact nl_sh 2048 1024 64 _ (initPM 5407) (by rw [rms_sh]; exact h9890) hw5407sh
  have hSM5408sh : (denoteGraph_ringAttn sm_goal_3 initSM 5408).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs9901
  rw [denote_sm_goal_3_5410, denote_pm_goal_3_9905, denote_pm_goal_3_9906]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5408).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5408sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 9901).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9901]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 9902).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9902]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs9901 hs9902

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L13_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5387 : denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5396 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9859,
         denoteGraph_ringAttn pm_goal_3 initPM 9860])
    (h9859 : (denoteGraph_ringAttn pm_goal_3 initPM 9859).shape = [2048, 16, 64])
    (h9860 : (denoteGraph_ringAttn pm_goal_3 initPM 9860).shape = [2048, 16, 64])
    (h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024])
    (h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024])
    (hw5399 : (initPM 5399).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5410 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9905,
         denoteGraph_ringAttn pm_goal_3 initPM 9906] := by
  have hreshape := sm_pm_reshape_float_5402_commute initSM initPM hInit hattn h9859 h9860 hw5399
  have h9885 : (denoteGraph_ringAttn pm_goal_3 initPM 9885).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9885, denote_pm_goal_3_9881]; rfl
  have h9886 : (denoteGraph_ringAttn pm_goal_3 initPM 9886).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9886, denote_pm_goal_3_9882]; rfl
  have hcarry5403 := sm_pm_carry_5403_commute initSM initPM hcarry5387 hreshape h9829 h9830 h9885 h9886
  have h9889 : (denoteGraph_ringAttn pm_goal_3 initPM 9889).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9889]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16051]; exact h9829) h9885
  have h9890 : (denoteGraph_ringAttn pm_goal_3 initPM 9890).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9890]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      (by rw [denote_pm_goal_3_16059]; exact h9830) h9886
  exact sm_pm_router_commute_L13 initSM initPM hInit hcarry5403 h9889 h9890

/-! ## L13 router — fully assembled from `StoreShapesHold` + cut init goals

Top-level per-layer commute for the L13 zigzag band.  All attention shape /
sharding hypotheses are discharged internally from the two `StoreShapesHold`
well-formedness facts and the cut init goals.  Two classes of hypotheses remain
statement-level (per AGENTS.md #29, with vacuity witnesses below):

* `h_bound` — the K cu_seqlens well-formed-input contract (`initPM 5395`);
* `hcarry5387` / `h9829` / `h9830` — the L12 block-output carry commute and its
  PM shard shapes.  The L12 block output (`SM 5387`) is not proven on `main`
  (the L12 spike proves only up to its router head and post-attention residual),
  so the L13 layer takes it as an input contract. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L13_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5395)).getD (t+1) 0 ≤ 4096)
    (hcarry5387 : denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830])
    (h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024])
    (h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5410 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9905,
         denoteGraph_ringAttn pm_goal_3 initPM 9906] := by
  have hattn := sm_pm_attention_L13_commute' initSM initPM hSM hPM hInit h_bound hcarry5387 h9829 h9830
  have hw5390 : (initPM 5390).shape = [16, 64, 1024] := hPM 5390 [16, 64, 1024] (by decide)
  have hw5399 : (initPM 5399).shape = [1024, 1024] := hPM 5399 [1024, 1024] (by decide)
  -- PM Q-path shard shapes [2048,16,64]
  have h9833 : (denoteGraph_ringAttn pm_goal_3 initPM 9833).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9833, rms_sh]; exact h9829
  have h9834 : (denoteGraph_ringAttn pm_goal_3 initPM 9834).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9834, rms_sh]; exact h9830
  have h9835d : (denoteGraph_ringAttn pm_goal_3 initPM 9835).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9835]; exact ph_lin_shape_gen _ _ 2048 16 h9833 hw5390
  have h9836d : (denoteGraph_ringAttn pm_goal_3 initPM 9836).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9836]; exact ph_lin_shape_gen _ _ 2048 16 h9834 hw5390
  -- folded-store ↔ denote bridges at the two attention Q tids
  have b1137_9835 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9835
      = denoteGraph_ringAttn pm_goal_3 initPM 9835 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9835 1137 (by decide) (by decide)).symm
  have b1137_9836 : (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM 9836
      = denoteGraph_ringAttn pm_goal_3 initPM 9836 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9836 1137 (by decide) (by decide)).symm
  have b1138_9835 : (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 9835
      = denoteGraph_ringAttn pm_goal_3 initPM 9835 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9835 1138 (by decide) (by decide)).symm
  have b1138_9836 : (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM 9836
      = denoteGraph_ringAttn pm_goal_3 initPM 9836 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9836 1138 (by decide) (by decide)).symm
  -- PM attention output shapes [2048,16,64] (chunk of the full [4096,16,64])
  have h9859 : (denoteGraph_ringAttn pm_goal_3 initPM 9859).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L13_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_13 nR0_13 nR1_13 0 buddy_r0_13 (by decide)]
    have e0 : nR0_13.ins.getD 0 0 = 9835 := by decide
    have e1 : nR1_13.ins.getD 0 0 = 9836 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_13.ins.getD 0 0),
         (pm_goal_3.nodes.take 1137).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_13.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1137_9835, b1137_9836]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9835d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h9860 : (denoteGraph_ringAttn pm_goal_3 initPM 9860).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L13_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_13 nR0_13 nR1_13 1 buddy_r1_13 (by decide)]
    have e0 : nR0_13.ins.getD 0 0 = 9835 := by decide
    have e1 : nR1_13.ins.getD 0 0 = 9836 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_13.ins.getD 0 0),
         (pm_goal_3.nodes.take 1138).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_13.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1138_9835, b1138_9836]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9835d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L13_from_attention initSM initPM hInit hcarry5387
    hattn h9859 h9860 h9829 h9830 hw5399

/-! ## Vacuity witnesses for the statement-level hypotheses (AGENTS.md #29) -/

-- `h_bound`: the all-zero cu_seqlens store satisfies the K-length bound.
theorem sm_pm_router_L13_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5395)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

-- `hcarry5387` / `h9829` / `h9830`: the L12 block-output carry commute and its PM
-- shard shapes.  These are the standard per-layer carry contract (identical in form
-- to the proven `sm_pm_carry_5354_commute` / `sm_pm_carry_5330_commute`), threaded
-- into L13 exactly as L12 threaded the proven `sm_pm_carry_5330_commute`.  They are
-- *not* vacuous: the equation `SM residual = allGather0 [PM shard, PM shard]` is the
-- same shape/sharding relation discharged for every earlier layer.  A closed proof of
-- this specific instance requires the L12 MoE-sublayer commute (`SM 5387`), which is
-- not yet on `main`; when that lands it discharges `hcarry5387`/`h9829`/`h9830`
-- directly, making `sm_pm_router_commute_L13_full` unconditional (cf. AGENTS.md #4).

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L13_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L13
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L13_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L13_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L13_hbound_witness
