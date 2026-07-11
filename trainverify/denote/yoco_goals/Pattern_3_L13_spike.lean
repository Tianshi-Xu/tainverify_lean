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

end TrainVerify.Denote.GeneratedPatterns
