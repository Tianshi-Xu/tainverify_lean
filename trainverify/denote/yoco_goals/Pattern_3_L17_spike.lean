/-
  Pattern_3_L17_spike.lean — L17 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L17-specific TIDs.  The L17 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L17's Q path
  is just  carry -> rms -> per_head_linear -> attn.

  Imports the frozen L12 pilot to reuse the op-parametric zigzag reconstruction
  primitives and the L11/L12 carry commute `sm_pm_carry_5330_commute`.
-/
import denote.yoco_goals.Pattern_3_L12_spike

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

/-! ## L17 attention node declarations + buddy proofs.
SM attn node index 679; PM r0 = 1417; PM r1 = 1418. -/

def nSM_17 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5587, 5588, 5589, 5590, 5591], outs := [5592],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_17 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10523, 5588, 5589, 5590, 5591], outs := [10547],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_17 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10524, 5588, 5589, 5590, 5591], outs := [10548],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_17 : ringAttnBuddies sm_goal_3 nSM_17 = [nSM_17] := by
  show (List.filter (fun m => decide (m.op = nSM_17.op) && decide (m.params = nSM_17.params) &&
      decide (m.ins.getD 3 0 = nSM_17.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_17.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_17]
  rw [show (List.filter (fun m => decide (m.op = nSM_17.op) && decide (m.params = nSM_17.params) &&
      decide (m.ins.getD 3 0 = nSM_17.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_17.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_17] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_17 : ringAttnBuddies pm_goal_3 nR0_17 = [nR0_17, nR1_17] := by
  show (List.filter (fun m => decide (m.op = nR0_17.op) && decide (m.params = nR0_17.params) &&
      decide (m.ins.getD 3 0 = nR0_17.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_17.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_17, nR1_17]
  rw [show (List.filter (fun m => decide (m.op = nR0_17.op) && decide (m.params = nR0_17.params) &&
      decide (m.ins.getD 3 0 = nR0_17.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_17.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_17, nR1_17] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_17 : ringAttnBuddies pm_goal_3 nR1_17 = [nR0_17, nR1_17] := by
  show (List.filter (fun m => decide (m.op = nR1_17.op) && decide (m.params = nR1_17.params) &&
      decide (m.ins.getD 3 0 = nR1_17.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_17.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_17, nR1_17]
  rw [show (List.filter (fun m => decide (m.op = nR1_17.op) && decide (m.params = nR1_17.params) &&
      decide (m.ins.getD 3 0 = nR1_17.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_17.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_17, nR1_17] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L17 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L17_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5592
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_17 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5592
      = (sm_goal_3.nodes.take 680).foldl (applyNodeRingAttn sm_goal_3) initSM 5592 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5592 680 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 680 = sm_goal_3.nodes.take 679 ++ [nSM_17] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5587 5588 5589 5590 5591 5592 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L17_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10547
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_17 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10547
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10547 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10547 1418 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1418 = pm_goal_3.nodes.take 1417 ++ [nR0_17] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10523 5588 5589 5590 5591 10547 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L17_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10548
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_17 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10548
      = (pm_goal_3.nodes.take 1419).foldl (applyNodeRingAttn pm_goal_3) initPM 10548 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10548 1419 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1419 = pm_goal_3.nodes.take 1418 ++ [nR1_17] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10524 5588 5589 5590 5591 10548 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L17) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5585 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5583) (initSM 5584) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5585 8334 5584 677
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8334, 5584], outs := [5585] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8334 5584 5585)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8334 5583 676
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5583], outs := [8334, 8338], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5583 8334 [8334, 8338] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5584 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5587 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5585) (initSM 5586) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5587 5585 5586 678
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5585, 5586], outs := [5587] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5585 5586 5587 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5586 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5593 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5592) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5593 5592 680
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5592], outs := [5593], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5592 5593 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5594 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5593) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5594 5593 681
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5593], outs := [5594], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5593 5594 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5596 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5594) (initSM 5595) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5596 5594 5595 682
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5594, 5595], outs := [5596] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5594 5595 5596)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5595 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5597 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5596) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5597 5596 683
    ({ rank := 0, op := "OpName.FW_view", ins := [5596], outs := [5597], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5596 5597)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5598 =
      denoteGraph_ringAttn sm_goal_3 initSM 5597 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5598 5597 684
    ({ rank := 0, op := "OpName.FW_float", ins := [5597], outs := [5598] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5597 5598 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5599 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5583)
        (denoteGraph_ringAttn sm_goal_3 initSM 5598) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8338 = denoteGraph_ringAttn sm_goal_3 initSM 5583 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8338 5583 676
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5583], outs := [8334, 8338], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5583 8338 [8334, 8338] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5599 8338 5598 685
    ({ rank := 0, op := "OpName.FW_add", ins := [8338, 5598], outs := [5599] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8338 5598 5599)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5601 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5599) (initSM 5600) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5601 8342 5600 687
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8342, 5600], outs := [5601] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8342 5600 5601)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8342 5599 686
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5599], outs := [8342, 8346], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5599 8342 [8342, 8346] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5600 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5602 =
      denoteGraph_ringAttn sm_goal_3 initSM 5601 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5602 8353 689
    ({ rank := 0, op := "OpName.FW_float", ins := [8353], outs := [5602] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8353 5602 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8353 5601 688
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5601 8353 [8353, 8357, 8361, 8365, 8369] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5604 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5602) (initSM 5603) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5604 5602 5603 693
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5602, 5603], outs := [5604] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5602 5603 5604 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5603 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5606 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5604) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5604).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5606 5604 697
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5604], outs := [5605, 5606, 5607], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5604 5605 5606 5607 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5588 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5588 8053 485
    ({ rank := 0, op := "OpName.FW_to", ins := [8053], outs := [5588] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8053 5588 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8053 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8053 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589_L17 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5589 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5589 8111 497
    ({ rank := 0, op := "OpName.FW_to", ins := [8111], outs := [5589] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8111 5589 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8111 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8111 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L17) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10521 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10517) (initPM 5584) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10521 16359 5584 1413
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16359, 5584], outs := [10521] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16359 5584 10521)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16359 10517 1411
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359, 16363], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10517 16359 [16359, 16363] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5584 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10523 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10521) (initPM 5586) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10523 10521 5586 1415
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10521, 5586], outs := [10523] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 10521 5586 10523 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5586 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10549 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10547) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10549 10547 1419
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10547], outs := [10549], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10547 10549 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10555 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10549) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10555 10549 1421
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10549], outs := [10555], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10549 10555 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10559 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10555) (initPM 5595) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10559 10555 5595 1423
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10555, 5595], outs := [10559] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10555 5595 10559)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5595 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10569 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10559) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10569 10559 1425
    ({ rank := 0, op := "OpName.FW_view", ins := [10559], outs := [10569], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10559 10569)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10573 =
      denoteGraph_ringAttn pm_goal_3 initPM 10569 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10573 10569 1427
    ({ rank := 0, op := "OpName.FW_float", ins := [10569], outs := [10573] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10569 10573 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10577 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10517)
        (denoteGraph_ringAttn pm_goal_3 initPM 10573) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16363 = denoteGraph_ringAttn pm_goal_3 initPM 10517 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16363 10517 1411
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359, 16363], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10517 16363 [16359, 16363] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10577 16363 10573 1429
    ({ rank := 0, op := "OpName.FW_add", ins := [16363, 10573], outs := [10577] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16363 10573 10577)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10581 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10577) (initPM 5600) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10581 16375 5600 1433
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16375, 5600], outs := [10581] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16375 5600 10581)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16375 10577 1431
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10577], outs := [16375, 16379], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10577 16375 [16375, 16379] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5600 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10583 =
      denoteGraph_ringAttn pm_goal_3 initPM 10581 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10583 16394 1437
    ({ rank := 0, op := "OpName.FW_float", ins := [16394], outs := [10583] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16394 10583 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16394 10581 1435
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10581 16394 [16394, 16398, 16402, 16406, 16410] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10589 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10583) (initPM 5603) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10589 10583 5603 1445
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [10583, 5603], outs := [10589] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 10583 5603 10589 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5603 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10593 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10589) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10589).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10593 10589 1453
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10589], outs := [10591, 10593, 10595], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 10589 10591 10593 10595 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10522 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10518) (initPM 5584) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10522 16367 5584 1414
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16367, 5584], outs := [10522] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16367 5584 10522)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16367 10518 1412
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367, 16371], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10518 16367 [16367, 16371] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5584 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10524 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10522) (initPM 5586) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10524 10522 5586 1416
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10522, 5586], outs := [10524] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 10522 5586 10524 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5586 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10550 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10548) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10550 10548 1420
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10548], outs := [10550], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10548 10550 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10556 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10550) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10556 10550 1422
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10550], outs := [10556], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10550 10556 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10560 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10556) (initPM 5595) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10560 10556 5595 1424
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10556, 5595], outs := [10560] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10556 5595 10560)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5595 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10570 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10560) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10570 10560 1426
    ({ rank := 1, op := "OpName.FW_view", ins := [10560], outs := [10570], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10560 10570)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10574 =
      denoteGraph_ringAttn pm_goal_3 initPM 10570 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10574 10570 1428
    ({ rank := 1, op := "OpName.FW_float", ins := [10570], outs := [10574] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10570 10574 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10578 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10518)
        (denoteGraph_ringAttn pm_goal_3 initPM 10574) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16371 = denoteGraph_ringAttn pm_goal_3 initPM 10518 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16371 10518 1412
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367, 16371], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10518 16371 [16367, 16371] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10578 16371 10574 1430
    ({ rank := 1, op := "OpName.FW_add", ins := [16371, 10574], outs := [10578] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16371 10574 10578)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10582 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10578) (initPM 5600) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10582 16383 5600 1434
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16383, 5600], outs := [10582] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16383 5600 10582)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16383 10578 1432
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10578], outs := [16383, 16387], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10578 16383 [16383, 16387] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5600 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10584 =
      denoteGraph_ringAttn pm_goal_3 initPM 10582 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10584 16417 1441
    ({ rank := 1, op := "OpName.FW_float", ins := [16417], outs := [10584] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16417 10584 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16417 10582 1436
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10582 16417 [16417, 16421, 16425, 16429, 16433] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10590 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10584) (initPM 5603) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10590 10584 5603 1449
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [10584, 5603], outs := [10590] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 10584 5603 10590 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5603 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10594 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10590) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10590).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10594 10590 1457
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10590], outs := [10592, 10594, 10596], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 10590 10592 10594 10596 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5588 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5588 15835 1036
    ({ rank := 1, op := "OpName.FW_to", ins := [15835], outs := [5588] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15835 5588 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15835 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15835 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589_L17 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5589 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5589 15941 1060
    ({ rank := 1, op := "OpName.FW_to", ins := [15941], outs := [5589] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15941 5589 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15941 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15941 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L17 commute theorems -/

-- Q sharding commute: SM 5587 = allGather0[PM 10523, PM 10524].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10517,
         denoteGraph_ringAttn pm_goal_3 initPM 10518])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024])
    (hw5586 : (initPM 5586).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5587 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10523,
         denoteGraph_ringAttn pm_goal_3 initPM 10524] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5584 = initPM 5584 := hb initGoal_5584 (by decide) rfl
  have hw5586e : initSM 5586 = initPM 5586 := hb initGoal_5586 (by decide) rfl
  rw [denote_sm_goal_3_5587_L17, denote_sm_goal_3_5585_L17,
      denote_pm_goal_3_10523_L17, denote_pm_goal_3_10521_L17,
      denote_pm_goal_3_10524_L17, denote_pm_goal_3_10522_L17]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10517) (initPM 5584)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10518) (initPM 5584)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5584) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5586) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape_L17 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5588).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588_L17, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape_L17 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5589).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589_L17, denote_pm_goal_3_5336]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))

-- K/V replication (cross-graph, full tensor): SM 5588 = PM 5588, SM 5589 = PM 5589.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5588 =
      denoteGraph_ringAttn pm_goal_3 initPM 5588 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588_L17, denote_pm_goal_3_5588_L17, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5589 =
      denoteGraph_ringAttn pm_goal_3 initPM 5589 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589_L17, denote_pm_goal_3_5589_L17, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L17 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L17_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10517,
         denoteGraph_ringAttn pm_goal_3 initPM 10518])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5592 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10547,
         denoteGraph_ringAttn pm_goal_3 initPM 10548] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5586).shape = [16, 64, 1024] := hPM 5586 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L17_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L17_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L17_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape_L17 initPM hPM
  have hVsh := pm_5589_shape_L17 initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10521).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L17, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10522).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L17, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 10523).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L17]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 10524).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L17]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5587).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5587).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5588).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5589).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 679)
  have bSM5587 : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5587 = denoteGraph_ringAttn sm_goal_3 initSM 5587 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5587 679 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5588 = denoteGraph_ringAttn sm_goal_3 initSM 5588 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5588 679 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5589 = denoteGraph_ringAttn sm_goal_3 initSM 5589 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5589 679 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1417)
  have bPM10523 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10523 = denoteGraph_ringAttn pm_goal_3 initPM 10523 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10523 1417 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10524 = denoteGraph_ringAttn pm_goal_3 initPM 10524 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10524 1417 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5588 = denoteGraph_ringAttn pm_goal_3 initPM 5588 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5588 1417 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5589 = denoteGraph_ringAttn pm_goal_3 initPM 5589 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5589 1417 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5590 = initSM 5590 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 679) initSM 5590 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5591 = initSM 5591 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 679) initSM 5591 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5590 = initPM 5590 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1417) initPM 5590 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5591 = initPM 5591 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1417) initPM 5591 (by decide) (by decide)
  have hw5590 : initSM 5590 = initPM 5590 := hb initGoal_5590 (by decide) rfl
  have hw5591 : initSM 5591 = initPM 5591 := hb initGoal_5591 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5587).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5588).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5589).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
        (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5587 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10523,
        (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10524]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5588 =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5588
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5589 =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5589
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5588).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5589).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5591)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5590 =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5590
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_17.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM 5591 =
      (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5591
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
       (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10523,
       (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10524]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
          (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 1 0),
          (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 2 0),
          (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 4 0))
        (nR0_17.params.getD 0 1) (nR0_17.params.getD 1 1) (nR0_17.params.getD 2 1) (nR0_17.params.getD 3 1)
        (decide (nR0_17.params.getD 4 0 ≠ 0)) (nR0_17.params.getD 5 0)).shape
        = [2 * 2048, nR0_17.params.getD 0 1, nR0_17.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1417 -> take 1418)
  have e10523 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10523
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10523 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10523 1417 1418 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10524
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10524 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10524 1417 1418 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5588
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 5588 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5588 1417 1418 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5589
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 5589 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5589 1417 1418 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5590
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 5590 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5590 1417 1418 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 5591
      = (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 5591 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5591 1417 1418 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_17
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_17 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_17]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_17]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_17]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 679).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_17 nR0_17 nR1_17 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_17 buddy_r0_17 buddy_r1_17 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L17_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L17_r0_bridge, ← denote_pm_attn_L17_r1_bridge]


/-! ## L17 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5592 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10547,
         denoteGraph_ringAttn pm_goal_3 initPM 10548])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10547).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10548).shape = [2048, 16, 64])
    (hw5595 : (initPM 5595).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5598 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10573,
         denoteGraph_ringAttn pm_goal_3 initPM 10574] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5595 = initPM 5595 := hb initGoal_5595 (by decide) rfl
  rw [denote_sm_goal_3_5598_L17, denote_sm_goal_3_5597_L17, denote_sm_goal_3_5596_L17,
      denote_sm_goal_3_5594_L17, denote_sm_goal_3_5593_L17,
      denote_pm_goal_3_10573_L17, denote_pm_goal_3_10569_L17, denote_pm_goal_3_10559_L17,
      denote_pm_goal_3_10555_L17, denote_pm_goal_3_10549_L17,
      denote_pm_goal_3_10574_L17, denote_pm_goal_3_10570_L17, denote_pm_goal_3_10560_L17,
      denote_pm_goal_3_10556_L17, denote_pm_goal_3_10550_L17]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10547))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10548))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5595) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10547))) (initPM 5595)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10548))) (initPM 5595)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10547))) (initPM 5595),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10548))) (initPM 5595)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute_L17 (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10517,
         denoteGraph_ringAttn pm_goal_3 initPM 10518])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5598 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10573,
         denoteGraph_ringAttn pm_goal_3 initPM 10574])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10573).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10574).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5599 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10577,
         denoteGraph_ringAttn pm_goal_3 initPM 10578] := by
  rw [denote_sm_goal_3_5599_L17, denote_pm_goal_3_10577_L17, denote_pm_goal_3_10578_L17]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5599 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10577,
         denoteGraph_ringAttn pm_goal_3 initPM 10578])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5604 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10589,
         denoteGraph_ringAttn pm_goal_3 initPM 10590] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5600 = initPM 5600 := hb initGoal_5600 (by decide) rfl
  have hw5603 : initSM 5603 = initPM 5603 := hb initGoal_5603 (by decide) rfl
  have hw5603sh : (initPM 5603).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5603 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5603] using hsh
  rw [denote_sm_goal_3_5604_L17, denote_sm_goal_3_5602_L17, denote_sm_goal_3_5601_L17,
      denote_pm_goal_3_10589_L17, denote_pm_goal_3_10583_L17, denote_pm_goal_3_10581_L17,
      denote_pm_goal_3_10590_L17, denote_pm_goal_3_10584_L17, denote_pm_goal_3_10582_L17]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5600) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10577) (initPM 5600)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10578) (initPM 5600)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5603) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L17 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5599 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10577,
         denoteGraph_ringAttn pm_goal_3 initPM 10578])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5606 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10593,
         denoteGraph_ringAttn pm_goal_3 initPM 10594] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5603).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5603 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5603] using hsh
  have hnl := sm_pm_nl_L17_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 10589).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L17, denote_pm_goal_3_10583_L17, denote_pm_goal_3_10581_L17]
    exact nl_sh 2048 1024 64 _ (initPM 5603) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 10590).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L17, denote_pm_goal_3_10584_L17, denote_pm_goal_3_10582_L17]
    exact nl_sh 2048 1024 64 _ (initPM 5603) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5604).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606_L17, denote_pm_goal_3_10593_L17, denote_pm_goal_3_10594_L17]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5604).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10589).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10590).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L17 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L17_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10517,
         denoteGraph_ringAttn pm_goal_3 initPM 10518])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5592 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10547,
         denoteGraph_ringAttn pm_goal_3 initPM 10548])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10547).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10548).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024])
    (hw5595 : (initPM 5595).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5606 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10593,
         denoteGraph_ringAttn pm_goal_3 initPM 10594] := by
  have hreshape := sm_pm_reshape_float_L17_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10573).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L17, denote_pm_goal_3_10569_L17]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10574).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L17, denote_pm_goal_3_10570_L17]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L17 initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L17]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L17]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L17 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L17 router — fully assembled

The only genuinely-external hypotheses beyond the two `StoreShapesHold`
well-formedness facts and the cut init goals are:
  * `h_bound`   — the K cu_seqlens well-formed-input contract (like L12),
  * `hcarry5583`, `h10517`, `h10518` — the L16 residual carry-out commute and
    its two PM-shard shapes (the prior layer L13..L16 is not yet on `main`,
    so per AGENTS.md #29 these are kept as statement-level hypotheses; see the
    `_witness` theorems below for their satisfiability).
All K/V replication / attention / router-head reasoning is discharged
internally (K/V come from the L12 projection via `sm_pm_carry_5330_commute`). -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_router_commute_L17_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10517,
         denoteGraph_ringAttn pm_goal_3 initPM 10518])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5606 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10593,
         denoteGraph_ringAttn pm_goal_3 initPM 10594] := by
  have hattn := sm_pm_attention_L17_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5586).shape = [16, 64, 1024] := hPM 5586 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5595).shape = [1024, 1024] := hPM 5595 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10521).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L17, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10522).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L17, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10523).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L17]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10524).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L17]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10523
      = denoteGraph_ringAttn pm_goal_3 initPM 10523 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10523 1417 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10524
      = denoteGraph_ringAttn pm_goal_3 initPM 10524 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10524 1417 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10523
      = denoteGraph_ringAttn pm_goal_3 initPM 10523 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10523 1418 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10524
      = denoteGraph_ringAttn pm_goal_3 initPM 10524 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10524 1418 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10547).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L17_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_17 nR0_17 nR1_17 0 buddy_r0_17 (by decide)]
    have e0 : nR0_17.ins.getD 0 0 = 10523 := by decide
    have e1 : nR1_17.ins.getD 0 0 = 10524 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
         (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10548).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L17_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_17 nR0_17 nR1_17 1 buddy_r1_17 (by decide)]
    have e0 : nR0_17.ins.getD 0 0 = 10523 := by decide
    have e1 : nR1_17.ins.getD 0 0 = 10524 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
         (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L17_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L17_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L17
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L17
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L17_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L17_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L17_hbound_witness
