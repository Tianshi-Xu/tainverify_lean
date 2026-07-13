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


-- ================= L17 MoE carry (sm_pm_carry_5632_commute) =================
theorem br_pm_16363 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16363 = denoteGraph_ringAttn pm_goal_3 initPM 10517 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16363 10517 1411
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359, 16363], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10517 16363 [16359, 16363] 2 (by decide) (by decide))
    rfl

theorem br_pm_16371 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16371 = denoteGraph_ringAttn pm_goal_3 initPM 10518 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16371 10518 1412
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367, 16371], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10518 16371 [16367, 16371] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10591 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10591 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10589) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10589).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10591 10589 1453
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10589], outs := [10591, 10593, 10595], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 10589 10591 10593 10595 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10592 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10592 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10590) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10590).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10592 10590 1457
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10590], outs := [10592, 10594, 10596], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 10590 10592 10594 10596 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10601 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10601 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16398)
        (denoteGraph_ringAttn pm_goal_3 initPM 10591)
        (denoteGraph_ringAttn pm_goal_3 initPM 10593)
        [initPM 10597, initPM 10598] [initPM 10599, initPM 10600]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10601 16398 10591 10593 10597 10598 10599 10600 1461
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16398, 10591, 10593, 10597, 10598, 10599, 10600], outs := [10601], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16398 10591 10593 10597 10598 10599 10600 10601 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10597 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10598 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10599 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10600 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10602 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10602 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16421)
        (denoteGraph_ringAttn pm_goal_3 initPM 10592)
        (denoteGraph_ringAttn pm_goal_3 initPM 10594)
        [initPM 10597, initPM 10598] [initPM 10599, initPM 10600]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10602 16421 10592 10594 10597 10598 10599 10600 1464
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16421, 10592, 10594, 10597, 10598, 10599, 10600], outs := [10602], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16421 10592 10594 10597 10598 10599 10600 10602 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10597 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10598 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10599 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10600 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10603 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10603 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16402) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10603 16402 1438
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16402], outs := [10603], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16402 10603 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10604 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10604 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16425) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10604 16425 1442
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16425], outs := [10604], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16425 10604 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10607 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10607 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10603) (initPM 5612) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10607 10603 5612 1446
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10603, 5612], outs := [10607] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10603 5612 10607)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5612 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10608 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10608 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10604) (initPM 5612) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10608 10604 5612 1450
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10604, 5612], outs := [10608] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10604 5612 10608)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5612 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10613 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10613 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10607) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10613 10607 1454
    ({ rank := 0, op := "OpName.FW_view", ins := [10607], outs := [10613], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 10607 10613)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10614 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10614 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10608) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10614 10608 1458
    ({ rank := 1, op := "OpName.FW_view", ins := [10608], outs := [10614], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 10608 10614)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10615 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10615 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10613) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10615 10613 1462
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [10613], outs := [10615] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 10613 10615])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10616 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10616 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10614) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10616 10614 1465
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [10614], outs := [10616] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 10614 10616])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10617 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10617 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16406) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10617 16406 1439
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16406], outs := [10617], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16406 10617 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10618 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10618 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16429) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10618 16429 1443
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16429], outs := [10618], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16429 10618 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10621 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10621 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10617) (initPM 5617) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10621 10617 5617 1447
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10617, 5617], outs := [10621] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10617 5617 10621)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5617 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10622 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10622 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10618) (initPM 5617) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10622 10618 5617 1451
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10618, 5617], outs := [10622] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10618 5617 10622)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5617 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10631 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10631 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10621) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10631 10621 1455
    ({ rank := 0, op := "OpName.FW_view", ins := [10621], outs := [10631], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10621 10631)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10632 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10632 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10622) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10632 10622 1459
    ({ rank := 1, op := "OpName.FW_view", ins := [10622], outs := [10632], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10622 10632)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10635 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10635 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16410) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10635 16410 1440
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16410], outs := [10635], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16410 10635 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10636 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10636 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16433) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10636 16433 1444
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16433], outs := [10636], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16433 10636 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10639 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10639 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10635) (initPM 5621) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10639 10635 5621 1448
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10635, 5621], outs := [10639] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10635 5621 10639)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5621 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10640 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10640 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10636) (initPM 5621) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10640 10636 5621 1452
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10636, 5621], outs := [10640] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10636 5621 10640)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5621 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10649 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10649 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10639) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10649 10639 1456
    ({ rank := 0, op := "OpName.FW_view", ins := [10639], outs := [10649], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10639 10649)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10650 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10650 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10640) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10650 10640 1460
    ({ rank := 1, op := "OpName.FW_view", ins := [10640], outs := [10650], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10640 10650)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10653 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10653 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10631) (denoteGraph_ringAttn pm_goal_3 initPM 10649) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10653 10631 10649 1463
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [10631, 10649], outs := [10653] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 10631 10649 10653])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10654 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10654 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10632) (denoteGraph_ringAttn pm_goal_3 initPM 10650) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10654 10632 10650 1466
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [10632, 10650], outs := [10654] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 10632 10650 10654])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10655 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10655 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10653) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10655 10653 1467
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10653], outs := [10655], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10653 10655 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10656 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10656 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10654) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10656 10654 1468
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10654], outs := [10656], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10654 10656 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10661 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10661 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10655) (initPM 5626) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10661 10655 5626 1469
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10655, 5626], outs := [10661] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10655 5626 10661)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5626 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10662 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10662 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10656) (initPM 5626) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10662 10656 5626 1470
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10656, 5626], outs := [10662] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10656 5626 10662)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5626 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10671 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10671 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10661) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10671 10661 1471
    ({ rank := 0, op := "OpName.FW_view", ins := [10661], outs := [10671], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10661 10671)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10672 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10672 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10662) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10672 10662 1472
    ({ rank := 1, op := "OpName.FW_view", ins := [10662], outs := [10672], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10662 10672)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10675 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10675 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10615) (denoteGraph_ringAttn pm_goal_3 initPM 10671) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10675 10615 10671 1473
    ({ rank := 0, op := "OpName.FW_mul", ins := [10615, 10671], outs := [10675] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 10615 10671 10675])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10676 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10676 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10616) (denoteGraph_ringAttn pm_goal_3 initPM 10672) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10676 10616 10672 1474
    ({ rank := 1, op := "OpName.FW_mul", ins := [10616, 10672], outs := [10676] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 10616 10672 10676])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10679 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10679 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10601) (denoteGraph_ringAttn pm_goal_3 initPM 10675) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10679 10601 10675 1475
    ({ rank := 0, op := "OpName.FW_add", ins := [10601, 10675], outs := [10679] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 10601 10675 10679)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10680 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10680 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10602) (denoteGraph_ringAttn pm_goal_3 initPM 10676) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10680 10602 10676 1476
    ({ rank := 1, op := "OpName.FW_add", ins := [10602, 10676], outs := [10680] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 10602 10676 10680)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10685 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10685 =
      denoteGraph_ringAttn pm_goal_3 initPM 10679 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10685 10679 1477
    ({ rank := 0, op := "OpName.FW_float", ins := [10679], outs := [10685] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10679 10685 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10686 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10686 =
      denoteGraph_ringAttn pm_goal_3 initPM 10680 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10686 10680 1478
    ({ rank := 1, op := "OpName.FW_float", ins := [10680], outs := [10686] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10680 10686 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10689 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10689 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16379) (denoteGraph_ringAttn pm_goal_3 initPM 10685) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10689 16379 10685 1479
    ({ rank := 0, op := "OpName.FW_add", ins := [16379, 10685], outs := [10689] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16379 10685 10689)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10690 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10690 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16387) (denoteGraph_ringAttn pm_goal_3 initPM 10686) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10690 16387 10686 1480
    ({ rank := 1, op := "OpName.FW_add", ins := [16387, 10686], outs := [10690] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16387 10686 10690)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16379 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16379 =
      denoteGraph_ringAttn pm_goal_3 initPM 10577 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16379 10577 1431
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10577], outs := [16375, 16379], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 10577 16375 16379 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16387 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16387 =
      denoteGraph_ringAttn pm_goal_3 initPM 10578 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16387 10578 1432
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10578], outs := [16383, 16387], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 10578 16383 16387 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16398 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16398 =
      denoteGraph_ringAttn pm_goal_3 initPM 10581 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16398 10581 1435
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 10581 16394 16398 16402 16406 16410 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16402 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16402 =
      denoteGraph_ringAttn pm_goal_3 initPM 10581 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16402 10581 1435
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 10581 16394 16398 16402 16406 16410 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16406 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16406 =
      denoteGraph_ringAttn pm_goal_3 initPM 10581 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16406 10581 1435
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 10581 16394 16398 16402 16406 16410 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16410 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16410 =
      denoteGraph_ringAttn pm_goal_3 initPM 10581 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16410 10581 1435
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 10581 16394 16398 16402 16406 16410 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16421 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16421 =
      denoteGraph_ringAttn pm_goal_3 initPM 10582 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16421 10582 1436
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 10582 16417 16421 16425 16429 16433 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16425 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16425 =
      denoteGraph_ringAttn pm_goal_3 initPM 10582 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16425 10582 1436
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 10582 16417 16421 16425 16429 16433 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16429 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16429 =
      denoteGraph_ringAttn pm_goal_3 initPM 10582 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16429 10582 1436
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 10582 16417 16421 16425 16429 16433 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16433 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16433 =
      denoteGraph_ringAttn pm_goal_3 initPM 10582 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16433 10582 1436
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 10582 16417 16421 16425 16429 16433 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5605 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5605 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5604) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5604).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5605 5604 697
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5604], outs := [5605, 5606, 5607], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5604 5605 5606 5607 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5610 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5610 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8357)
        (denoteGraph_ringAttn sm_goal_3 initSM 5605)
        (denoteGraph_ringAttn sm_goal_3 initSM 5606)
        (initSM 5608) (initSM 5609) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5610 8357 5605 5606 5608 5609 701
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8357, 5605, 5606, 5608, 5609], outs := [5610], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8357 5605 5606 5608 5609 5610 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5608 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5609 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5611 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5611 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8361) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5611 8361 690
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8361], outs := [5611], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8361 5611 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5613 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5613 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5611) (initSM 5612) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5613 5611 5612 694
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5611, 5612], outs := [5613] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5611 5612 5613)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5612 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5614 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5614 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5613) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5614 5613 698
    ({ rank := 0, op := "OpName.FW_view", ins := [5613], outs := [5614], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5613 5614)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5615 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5615 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5614) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5615 5614 702
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5614], outs := [5615] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5614 5615])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5616 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5616 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8365) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5616 8365 691
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8365], outs := [5616], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8365 5616 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5618 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5618 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5616) (initSM 5617) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5618 5616 5617 695
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5616, 5617], outs := [5618] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5616 5617 5618)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5617 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5619 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5619 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5618) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5619 5618 699
    ({ rank := 0, op := "OpName.FW_view", ins := [5618], outs := [5619], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5618 5619)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5620 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5620 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8369) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5620 8369 692
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8369], outs := [5620], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8369 5620 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5622 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5622 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5620) (initSM 5621) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5622 5620 5621 696
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5620, 5621], outs := [5622] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5620 5621 5622)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5621 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5623 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5623 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5622) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5623 5622 700
    ({ rank := 0, op := "OpName.FW_view", ins := [5622], outs := [5623], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5622 5623)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5624 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5624 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5619) (denoteGraph_ringAttn sm_goal_3 initSM 5623) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5624 5619 5623 703
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5619, 5623], outs := [5624] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5619 5623 5624])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5625 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5625 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5624) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5625 5624 704
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5624], outs := [5625], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5624 5625 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5627 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5627 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5625) (initSM 5626) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5627 5625 5626 705
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5625, 5626], outs := [5627] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5625 5626 5627)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5626 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5628 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5628 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5627) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5628 5627 706
    ({ rank := 0, op := "OpName.FW_view", ins := [5627], outs := [5628], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5627 5628)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5629 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5629 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5615) (denoteGraph_ringAttn sm_goal_3 initSM 5628) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5629 5615 5628 707
    ({ rank := 0, op := "OpName.FW_mul", ins := [5615, 5628], outs := [5629] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5615 5628 5629])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5630 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5630 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5610) (denoteGraph_ringAttn sm_goal_3 initSM 5629) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5630 5610 5629 708
    ({ rank := 0, op := "OpName.FW_add", ins := [5610, 5629], outs := [5630] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5610 5629 5630)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5631 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5631 =
      denoteGraph_ringAttn sm_goal_3 initSM 5630 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5631 5630 709
    ({ rank := 0, op := "OpName.FW_float", ins := [5630], outs := [5631] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5630 5631 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5632 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8346) (denoteGraph_ringAttn sm_goal_3 initSM 5631) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5632 8346 5631 710
    ({ rank := 0, op := "OpName.FW_add", ins := [8346, 5631], outs := [5632] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8346 5631 5632)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8346 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8346 =
      denoteGraph_ringAttn sm_goal_3 initSM 5599 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8346 5599 686
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5599], outs := [8342, 8346], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5599 8342 8346 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8357 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8357 =
      denoteGraph_ringAttn sm_goal_3 initSM 5601 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8357 5601 688
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5601 8353 8357 8361 8365 8369 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8361 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8361 =
      denoteGraph_ringAttn sm_goal_3 initSM 5601 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8361 5601 688
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5601 8353 8357 8361 8365 8369 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8365 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8365 =
      denoteGraph_ringAttn sm_goal_3 initSM 5601 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8365 5601 688
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5601 8353 8357 8361 8365 8369 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8369 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8369 =
      denoteGraph_ringAttn sm_goal_3 initSM 5601 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8369 5601 688
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5601 8353 8357 8361 8365 8369 (by decide) (by decide) (by decide) (by decide))
    rfl







-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5599 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10577,
         denoteGraph_ringAttn pm_goal_3 initPM 10578])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5610 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10601,
         denoteGraph_ringAttn pm_goal_3 initPM 10602] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5600 = initPM 5600 := hb initGoal_5600 (by decide) rfl
  have hw5603sh : (initPM 5603).shape = [64, 1024] := by
    have hgh := hII initGoal_5603 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5603] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5608 : initSM 5608 = allGatherPrimDimN 0 2 0 [initPM 10597, initPM 10598] := by
    have hg := hII initGoal_5608 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5608, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10597) (initPM 10598) []
        (by rw [h_ss_pm 10597 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5609 : initSM 5609 = allGatherPrimDimN 0 2 0 [initPM 10599, initPM 10600] := by
    have hg := hII initGoal_5609 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5609, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10599) (initPM 10600) []
        (by rw [h_ss_pm 10599 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L17_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hrouter := sm_pm_router_commute_L17 initSM initPM hInit hcarry5599 h10577 h10578
  -- PM rms output shapes [2048, 1024]
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10581).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L17, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10582).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L17, rms_sh]; exact h10578
  -- PM nl output shapes [2048, 64]
  have h10589sh : (denoteGraph_ringAttn pm_goal_3 initPM 10589).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L17, denote_pm_goal_3_10583_L17, denote_pm_goal_3_10581_L17]
    exact nl_sh 2048 1024 64 _ (initPM 5603) (by rw [rms_sh]; exact h10577) hw5603sh
  have h10590sh : (denoteGraph_ringAttn pm_goal_3 initPM 10590).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L17, denote_pm_goal_3_10584_L17, denote_pm_goal_3_10582_L17]
    exact nl_sh 2048 1024 64 _ (initPM 5603) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5604).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10589sh
  -- MoE weight shapes
  have hw10597 : (initPM 10597).shape = [32,1024,1024] := h_ss_pm 10597 [32,1024,1024] (by decide)
  have hw10598 : (initPM 10598).shape = [32,1024,1024] := h_ss_pm 10598 [32,1024,1024] (by decide)
  have hw10599 : (initPM 10599).shape = [32,1024,512] := h_ss_pm 10599 [32,1024,512] (by decide)
  have hw10600 : (initPM 10600).shape = [32,1024,512] := h_ss_pm 10600 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10591canon : denoteGraph_ringAttn pm_goal_3 initPM 10591
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10589) 8 64).fst := by
    rw [br_pm_10591,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10589).shape.reverse.head?).getD 1 = 64 from by rw [h10589sh]; rfl]
  have h10592canon : denoteGraph_ringAttn pm_goal_3 initPM 10592
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10590) 8 64).fst := by
    rw [br_pm_10592,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10590).shape.reverse.head?).getD 1 = 64 from by rw [h10590sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10591sh : (denoteGraph_ringAttn pm_goal_3 initPM 10591).shape = [2048, 64] := by
    rw [h10591canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10589sh]; rfl)
  have h10592sh : (denoteGraph_ringAttn pm_goal_3 initPM 10592).shape = [2048, 64] := by
    rw [h10592canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10590sh]; rfl)
  have h10593canon : denoteGraph_ringAttn pm_goal_3 initPM 10593
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10589) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593_L17,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10589).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10589sh]; rfl]
  have h10594canon : denoteGraph_ringAttn pm_goal_3 initPM 10594
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10590) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594_L17,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10590).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10590sh]; rfl]
  have h10593sh : (denoteGraph_ringAttn pm_goal_3 initPM 10593).shape = [2048, 64] := by
    rw [h10593canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10589sh
  have h10594sh : (denoteGraph_ringAttn pm_goal_3 initPM 10594).shape = [2048, 64] := by
    rw [h10594canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10590sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 10581) (denoteGraph_ringAttn pm_goal_3 initPM 10582)
    (denoteGraph_ringAttn pm_goal_3 initPM 10591) (denoteGraph_ringAttn pm_goal_3 initPM 10592)
    (denoteGraph_ringAttn pm_goal_3 initPM 10593) (denoteGraph_ringAttn pm_goal_3 initPM 10594)
    (initPM 10597) (initPM 10598) (initPM 10599) (initPM 10600)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10581sh h10582sh h10591sh h10592sh h10593sh h10594sh hw10597 hw10598 hw10599 hw10600
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_10601, br_pm_10602, br_pm_16398, br_pm_16421,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5610, br_sm_8357, denote_sm_goal_3_5601_L17, br_sm_5605]
  rw [hrouter, h5608, h5609]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5604).shape.reverse.head?).getD 1 = 64 from by rw [hSM5604sh]; rfl]
  rw [hw5600, hcarry5599, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5600) 2048 1024 (by omega) (by omega) h10577 h10578]
  rw [← denote_pm_goal_3_10581_L17, ← denote_pm_goal_3_10582_L17]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10589sh h10590sh]
  rw [← h10591canon, ← h10592canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L17_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5599 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10577,
         denoteGraph_ringAttn pm_goal_3 initPM 10578])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5629
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10675,
           denoteGraph_ringAttn pm_goal_3 initPM 10676] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5600 = initPM 5600 := hb initGoal_5600 (by decide) rfl
  have hw5612 : initSM 5612 = initPM 5612 := hb initGoal_5612 (by decide) rfl
  have hw5617 : initSM 5617 = initPM 5617 := hb initGoal_5617 (by decide) rfl
  have hw5621 : initSM 5621 = initPM 5621 := hb initGoal_5621 (by decide) rfl
  have hw5626 : initSM 5626 = initPM 5626 := hb initGoal_5626 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5599) (initSM 5600)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10581,
           denoteGraph_ringAttn pm_goal_3 initPM 10582] := by
    rw [hcarry5599, hw5600,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5600) 2048 1024 (by omega) (by omega) h10577 h10578,
        ← denote_pm_goal_3_10581_L17, ← denote_pm_goal_3_10582_L17]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 10581 / 10582
  rw [br_pm_10675, br_pm_10676,
      br_pm_10615, br_pm_10613, br_pm_10607, br_pm_10603, br_pm_16402,
      br_pm_10671, br_pm_10661, br_pm_10655, br_pm_10653,
      br_pm_10631, br_pm_10621, br_pm_10617, br_pm_16406,
      br_pm_10649, br_pm_10639, br_pm_10635, br_pm_16410,
      br_pm_10616, br_pm_10614, br_pm_10608, br_pm_10604, br_pm_16425,
      br_pm_10672, br_pm_10662, br_pm_10656, br_pm_10654,
      br_pm_10632, br_pm_10622, br_pm_10618, br_pm_16429,
      br_pm_10650, br_pm_10640, br_pm_10636, br_pm_16433]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5601
  rw [br_sm_5629, br_sm_5615, br_sm_5614, br_sm_5613,
      br_sm_5611, br_sm_8361,
      br_sm_5628, br_sm_5627, br_sm_5625, br_sm_5624,
      br_sm_5619, br_sm_5618, br_sm_5616, br_sm_8365,
      br_sm_5623, br_sm_5622, br_sm_5620, br_sm_8369,
      denote_sm_goal_3_5601_L17]
  rw [hRMS, hw5612, hw5617, hw5621, hw5626]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 10581 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 10582 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581_L17, rms_sh]; exact h10577
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582_L17, rms_sh]; exact h10578
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5612).shape = [1, 1024] := h_ss_pm 5612 [1, 1024] (by decide)
  have hw29 : (initPM 5617).shape = [512, 1024] := h_ss_pm 5617 [512, 1024] (by decide)
  have hw33 : (initPM 5621).shape = [512, 1024] := h_ss_pm 5621 [512, 1024] (by decide)
  have hw38 : (initPM 5626).shape = [1024, 512] := h_ss_pm 5626 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5612) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5617) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5621) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5612)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5612)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5617)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5617)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5621)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5621)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5612), fw_linear (fw_view [2048, 1024] B) (initPM 5612)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5612)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5612))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5617), fw_linear (fw_view [2048, 1024] B) (initPM 5617)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5621), fw_linear (fw_view [2048, 1024] B) (initPM 5621)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5612)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5612)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5626) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621))))) (initPM 5626)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))))) (initPM 5626)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621))))) (initPM 5626), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))))) (initPM 5626)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621))))) (initPM 5626)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))))) (initPM 5626))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5612))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5612))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5621))))) (initPM 5626)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5617))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5621))))) (initPM 5626)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10689_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024] := by
  have h10517 := hbase345
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10573).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L17, denote_pm_goal_3_10569_L17]; rfl
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L17]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10517 h10573
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10581).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L17, rms_sh]; exact h10577
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 10601).shape = [2048, 1024] := by
    rw [br_pm_10601, br_pm_16398]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 10615).shape = [2048, 1] := by
    rw [br_pm_10615, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10613]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 10671).shape = [2048, 1024] := by
    rw [br_pm_10671]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 10675).shape = [2048, 1024] := by
    rw [br_pm_10675, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10601) (denoteGraph_ringAttn pm_goal_3 initPM 10675)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have h16379sh : (denoteGraph_ringAttn pm_goal_3 initPM 16379).shape = [2048, 1024] := by
    rw [br_pm_16379]; exact h10577
  have h10685sh : (denoteGraph_ringAttn pm_goal_3 initPM 10685).shape = [2048, 1024] := by
    rw [br_pm_10685, br_pm_10679]; exact hinnerA
  rw [br_pm_10689]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16379sh h10685sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10690_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024] := by
  have h10518 := hbase346
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10574).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L17, denote_pm_goal_3_10570_L17]; rfl
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L17]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10518 h10574
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10582).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L17, rms_sh]; exact h10578
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 10602).shape = [2048, 1024] := by
    rw [br_pm_10602, br_pm_16421]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 10616).shape = [2048, 1] := by
    rw [br_pm_10616, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10614]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 10672).shape = [2048, 1024] := by
    rw [br_pm_10672]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 10676).shape = [2048, 1024] := by
    rw [br_pm_10676, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10602) (denoteGraph_ringAttn pm_goal_3 initPM 10676)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  have h16387sh : (denoteGraph_ringAttn pm_goal_3 initPM 16387).shape = [2048, 1024] := by
    rw [br_pm_16387]; exact h10578
  have h10686sh : (denoteGraph_ringAttn pm_goal_3 initPM 10686).shape = [2048, 1024] := by
    rw [br_pm_10686, br_pm_10680]; exact hinnerB
  rw [br_pm_10690]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16387sh h10686sh

-- ===== carry_5632 =====
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_carry_5632_commute (initSM initPM : Store)
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
    denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10689,
         denoteGraph_ringAttn pm_goal_3 initPM 10690] := by
  have hattn := sm_pm_attention_L17_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5635 : (initPM 5586).shape = [16, 64, 1024] := hPM 5586 [16, 64, 1024] (by decide)
  have hw5644 : (initPM 5595).shape = [1024, 1024] := hPM 5595 [1024, 1024] (by decide)
  have h10693 : (denoteGraph_ringAttn pm_goal_3 initPM 10521).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L17, rms_sh]; exact h10517
  have h10694 : (denoteGraph_ringAttn pm_goal_3 initPM 10522).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L17, rms_sh]; exact h10518
  have h10695d : (denoteGraph_ringAttn pm_goal_3 initPM 10523).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L17]; exact ph_lin_shape_gen _ _ 2048 16 h10693 hw5635
  have h10696d : (denoteGraph_ringAttn pm_goal_3 initPM 10524).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L17]; exact ph_lin_shape_gen _ _ 2048 16 h10694 hw5635
  -- folded-store bridges at the two attention Q tids
  have b1487_10695 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10523
      = denoteGraph_ringAttn pm_goal_3 initPM 10523 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10523 1417 (by decide) (by decide)).symm
  have b1487_10696 : (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM 10524
      = denoteGraph_ringAttn pm_goal_3 initPM 10524 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10524 1417 (by decide) (by decide)).symm
  have b1488_10695 : (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10523
      = denoteGraph_ringAttn pm_goal_3 initPM 10523 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10523 1418 (by decide) (by decide)).symm
  have b1488_10696 : (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM 10524
      = denoteGraph_ringAttn pm_goal_3 initPM 10524 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10524 1418 (by decide) (by decide)).symm
  have h10719 : (denoteGraph_ringAttn pm_goal_3 initPM 10547).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L17_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_17 nR0_17 nR1_17 0 buddy_r0_17 (by decide)]
    have e0 : nR0_17.ins.getD 0 0 = 10523 := by decide
    have e1 : nR1_17.ins.getD 0 0 = 10524 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
         (pm_goal_3.nodes.take 1417).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1487_10695, b1487_10696]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10695d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10720 : (denoteGraph_ringAttn pm_goal_3 initPM 10548).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L17_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_17 nR0_17 nR1_17 1 buddy_r1_17 (by decide)]
    have e0 : nR0_17.ins.getD 0 0 = 10523 := by decide
    have e1 : nR1_17.ins.getD 0 0 = 10524 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_17.ins.getD 0 0),
         (pm_goal_3.nodes.take 1418).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_17.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1488_10695, b1488_10696]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10695d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl

  have hreshape := sm_pm_reshape_float_L17_commute initSM initPM hInit hattn h10719 h10720 hw5644
  have h10745 : (denoteGraph_ringAttn pm_goal_3 initPM 10573).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L17, denote_pm_goal_3_10569_L17]; rfl
  have h10746 : (denoteGraph_ringAttn pm_goal_3 initPM 10574).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L17, denote_pm_goal_3_10570_L17]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L17 initSM initPM hcarry5583 hreshape h10517 h10518 h10745 h10746
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10577).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L17]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10745
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10578).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L17]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10746
  have hgmm := sm_pm_moe_gmm_L17_commute initSM initPM hInit hPM hcarry5599 h10577 h10578
  have hgate := sm_pm_gate_mul_L17_commute initSM initPM hInit hPM hcarry5599 h10577 h10578
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10581).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L17, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10582).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L17, rms_sh]; exact h10578
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 10601).shape = [2048, 1024] := by
    rw [br_pm_10601, br_pm_16398]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 10602).shape = [2048, 1024] := by
    rw [br_pm_10602, br_pm_16421]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 10615).shape = [2048, 1] := by
    rw [br_pm_10615, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10613]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 10671).shape = [2048, 1024] := by
    rw [br_pm_10671]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 10675).shape = [2048, 1024] := by
    rw [br_pm_10675, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 10616).shape = [2048, 1] := by
    rw [br_pm_10616, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10614]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 10672).shape = [2048, 1024] := by
    rw [br_pm_10672]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 10676).shape = [2048, 1024] := by
    rw [br_pm_10676, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10601) (denoteGraph_ringAttn pm_goal_3 initPM 10675)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10602) (denoteGraph_ringAttn pm_goal_3 initPM 10676)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  -- === assemble ===
  rw [br_pm_10689, br_pm_16379, br_pm_10685, br_pm_10679,
      br_pm_10690, br_pm_16387, br_pm_10686, br_pm_10680]
  rw [br_sm_5632, br_sm_8346, br_sm_5631, br_sm_5630]
  rw [hcarry5599, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10601) (denoteGraph_ringAttn pm_goal_3 initPM 10602)
        (denoteGraph_ringAttn pm_goal_3 initPM 10675) (denoteGraph_ringAttn pm_goal_3 initPM 10676)
        h10601sh h10602sh h10675sh h10676sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10577) (denoteGraph_ringAttn pm_goal_3 initPM 10578)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10601) (denoteGraph_ringAttn pm_goal_3 initPM 10675))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10602) (denoteGraph_ringAttn pm_goal_3 initPM 10676))
        h10577 h10578 hinnerA hinnerB]

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L17
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L17
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L17_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L17_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L17_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L17_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10689_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10690_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5632_commute
