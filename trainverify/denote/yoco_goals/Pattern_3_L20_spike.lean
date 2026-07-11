/-
  Pattern_3_L20_spike.lean — L20 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L20-specific TIDs.  The L20 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L20's Q path
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

/-! ## L20 attention node declarations + buddy proofs.
SM attn node index 784; PM r0 = 1627; PM r1 = 1628. -/

def nSM_20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5734, 5735, 5736, 5737, 5738], outs := [5739],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11039, 5735, 5736, 5737, 5738], outs := [11063],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_20 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11040, 5735, 5736, 5737, 5738], outs := [11064],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_20 : ringAttnBuddies sm_goal_3 nSM_20 = [nSM_20] := by
  show (List.filter (fun m => decide (m.op = nSM_20.op) && decide (m.params = nSM_20.params) &&
      decide (m.ins.getD 3 0 = nSM_20.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_20.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_20]
  rw [show (List.filter (fun m => decide (m.op = nSM_20.op) && decide (m.params = nSM_20.params) &&
      decide (m.ins.getD 3 0 = nSM_20.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_20.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_20] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_20 : ringAttnBuddies pm_goal_3 nR0_20 = [nR0_20, nR1_20] := by
  show (List.filter (fun m => decide (m.op = nR0_20.op) && decide (m.params = nR0_20.params) &&
      decide (m.ins.getD 3 0 = nR0_20.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_20.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_20, nR1_20]
  rw [show (List.filter (fun m => decide (m.op = nR0_20.op) && decide (m.params = nR0_20.params) &&
      decide (m.ins.getD 3 0 = nR0_20.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_20.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_20, nR1_20] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_20 : ringAttnBuddies pm_goal_3 nR1_20 = [nR0_20, nR1_20] := by
  show (List.filter (fun m => decide (m.op = nR1_20.op) && decide (m.params = nR1_20.params) &&
      decide (m.ins.getD 3 0 = nR1_20.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_20.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_20, nR1_20]
  rw [show (List.filter (fun m => decide (m.op = nR1_20.op) && decide (m.params = nR1_20.params) &&
      decide (m.ins.getD 3 0 = nR1_20.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_20.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_20, nR1_20] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L20 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L20_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5739
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_20 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5739
      = (sm_goal_3.nodes.take 785).foldl (applyNodeRingAttn sm_goal_3) initSM 5739 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5739 785 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 785 = sm_goal_3.nodes.take 784 ++ [nSM_20] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5734 5735 5736 5737 5738 5739 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L20_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11063
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_20 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11063
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 11063 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11063 1628 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1628 = pm_goal_3.nodes.take 1627 ++ [nR0_20] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 11039 5735 5736 5737 5738 11063 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L20_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11064
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_20 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11064
      = (pm_goal_3.nodes.take 1629).foldl (applyNodeRingAttn pm_goal_3) initPM 11064 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11064 1629 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1629 = pm_goal_3.nodes.take 1628 ++ [nR1_20] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 11040 5735 5736 5737 5738 11064 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L20) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5732 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5730) (initSM 5731) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5732 8451 5731 782
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8451, 5731], outs := [5732] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8451 5731 5732)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8451 5730 781
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8451, 8455], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5730 8451 [8451, 8455] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5731 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5734 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5732) (initSM 5733) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5734 5732 5733 783
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5732, 5733], outs := [5734] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5732 5733 5734 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5733 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5740 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5739) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5740 5739 785
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5739], outs := [5740], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5739 5740 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5741 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5740) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5741 5740 786
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5740], outs := [5741], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5740 5741 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5743 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5741) (initSM 5742) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5743 5741 5742 787
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5741, 5742], outs := [5743] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5741 5742 5743)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5742 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5744 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5743) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5744 5743 788
    ({ rank := 0, op := "OpName.FW_view", ins := [5743], outs := [5744], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5743 5744)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5745 =
      denoteGraph_ringAttn sm_goal_3 initSM 5744 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5745 5744 789
    ({ rank := 0, op := "OpName.FW_float", ins := [5744], outs := [5745] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5744 5745 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5746 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5730)
        (denoteGraph_ringAttn sm_goal_3 initSM 5745) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8455 = denoteGraph_ringAttn sm_goal_3 initSM 5730 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8455 5730 781
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8451, 8455], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5730 8455 [8451, 8455] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5746 8455 5745 790
    ({ rank := 0, op := "OpName.FW_add", ins := [8455, 5745], outs := [5746] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8455 5745 5746)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5748 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5746) (initSM 5747) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5748 8459 5747 792
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8459, 5747], outs := [5748] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8459 5747 5748)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8459 5746 791
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5746], outs := [8459, 8463], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5746 8459 [8459, 8463] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5747 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5749 =
      denoteGraph_ringAttn sm_goal_3 initSM 5748 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5749 8470 794
    ({ rank := 0, op := "OpName.FW_float", ins := [8470], outs := [5749] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8470 5749 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8470 5748 793
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5748 8470 [8470, 8474, 8478, 8482, 8486] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5751 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5749) (initSM 5750) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5751 5749 5750 798
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5749, 5750], outs := [5751] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5749 5750 5751 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5750 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5753 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5751) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5751).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5753 5751 802
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5751], outs := [5752, 5753, 5754], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5751 5752 5753 5754 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5735 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5735 8065 488
    ({ rank := 0, op := "OpName.FW_to", ins := [8065], outs := [5735] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8065 5735 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8065 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8065 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5736 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5736 8123 500
    ({ rank := 0, op := "OpName.FW_to", ins := [8123], outs := [5736] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8123 5736 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8123 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8123 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L20) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11037 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11033) (initPM 5731) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11037 16593 5731 1623
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16593, 5731], outs := [11037] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16593 5731 11037)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16593 11033 1621
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593, 16597], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11033 16593 [16593, 16597] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5731 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11039 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11037) (initPM 5733) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11039 11037 5733 1625
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11037, 5733], outs := [11039] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 11037 5733 11039 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5733 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11065 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11063) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11065 11063 1629
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11063], outs := [11065], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11063 11065 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11071 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11065) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11071 11065 1631
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11065], outs := [11071], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11065 11071 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11075 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11071) (initPM 5742) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11075 11071 5742 1633
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11071, 5742], outs := [11075] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11071 5742 11075)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5742 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11085 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11075) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11085 11075 1635
    ({ rank := 0, op := "OpName.FW_view", ins := [11075], outs := [11085], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11075 11085)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11089 =
      denoteGraph_ringAttn pm_goal_3 initPM 11085 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11089 11085 1637
    ({ rank := 0, op := "OpName.FW_float", ins := [11085], outs := [11089] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11085 11089 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11093 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11033)
        (denoteGraph_ringAttn pm_goal_3 initPM 11089) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16597 = denoteGraph_ringAttn pm_goal_3 initPM 11033 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16597 11033 1621
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593, 16597], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11033 16597 [16593, 16597] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11093 16597 11089 1639
    ({ rank := 0, op := "OpName.FW_add", ins := [16597, 11089], outs := [11093] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16597 11089 11093)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11097 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11093) (initPM 5747) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11097 16609 5747 1643
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16609, 5747], outs := [11097] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16609 5747 11097)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16609 11093 1641
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11093], outs := [16609, 16613], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11093 16609 [16609, 16613] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5747 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11099 =
      denoteGraph_ringAttn pm_goal_3 initPM 11097 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11099 16628 1647
    ({ rank := 0, op := "OpName.FW_float", ins := [16628], outs := [11099] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16628 11099 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16628 11097 1645
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11097 16628 [16628, 16632, 16636, 16640, 16644] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11105 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11099) (initPM 5750) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11105 11099 5750 1655
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [11099, 5750], outs := [11105] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 11099 5750 11105 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5750 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11109 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11105) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11105).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11109 11105 1663
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11105], outs := [11107, 11109, 11111], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 11105 11107 11109 11111 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11038 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11034) (initPM 5731) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11038 16601 5731 1624
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16601, 5731], outs := [11038] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16601 5731 11038)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16601 11034 1622
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601, 16605], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11034 16601 [16601, 16605] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5731 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11040 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11038) (initPM 5733) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11040 11038 5733 1626
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11038, 5733], outs := [11040] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 11038 5733 11040 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5733 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11066 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11064) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11066 11064 1630
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11064], outs := [11066], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11064 11066 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11072 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11066) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11072 11066 1632
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11066], outs := [11072], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11066 11072 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11076 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11072) (initPM 5742) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11076 11072 5742 1634
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11072, 5742], outs := [11076] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11072 5742 11076)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5742 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11086 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11076) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11086 11076 1636
    ({ rank := 1, op := "OpName.FW_view", ins := [11076], outs := [11086], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11076 11086)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11090 =
      denoteGraph_ringAttn pm_goal_3 initPM 11086 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11090 11086 1638
    ({ rank := 1, op := "OpName.FW_float", ins := [11086], outs := [11090] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11086 11090 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11094 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11034)
        (denoteGraph_ringAttn pm_goal_3 initPM 11090) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16605 = denoteGraph_ringAttn pm_goal_3 initPM 11034 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16605 11034 1622
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601, 16605], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11034 16605 [16601, 16605] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11094 16605 11090 1640
    ({ rank := 1, op := "OpName.FW_add", ins := [16605, 11090], outs := [11094] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16605 11090 11094)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11098 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11094) (initPM 5747) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11098 16617 5747 1644
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16617, 5747], outs := [11098] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16617 5747 11098)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16617 11094 1642
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11094], outs := [16617, 16621], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11094 16617 [16617, 16621] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5747 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11100 =
      denoteGraph_ringAttn pm_goal_3 initPM 11098 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11100 16651 1651
    ({ rank := 1, op := "OpName.FW_float", ins := [16651], outs := [11100] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16651 11100 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16651 11098 1646
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11098 16651 [16651, 16655, 16659, 16663, 16667] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11106 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11100) (initPM 5750) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11106 11100 5750 1659
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [11100, 5750], outs := [11106] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 11100 5750 11106 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5750 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11110 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11106) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11106).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11110 11106 1667
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11106], outs := [11108, 11110, 11112], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 11106 11108 11110 11112 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5735 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5735 15847 1039
    ({ rank := 1, op := "OpName.FW_to", ins := [15847], outs := [5735] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15847 5735 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15847 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15847 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5736 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5736 15953 1063
    ({ rank := 1, op := "OpName.FW_to", ins := [15953], outs := [5736] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15953 5736 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15953 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15953 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L20 commute theorems -/

-- Q sharding commute: SM 5734 = allGather0[PM 11039, PM 11040].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11033,
         denoteGraph_ringAttn pm_goal_3 initPM 11034])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024])
    (hw5586 : (initPM 5733).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5734 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11039,
         denoteGraph_ringAttn pm_goal_3 initPM 11040] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5731 = initPM 5731 := hb initGoal_5731 (by decide) rfl
  have hw5586e : initSM 5733 = initPM 5733 := hb initGoal_5733 (by decide) rfl
  rw [denote_sm_goal_3_5587, denote_sm_goal_3_5585,
      denote_pm_goal_3_10523, denote_pm_goal_3_10521,
      denote_pm_goal_3_10524, denote_pm_goal_3_10522]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11033) (initPM 5731)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11034) (initPM 5731)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5731) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5733) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5735).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5736).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589, denote_pm_goal_3_5336]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))

-- K/V replication (cross-graph, full tensor): SM 5735 = PM 5735, SM 5736 = PM 5736.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5735 =
      denoteGraph_ringAttn pm_goal_3 initPM 5735 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588, denote_pm_goal_3_5588, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5736 =
      denoteGraph_ringAttn pm_goal_3 initPM 5736 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589, denote_pm_goal_3_5589, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L20 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L20_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11033,
         denoteGraph_ringAttn pm_goal_3 initPM 11034])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5738)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5739 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11063,
         denoteGraph_ringAttn pm_goal_3 initPM 11064] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5733).shape = [16, 64, 1024] := hPM 5733 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L20_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L20_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L20_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape initPM hPM
  have hVsh := pm_5589_shape initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11037).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11038).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 11039).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 11040).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5734).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5734).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5735).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5736).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 784)
  have bSM5587 : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5734 = denoteGraph_ringAttn sm_goal_3 initSM 5734 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5734 784 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5735 = denoteGraph_ringAttn sm_goal_3 initSM 5735 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5735 784 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5736 = denoteGraph_ringAttn sm_goal_3 initSM 5736 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5736 784 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1627)
  have bPM10523 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11039 = denoteGraph_ringAttn pm_goal_3 initPM 11039 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11039 1627 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11040 = denoteGraph_ringAttn pm_goal_3 initPM 11040 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11040 1627 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5735 = denoteGraph_ringAttn pm_goal_3 initPM 5735 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5735 1627 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5736 = denoteGraph_ringAttn pm_goal_3 initPM 5736 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5736 1627 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5737 = initSM 5737 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 784) initSM 5737 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5738 = initSM 5738 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 784) initSM 5738 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5737 = initPM 5737 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1627) initPM 5737 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5738 = initPM 5738 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1627) initPM 5738 (by decide) (by decide)
  have hw5590 : initSM 5737 = initPM 5737 := hb initGoal_5737 (by decide) rfl
  have hw5591 : initSM 5738 = initPM 5738 := hb initGoal_5738 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5734).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5735).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5736).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 0 0),
        (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5734 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11039,
        (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11040]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5735 =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5735
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5736 =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5736
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5735).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5736).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5738)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5737 =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5737
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_20.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM 5738 =
      (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5738
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 0 0),
       (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11039,
       (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11040]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 0 0),
          (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 1 0),
          (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 2 0),
          (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 4 0))
        (nR0_20.params.getD 0 1) (nR0_20.params.getD 1 1) (nR0_20.params.getD 2 1) (nR0_20.params.getD 3 1)
        (decide (nR0_20.params.getD 4 0 ≠ 0)) (nR0_20.params.getD 5 0)).shape
        = [2 * 2048, nR0_20.params.getD 0 1, nR0_20.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1627 -> take 1628)
  have e10523 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11039
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 11039 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11039 1627 1628 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11040
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 11040 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11040 1627 1628 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5735
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 5735 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5735 1627 1628 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5736
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 5736 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5736 1627 1628 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5737
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 5737 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5737 1627 1628 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 5738
      = (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 5738 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5738 1627 1628 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_20
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_20 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_20]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_20]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_20]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 784).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_20 nR0_20 nR1_20 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_20 buddy_r0_20 buddy_r1_20 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L20_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L20_r0_bridge, ← denote_pm_attn_L20_r1_bridge]


/-! ## L20 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5739 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11063,
         denoteGraph_ringAttn pm_goal_3 initPM 11064])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11063).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11064).shape = [2048, 16, 64])
    (hw5595 : (initPM 5742).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5745 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11089,
         denoteGraph_ringAttn pm_goal_3 initPM 11090] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5742 = initPM 5742 := hb initGoal_5742 (by decide) rfl
  rw [denote_sm_goal_3_5598, denote_sm_goal_3_5597, denote_sm_goal_3_5596,
      denote_sm_goal_3_5594, denote_sm_goal_3_5593,
      denote_pm_goal_3_10573, denote_pm_goal_3_10569, denote_pm_goal_3_10559,
      denote_pm_goal_3_10555, denote_pm_goal_3_10549,
      denote_pm_goal_3_10574, denote_pm_goal_3_10570, denote_pm_goal_3_10560,
      denote_pm_goal_3_10556, denote_pm_goal_3_10550]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11063))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11064))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5742) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11063))) (initPM 5742)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11064))) (initPM 5742)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11063))) (initPM 5742),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11064))) (initPM 5742)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11033,
         denoteGraph_ringAttn pm_goal_3 initPM 11034])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5745 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11089,
         denoteGraph_ringAttn pm_goal_3 initPM 11090])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11089).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11090).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5746 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11093,
         denoteGraph_ringAttn pm_goal_3 initPM 11094] := by
  rw [denote_sm_goal_3_5599, denote_pm_goal_3_10577, denote_pm_goal_3_10578]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5746 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11093,
         denoteGraph_ringAttn pm_goal_3 initPM 11094])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5751 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11105,
         denoteGraph_ringAttn pm_goal_3 initPM 11106] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5747 = initPM 5747 := hb initGoal_5747 (by decide) rfl
  have hw5603 : initSM 5750 = initPM 5750 := hb initGoal_5750 (by decide) rfl
  have hw5603sh : (initPM 5750).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5750 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5750] using hsh
  rw [denote_sm_goal_3_5604, denote_sm_goal_3_5602, denote_sm_goal_3_5601,
      denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581,
      denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5747) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11093) (initPM 5747)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11094) (initPM 5747)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5750) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L20 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5746 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11093,
         denoteGraph_ringAttn pm_goal_3 initPM 11094])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5753 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11109,
         denoteGraph_ringAttn pm_goal_3 initPM 11110] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5750).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5750 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5750] using hsh
  have hnl := sm_pm_nl_L20_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 11105).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581]
    exact nl_sh 2048 1024 64 _ (initPM 5750) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 11106).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
    exact nl_sh 2048 1024 64 _ (initPM 5750) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5751).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606, denote_pm_goal_3_10593, denote_pm_goal_3_10594]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5751).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11105).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11106).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L20 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L20_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11033,
         denoteGraph_ringAttn pm_goal_3 initPM 11034])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5739 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11063,
         denoteGraph_ringAttn pm_goal_3 initPM 11064])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11063).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11064).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024])
    (hw5595 : (initPM 5742).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5753 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11109,
         denoteGraph_ringAttn pm_goal_3 initPM 11110] := by
  have hreshape := sm_pm_reshape_float_L20_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11089).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573, denote_pm_goal_3_10569]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11090).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574, denote_pm_goal_3_10570]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L20 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L20 router — fully assembled

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
theorem sm_pm_router_commute_L20_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5738)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11033,
         denoteGraph_ringAttn pm_goal_3 initPM 11034])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5753 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11109,
         denoteGraph_ringAttn pm_goal_3 initPM 11110] := by
  have hattn := sm_pm_attention_L20_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5733).shape = [16, 64, 1024] := hPM 5733 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5742).shape = [1024, 1024] := hPM 5742 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11037).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11038).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 11039).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 11040).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11039
      = denoteGraph_ringAttn pm_goal_3 initPM 11039 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11039 1627 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM 11040
      = denoteGraph_ringAttn pm_goal_3 initPM 11040 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11040 1627 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 11039
      = denoteGraph_ringAttn pm_goal_3 initPM 11039 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11039 1628 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM 11040
      = denoteGraph_ringAttn pm_goal_3 initPM 11040 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11040 1628 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11063).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L20_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_20 nR0_20 nR1_20 0 buddy_r0_20 (by decide)]
    have e0 : nR0_20.ins.getD 0 0 = 11039 := by decide
    have e1 : nR1_20.ins.getD 0 0 = 11040 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 0 0),
         (pm_goal_3.nodes.take 1627).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11064).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L20_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_20 nR0_20 nR1_20 1 buddy_r1_20 (by decide)]
    have e0 : nR0_20.ins.getD 0 0 = 11039 := by decide
    have e1 : nR1_20.ins.getD 0 0 = 11040 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_20.ins.getD 0 0),
         (pm_goal_3.nodes.take 1628).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_20.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L20_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L20_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5738)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L20
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L20_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L20_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L20_hbound_witness
