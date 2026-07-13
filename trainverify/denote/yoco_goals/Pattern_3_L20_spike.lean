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
theorem denote_sm_goal_3_5585_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5587_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5593_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5594_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5596_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5597_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5598_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5599_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5601_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5602_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5604_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5606_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5588_L20 (initSM : Store) :
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
theorem denote_sm_goal_3_5589_L20 (initSM : Store) :
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
theorem denote_pm_goal_3_10521_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10523_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10549_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10555_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10559_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10569_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10573_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10577_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10581_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10583_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10589_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10593_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10522_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10524_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10550_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10556_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10560_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10570_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10574_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10578_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10582_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10584_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10590_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_10594_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_5588_L20 (initPM : Store) :
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
theorem denote_pm_goal_3_5589_L20 (initPM : Store) :
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
  rw [denote_sm_goal_3_5587_L20, denote_sm_goal_3_5585_L20,
      denote_pm_goal_3_10523_L20, denote_pm_goal_3_10521_L20,
      denote_pm_goal_3_10524_L20, denote_pm_goal_3_10522_L20]
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
theorem pm_5588_shape_L20 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5735).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588_L20, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape_L20 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5736).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589_L20, denote_pm_goal_3_5336]
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
  rw [denote_sm_goal_3_5588_L20, denote_pm_goal_3_5588_L20, ← denote_sm_goal_3_5343,
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
  rw [denote_sm_goal_3_5589_L20, denote_pm_goal_3_5589_L20, ← denote_sm_goal_3_5344,
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
  have hKsh := pm_5588_shape_L20 initPM hPM
  have hVsh := pm_5589_shape_L20 initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11037).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L20, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11038).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L20, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 11039).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L20]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 11040).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L20]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
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
  rw [denote_sm_goal_3_5598_L20, denote_sm_goal_3_5597_L20, denote_sm_goal_3_5596_L20,
      denote_sm_goal_3_5594_L20, denote_sm_goal_3_5593_L20,
      denote_pm_goal_3_10573_L20, denote_pm_goal_3_10569_L20, denote_pm_goal_3_10559_L20,
      denote_pm_goal_3_10555_L20, denote_pm_goal_3_10549_L20,
      denote_pm_goal_3_10574_L20, denote_pm_goal_3_10570_L20, denote_pm_goal_3_10560_L20,
      denote_pm_goal_3_10556_L20, denote_pm_goal_3_10550_L20]
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
theorem sm_pm_carry_5599_commute_L20 (initSM initPM : Store)
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
  rw [denote_sm_goal_3_5599_L20, denote_pm_goal_3_10577_L20, denote_pm_goal_3_10578_L20]
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
  rw [denote_sm_goal_3_5604_L20, denote_sm_goal_3_5602_L20, denote_sm_goal_3_5601_L20,
      denote_pm_goal_3_10589_L20, denote_pm_goal_3_10583_L20, denote_pm_goal_3_10581_L20,
      denote_pm_goal_3_10590_L20, denote_pm_goal_3_10584_L20, denote_pm_goal_3_10582_L20]
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
    rw [denote_pm_goal_3_10589_L20, denote_pm_goal_3_10583_L20, denote_pm_goal_3_10581_L20]
    exact nl_sh 2048 1024 64 _ (initPM 5750) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 11106).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L20, denote_pm_goal_3_10584_L20, denote_pm_goal_3_10582_L20]
    exact nl_sh 2048 1024 64 _ (initPM 5750) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5751).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606_L20, denote_pm_goal_3_10593_L20, denote_pm_goal_3_10594_L20]
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
    rw [denote_pm_goal_3_10573_L20, denote_pm_goal_3_10569_L20]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11090).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L20, denote_pm_goal_3_10570_L20]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L20 initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L20]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L20]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
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
    rw [denote_pm_goal_3_10521_L20, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11038).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L20, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 11039).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L20]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 11040).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L20]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
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



-- ================= L20 MoE carry (sm_pm_carry_5779_commute) =================
theorem br_pm_16597 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16597 = denoteGraph_ringAttn pm_goal_3 initPM 11033 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16597 11033 1621
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593, 16597], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11033 16597 [16593, 16597] 2 (by decide) (by decide))
    rfl

theorem br_pm_16605 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16605 = denoteGraph_ringAttn pm_goal_3 initPM 11034 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16605 11034 1622
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601, 16605], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11034 16605 [16601, 16605] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11107 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11107 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11105) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 11105).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11107 11105 1663
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11105], outs := [11107, 11109, 11111], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 11105 11107 11109 11111 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11108 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11108 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11106) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 11106).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11108 11106 1667
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11106], outs := [11108, 11110, 11112], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 11106 11108 11110 11112 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11117 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11117 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16632)
        (denoteGraph_ringAttn pm_goal_3 initPM 11107)
        (denoteGraph_ringAttn pm_goal_3 initPM 11109)
        [initPM 11113, initPM 11114] [initPM 11115, initPM 11116]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 11117 16632 11107 11109 11113 11114 11115 11116 1671
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16632, 11107, 11109, 11113, 11114, 11115, 11116], outs := [11117], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16632 11107 11109 11113 11114 11115 11116 11117 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11113 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11114 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11115 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11116 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11118 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11118 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16655)
        (denoteGraph_ringAttn pm_goal_3 initPM 11108)
        (denoteGraph_ringAttn pm_goal_3 initPM 11110)
        [initPM 11113, initPM 11114] [initPM 11115, initPM 11116]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 11118 16655 11108 11110 11113 11114 11115 11116 1674
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16655, 11108, 11110, 11113, 11114, 11115, 11116], outs := [11118], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16655 11108 11110 11113 11114 11115 11116 11118 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11113 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11114 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11115 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11116 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11119 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11119 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16636) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11119 16636 1648
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16636], outs := [11119], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16636 11119 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11120 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11120 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16659) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11120 16659 1652
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16659], outs := [11120], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16659 11120 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11123 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11123 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11119) (initPM 5759) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11123 11119 5759 1656
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11119, 5759], outs := [11123] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11119 5759 11123)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5759 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11124 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11124 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11120) (initPM 5759) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11124 11120 5759 1660
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11120, 5759], outs := [11124] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11120 5759 11124)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5759 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11129 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11129 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 11123) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11129 11123 1664
    ({ rank := 0, op := "OpName.FW_view", ins := [11123], outs := [11129], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 11123 11129)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11130 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11130 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 11124) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11130 11124 1668
    ({ rank := 1, op := "OpName.FW_view", ins := [11124], outs := [11130], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 11124 11130)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11131 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11131 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 11129) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11131 11129 1672
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [11129], outs := [11131] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 11129 11131])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11132 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11132 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 11130) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11132 11130 1675
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [11130], outs := [11132] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 11130 11132])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11133 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11133 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16640) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11133 16640 1649
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16640], outs := [11133], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16640 11133 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11134 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11134 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16663) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11134 16663 1653
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16663], outs := [11134], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16663 11134 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11137 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11137 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11133) (initPM 5764) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11137 11133 5764 1657
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11133, 5764], outs := [11137] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11133 5764 11137)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5764 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11138 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11138 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11134) (initPM 5764) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11138 11134 5764 1661
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11134, 5764], outs := [11138] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11134 5764 11138)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5764 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11147 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11147 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11137) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11147 11137 1665
    ({ rank := 0, op := "OpName.FW_view", ins := [11137], outs := [11147], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 11137 11147)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11148 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11148 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11138) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11148 11138 1669
    ({ rank := 1, op := "OpName.FW_view", ins := [11138], outs := [11148], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 11138 11148)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11151 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11151 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16644) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11151 16644 1650
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16644], outs := [11151], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16644 11151 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11152 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11152 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16667) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11152 16667 1654
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16667], outs := [11152], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16667 11152 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11155 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11155 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11151) (initPM 5768) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11155 11151 5768 1658
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11151, 5768], outs := [11155] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11151 5768 11155)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5768 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11156 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11156 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11152) (initPM 5768) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11156 11152 5768 1662
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11152, 5768], outs := [11156] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11152 5768 11156)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5768 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11165 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11165 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11155) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11165 11155 1666
    ({ rank := 0, op := "OpName.FW_view", ins := [11155], outs := [11165], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 11155 11165)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11166 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11166 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11156) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11166 11156 1670
    ({ rank := 1, op := "OpName.FW_view", ins := [11156], outs := [11166], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 11156 11166)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11169 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11169 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 11147) (denoteGraph_ringAttn pm_goal_3 initPM 11165) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11169 11147 11165 1673
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [11147, 11165], outs := [11169] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 11147 11165 11169])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11170 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11170 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 11148) (denoteGraph_ringAttn pm_goal_3 initPM 11166) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11170 11148 11166 1676
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [11148, 11166], outs := [11170] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 11148 11166 11170])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11171 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11171 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11169) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11171 11169 1677
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11169], outs := [11171], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11169 11171 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11172 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11172 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11170) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11172 11170 1678
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11170], outs := [11172], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11170 11172 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11177 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11177 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11171) (initPM 5773) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11177 11171 5773 1679
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11171, 5773], outs := [11177] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11171 5773 11177)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5773 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11178 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11178 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11172) (initPM 5773) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11178 11172 5773 1680
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11172, 5773], outs := [11178] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11172 5773 11178)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5773 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11187 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11187 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11177) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11187 11177 1681
    ({ rank := 0, op := "OpName.FW_view", ins := [11177], outs := [11187], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11177 11187)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11188 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11188 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11178) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11188 11178 1682
    ({ rank := 1, op := "OpName.FW_view", ins := [11178], outs := [11188], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11178 11188)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11191 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11191 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 11131) (denoteGraph_ringAttn pm_goal_3 initPM 11187) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11191 11131 11187 1683
    ({ rank := 0, op := "OpName.FW_mul", ins := [11131, 11187], outs := [11191] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 11131 11187 11191])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11192 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11192 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 11132) (denoteGraph_ringAttn pm_goal_3 initPM 11188) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11192 11132 11188 1684
    ({ rank := 1, op := "OpName.FW_mul", ins := [11132, 11188], outs := [11192] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 11132 11188 11192])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11195 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11195 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11117) (denoteGraph_ringAttn pm_goal_3 initPM 11191) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11195 11117 11191 1685
    ({ rank := 0, op := "OpName.FW_add", ins := [11117, 11191], outs := [11195] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 11117 11191 11195)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11196 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11196 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11118) (denoteGraph_ringAttn pm_goal_3 initPM 11192) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11196 11118 11192 1686
    ({ rank := 1, op := "OpName.FW_add", ins := [11118, 11192], outs := [11196] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 11118 11192 11196)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11201 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11201 =
      denoteGraph_ringAttn pm_goal_3 initPM 11195 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11201 11195 1687
    ({ rank := 0, op := "OpName.FW_float", ins := [11195], outs := [11201] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11195 11201 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11202 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11202 =
      denoteGraph_ringAttn pm_goal_3 initPM 11196 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11202 11196 1688
    ({ rank := 1, op := "OpName.FW_float", ins := [11196], outs := [11202] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11196 11202 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11205 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11205 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16613) (denoteGraph_ringAttn pm_goal_3 initPM 11201) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11205 16613 11201 1689
    ({ rank := 0, op := "OpName.FW_add", ins := [16613, 11201], outs := [11205] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16613 11201 11205)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11206 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11206 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16621) (denoteGraph_ringAttn pm_goal_3 initPM 11202) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11206 16621 11202 1690
    ({ rank := 1, op := "OpName.FW_add", ins := [16621, 11202], outs := [11206] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16621 11202 11206)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16613 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16613 =
      denoteGraph_ringAttn pm_goal_3 initPM 11093 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16613 11093 1641
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11093], outs := [16609, 16613], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 11093 16609 16613 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16621 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16621 =
      denoteGraph_ringAttn pm_goal_3 initPM 11094 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16621 11094 1642
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11094], outs := [16617, 16621], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 11094 16617 16621 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16632 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16632 =
      denoteGraph_ringAttn pm_goal_3 initPM 11097 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16632 11097 1645
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 11097 16628 16632 16636 16640 16644 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16636 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16636 =
      denoteGraph_ringAttn pm_goal_3 initPM 11097 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16636 11097 1645
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 11097 16628 16632 16636 16640 16644 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16640 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16640 =
      denoteGraph_ringAttn pm_goal_3 initPM 11097 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16640 11097 1645
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 11097 16628 16632 16636 16640 16644 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16644 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16644 =
      denoteGraph_ringAttn pm_goal_3 initPM 11097 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16644 11097 1645
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 11097 16628 16632 16636 16640 16644 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16655 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16655 =
      denoteGraph_ringAttn pm_goal_3 initPM 11098 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16655 11098 1646
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 11098 16651 16655 16659 16663 16667 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16659 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16659 =
      denoteGraph_ringAttn pm_goal_3 initPM 11098 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16659 11098 1646
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 11098 16651 16655 16659 16663 16667 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16663 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16663 =
      denoteGraph_ringAttn pm_goal_3 initPM 11098 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16663 11098 1646
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 11098 16651 16655 16659 16663 16667 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16667 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16667 =
      denoteGraph_ringAttn pm_goal_3 initPM 11098 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16667 11098 1646
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 11098 16651 16655 16659 16663 16667 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5752 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5752 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5751) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5751).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5752 5751 802
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5751], outs := [5752, 5753, 5754], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5751 5752 5753 5754 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5757 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5757 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8474)
        (denoteGraph_ringAttn sm_goal_3 initSM 5752)
        (denoteGraph_ringAttn sm_goal_3 initSM 5753)
        (initSM 5755) (initSM 5756) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5757 8474 5752 5753 5755 5756 806
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8474, 5752, 5753, 5755, 5756], outs := [5757], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8474 5752 5753 5755 5756 5757 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5755 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5756 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5758 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5758 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8478) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5758 8478 795
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8478], outs := [5758], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8478 5758 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5760 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5760 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5758) (initSM 5759) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5760 5758 5759 799
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5758, 5759], outs := [5760] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5758 5759 5760)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5759 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5761 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5761 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5760) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5761 5760 803
    ({ rank := 0, op := "OpName.FW_view", ins := [5760], outs := [5761], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5760 5761)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5762 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5762 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5761) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5762 5761 807
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5761], outs := [5762] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5761 5762])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5763 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5763 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8482) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5763 8482 796
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8482], outs := [5763], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8482 5763 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5765 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5765 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5763) (initSM 5764) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5765 5763 5764 800
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5763, 5764], outs := [5765] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5763 5764 5765)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5764 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5766 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5766 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5765) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5766 5765 804
    ({ rank := 0, op := "OpName.FW_view", ins := [5765], outs := [5766], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5765 5766)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5767 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5767 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8486) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5767 8486 797
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8486], outs := [5767], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8486 5767 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5769 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5769 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5767) (initSM 5768) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5769 5767 5768 801
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5767, 5768], outs := [5769] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5767 5768 5769)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5768 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5770 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5770 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5769) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5770 5769 805
    ({ rank := 0, op := "OpName.FW_view", ins := [5769], outs := [5770], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5769 5770)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5771 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5771 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5766) (denoteGraph_ringAttn sm_goal_3 initSM 5770) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5771 5766 5770 808
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5766, 5770], outs := [5771] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5766 5770 5771])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5772 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5772 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5771) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5772 5771 809
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5771], outs := [5772], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5771 5772 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5774 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5774 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5772) (initSM 5773) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5774 5772 5773 810
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5772, 5773], outs := [5774] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5772 5773 5774)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5773 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5775 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5775 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5774) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5775 5774 811
    ({ rank := 0, op := "OpName.FW_view", ins := [5774], outs := [5775], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5774 5775)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5776 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5776 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5762) (denoteGraph_ringAttn sm_goal_3 initSM 5775) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5776 5762 5775 812
    ({ rank := 0, op := "OpName.FW_mul", ins := [5762, 5775], outs := [5776] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5762 5775 5776])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5777 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5777 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5757) (denoteGraph_ringAttn sm_goal_3 initSM 5776) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5777 5757 5776 813
    ({ rank := 0, op := "OpName.FW_add", ins := [5757, 5776], outs := [5777] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5757 5776 5777)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5778 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5778 =
      denoteGraph_ringAttn sm_goal_3 initSM 5777 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5778 5777 814
    ({ rank := 0, op := "OpName.FW_float", ins := [5777], outs := [5778] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5777 5778 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5779 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8463) (denoteGraph_ringAttn sm_goal_3 initSM 5778) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5779 8463 5778 815
    ({ rank := 0, op := "OpName.FW_add", ins := [8463, 5778], outs := [5779] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8463 5778 5779)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8463 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8463 =
      denoteGraph_ringAttn sm_goal_3 initSM 5746 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8463 5746 791
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5746], outs := [8459, 8463], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5746 8459 8463 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8474 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8474 =
      denoteGraph_ringAttn sm_goal_3 initSM 5748 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8474 5748 793
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5748 8470 8474 8478 8482 8486 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8478 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8478 =
      denoteGraph_ringAttn sm_goal_3 initSM 5748 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8478 5748 793
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5748 8470 8474 8478 8482 8486 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8482 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8482 =
      denoteGraph_ringAttn sm_goal_3 initSM 5748 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8482 5748 793
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5748 8470 8474 8478 8482 8486 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8486 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8486 =
      denoteGraph_ringAttn sm_goal_3 initSM 5748 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8486 5748 793
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5748 8470 8474 8478 8482 8486 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5746 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11093,
         denoteGraph_ringAttn pm_goal_3 initPM 11094])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5757 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11117,
         denoteGraph_ringAttn pm_goal_3 initPM 11118] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5747 = initPM 5747 := hb initGoal_5747 (by decide) rfl
  have hw5603sh : (initPM 5750).shape = [64, 1024] := by
    have hgh := hII initGoal_5750 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5750] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5608 : initSM 5755 = allGatherPrimDimN 0 2 0 [initPM 11113, initPM 11114] := by
    have hg := hII initGoal_5755 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5755, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 11113) (initPM 11114) []
        (by rw [h_ss_pm 11113 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5609 : initSM 5756 = allGatherPrimDimN 0 2 0 [initPM 11115, initPM 11116] := by
    have hg := hII initGoal_5756 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5756, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 11115) (initPM 11116) []
        (by rw [h_ss_pm 11115 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L20_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hrouter := sm_pm_router_commute_L20 initSM initPM hInit hcarry5599 h10577 h10578
  -- PM rms output shapes [2048, 1024]
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11097).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L20, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11098).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L20, rms_sh]; exact h10578
  -- PM nl output shapes [2048, 64]
  have h10589sh : (denoteGraph_ringAttn pm_goal_3 initPM 11105).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L20, denote_pm_goal_3_10583_L20, denote_pm_goal_3_10581_L20]
    exact nl_sh 2048 1024 64 _ (initPM 5750) (by rw [rms_sh]; exact h10577) hw5603sh
  have h10590sh : (denoteGraph_ringAttn pm_goal_3 initPM 11106).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L20, denote_pm_goal_3_10584_L20, denote_pm_goal_3_10582_L20]
    exact nl_sh 2048 1024 64 _ (initPM 5750) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5751).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10589sh
  -- MoE weight shapes
  have hw10597 : (initPM 11113).shape = [32,1024,1024] := h_ss_pm 11113 [32,1024,1024] (by decide)
  have hw10598 : (initPM 11114).shape = [32,1024,1024] := h_ss_pm 11114 [32,1024,1024] (by decide)
  have hw10599 : (initPM 11115).shape = [32,1024,512] := h_ss_pm 11115 [32,1024,512] (by decide)
  have hw10600 : (initPM 11116).shape = [32,1024,512] := h_ss_pm 11116 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10591canon : denoteGraph_ringAttn pm_goal_3 initPM 11107
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11105) 8 64).fst := by
    rw [br_pm_11107,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11105).shape.reverse.head?).getD 1 = 64 from by rw [h10589sh]; rfl]
  have h10592canon : denoteGraph_ringAttn pm_goal_3 initPM 11108
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11106) 8 64).fst := by
    rw [br_pm_11108,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11106).shape.reverse.head?).getD 1 = 64 from by rw [h10590sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10591sh : (denoteGraph_ringAttn pm_goal_3 initPM 11107).shape = [2048, 64] := by
    rw [h10591canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10589sh]; rfl)
  have h10592sh : (denoteGraph_ringAttn pm_goal_3 initPM 11108).shape = [2048, 64] := by
    rw [h10592canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10590sh]; rfl)
  have h10593canon : denoteGraph_ringAttn pm_goal_3 initPM 11109
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11105) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593_L20,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11105).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10589sh]; rfl]
  have h10594canon : denoteGraph_ringAttn pm_goal_3 initPM 11110
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11106) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594_L20,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11106).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10590sh]; rfl]
  have h10593sh : (denoteGraph_ringAttn pm_goal_3 initPM 11109).shape = [2048, 64] := by
    rw [h10593canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10589sh
  have h10594sh : (denoteGraph_ringAttn pm_goal_3 initPM 11110).shape = [2048, 64] := by
    rw [h10594canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10590sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 11097) (denoteGraph_ringAttn pm_goal_3 initPM 11098)
    (denoteGraph_ringAttn pm_goal_3 initPM 11107) (denoteGraph_ringAttn pm_goal_3 initPM 11108)
    (denoteGraph_ringAttn pm_goal_3 initPM 11109) (denoteGraph_ringAttn pm_goal_3 initPM 11110)
    (initPM 11113) (initPM 11114) (initPM 11115) (initPM 11116)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10581sh h10582sh h10591sh h10592sh h10593sh h10594sh hw10597 hw10598 hw10599 hw10600
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_11117, br_pm_11118, br_pm_16632, br_pm_16655,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5757, br_sm_8474, denote_sm_goal_3_5601_L20, br_sm_5752]
  rw [hrouter, h5608, h5609]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5751).shape.reverse.head?).getD 1 = 64 from by rw [hSM5604sh]; rfl]
  rw [hw5600, hcarry5599, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5747) 2048 1024 (by omega) (by omega) h10577 h10578]
  rw [← denote_pm_goal_3_10581_L20, ← denote_pm_goal_3_10582_L20]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10589sh h10590sh]
  rw [← h10591canon, ← h10592canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L20_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5746 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11093,
         denoteGraph_ringAttn pm_goal_3 initPM 11094])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5776
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11191,
           denoteGraph_ringAttn pm_goal_3 initPM 11192] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5747 = initPM 5747 := hb initGoal_5747 (by decide) rfl
  have hw5612 : initSM 5759 = initPM 5759 := hb initGoal_5759 (by decide) rfl
  have hw5617 : initSM 5764 = initPM 5764 := hb initGoal_5764 (by decide) rfl
  have hw5621 : initSM 5768 = initPM 5768 := hb initGoal_5768 (by decide) rfl
  have hw5626 : initSM 5773 = initPM 5773 := hb initGoal_5773 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5746) (initSM 5747)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11097,
           denoteGraph_ringAttn pm_goal_3 initPM 11098] := by
    rw [hcarry5599, hw5600,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5747) 2048 1024 (by omega) (by omega) h10577 h10578,
        ← denote_pm_goal_3_10581_L20, ← denote_pm_goal_3_10582_L20]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 11097 / 11098
  rw [br_pm_11191, br_pm_11192,
      br_pm_11131, br_pm_11129, br_pm_11123, br_pm_11119, br_pm_16636,
      br_pm_11187, br_pm_11177, br_pm_11171, br_pm_11169,
      br_pm_11147, br_pm_11137, br_pm_11133, br_pm_16640,
      br_pm_11165, br_pm_11155, br_pm_11151, br_pm_16644,
      br_pm_11132, br_pm_11130, br_pm_11124, br_pm_11120, br_pm_16659,
      br_pm_11188, br_pm_11178, br_pm_11172, br_pm_11170,
      br_pm_11148, br_pm_11138, br_pm_11134, br_pm_16663,
      br_pm_11166, br_pm_11156, br_pm_11152, br_pm_16667]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5748
  rw [br_sm_5776, br_sm_5762, br_sm_5761, br_sm_5760,
      br_sm_5758, br_sm_8478,
      br_sm_5775, br_sm_5774, br_sm_5772, br_sm_5771,
      br_sm_5766, br_sm_5765, br_sm_5763, br_sm_8482,
      br_sm_5770, br_sm_5769, br_sm_5767, br_sm_8486,
      denote_sm_goal_3_5601_L20]
  rw [hRMS, hw5612, hw5617, hw5621, hw5626]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 11097 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 11098 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581_L20, rms_sh]; exact h10577
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582_L20, rms_sh]; exact h10578
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5759).shape = [1, 1024] := h_ss_pm 5759 [1, 1024] (by decide)
  have hw29 : (initPM 5764).shape = [512, 1024] := h_ss_pm 5764 [512, 1024] (by decide)
  have hw33 : (initPM 5768).shape = [512, 1024] := h_ss_pm 5768 [512, 1024] (by decide)
  have hw38 : (initPM 5773).shape = [1024, 512] := h_ss_pm 5773 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5759) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5764) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5768) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5759)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5759)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5764)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5764)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5768)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5768)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5759), fw_linear (fw_view [2048, 1024] B) (initPM 5759)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5759)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5759))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5764), fw_linear (fw_view [2048, 1024] B) (initPM 5764)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5768), fw_linear (fw_view [2048, 1024] B) (initPM 5768)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5759)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5759)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5773) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768))))) (initPM 5773)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))))) (initPM 5773)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768))))) (initPM 5773), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))))) (initPM 5773)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768))))) (initPM 5773)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))))) (initPM 5773))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5759))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5759))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5768))))) (initPM 5773)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5764))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5768))))) (initPM 5773)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11205_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024] := by
  have h10517 := hbase345
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11089).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L20, denote_pm_goal_3_10569_L20]; rfl
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11093).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L20]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10517 h10573
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11097).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L20, rms_sh]; exact h10577
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 11117).shape = [2048, 1024] := by
    rw [br_pm_11117, br_pm_16632]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 11131).shape = [2048, 1] := by
    rw [br_pm_11131, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11129]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 11187).shape = [2048, 1024] := by
    rw [br_pm_11187]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 11191).shape = [2048, 1024] := by
    rw [br_pm_11191, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11117) (denoteGraph_ringAttn pm_goal_3 initPM 11191)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have h16379sh : (denoteGraph_ringAttn pm_goal_3 initPM 16613).shape = [2048, 1024] := by
    rw [br_pm_16613]; exact h10577
  have h10685sh : (denoteGraph_ringAttn pm_goal_3 initPM 11201).shape = [2048, 1024] := by
    rw [br_pm_11201, br_pm_11195]; exact hinnerA
  rw [br_pm_11205]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16379sh h10685sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11206_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024] := by
  have h10518 := hbase346
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11090).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L20, denote_pm_goal_3_10570_L20]; rfl
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11094).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L20]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10518 h10574
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11098).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L20, rms_sh]; exact h10578
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 11118).shape = [2048, 1024] := by
    rw [br_pm_11118, br_pm_16655]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 11132).shape = [2048, 1] := by
    rw [br_pm_11132, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11130]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 11188).shape = [2048, 1024] := by
    rw [br_pm_11188]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 11192).shape = [2048, 1024] := by
    rw [br_pm_11192, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11118) (denoteGraph_ringAttn pm_goal_3 initPM 11192)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  have h16387sh : (denoteGraph_ringAttn pm_goal_3 initPM 16621).shape = [2048, 1024] := by
    rw [br_pm_16621]; exact h10578
  have h10686sh : (denoteGraph_ringAttn pm_goal_3 initPM 11202).shape = [2048, 1024] := by
    rw [br_pm_11202, br_pm_11196]; exact hinnerB
  rw [br_pm_11206]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16387sh h10686sh

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L20
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L20
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L20_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L20_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L20_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L20_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11205_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11206_shape
