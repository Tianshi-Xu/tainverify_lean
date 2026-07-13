/-
  Pattern_3_L22_spike.lean — L22 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L22-specific TIDs.  The L22 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L22's Q path
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

/-! ## L22 attention node declarations + buddy proofs.
SM attn node index 854; PM r0 = 1767; PM r1 = 1768. -/

def nSM_22 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5832, 5833, 5834, 5835, 5836], outs := [5837],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_22 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11383, 5833, 5834, 5835, 5836], outs := [11407],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_22 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11384, 5833, 5834, 5835, 5836], outs := [11408],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_22 : ringAttnBuddies sm_goal_3 nSM_22 = [nSM_22] := by
  show (List.filter (fun m => decide (m.op = nSM_22.op) && decide (m.params = nSM_22.params) &&
      decide (m.ins.getD 3 0 = nSM_22.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_22.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_22]
  rw [show (List.filter (fun m => decide (m.op = nSM_22.op) && decide (m.params = nSM_22.params) &&
      decide (m.ins.getD 3 0 = nSM_22.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_22.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_22] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_22 : ringAttnBuddies pm_goal_3 nR0_22 = [nR0_22, nR1_22] := by
  show (List.filter (fun m => decide (m.op = nR0_22.op) && decide (m.params = nR0_22.params) &&
      decide (m.ins.getD 3 0 = nR0_22.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_22.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_22, nR1_22]
  rw [show (List.filter (fun m => decide (m.op = nR0_22.op) && decide (m.params = nR0_22.params) &&
      decide (m.ins.getD 3 0 = nR0_22.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_22.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_22, nR1_22] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_22 : ringAttnBuddies pm_goal_3 nR1_22 = [nR0_22, nR1_22] := by
  show (List.filter (fun m => decide (m.op = nR1_22.op) && decide (m.params = nR1_22.params) &&
      decide (m.ins.getD 3 0 = nR1_22.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_22.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_22, nR1_22]
  rw [show (List.filter (fun m => decide (m.op = nR1_22.op) && decide (m.params = nR1_22.params) &&
      decide (m.ins.getD 3 0 = nR1_22.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_22.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_22, nR1_22] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L22 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L22_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5837
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_22 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5837
      = (sm_goal_3.nodes.take 855).foldl (applyNodeRingAttn sm_goal_3) initSM 5837 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5837 855 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 855 = sm_goal_3.nodes.take 854 ++ [nSM_22] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5832 5833 5834 5835 5836 5837 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L22_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11407
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_22 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11407
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 11407 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11407 1768 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1768 = pm_goal_3.nodes.take 1767 ++ [nR0_22] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 11383 5833 5834 5835 5836 11407 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L22_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11408
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_22 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11408
      = (pm_goal_3.nodes.take 1769).foldl (applyNodeRingAttn pm_goal_3) initPM 11408 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11408 1769 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1769 = pm_goal_3.nodes.take 1768 ++ [nR1_22] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 11384 5833 5834 5835 5836 11408 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L22) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5830 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5828) (initSM 5829) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5830 8529 5829 852
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8529, 5829], outs := [5830] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8529 5829 5830)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8529 5828 851
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5828], outs := [8529, 8533], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5828 8529 [8529, 8533] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5829 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5832 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5830) (initSM 5831) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5832 5830 5831 853
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5830, 5831], outs := [5832] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5830 5831 5832 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5831 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5838 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5837) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5838 5837 855
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5837], outs := [5838], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5837 5838 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5839 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5838) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5839 5838 856
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5838], outs := [5839], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5838 5839 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5841 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5839) (initSM 5840) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5841 5839 5840 857
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5839, 5840], outs := [5841] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5839 5840 5841)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5840 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5842 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5841) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5842 5841 858
    ({ rank := 0, op := "OpName.FW_view", ins := [5841], outs := [5842], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5841 5842)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5843 =
      denoteGraph_ringAttn sm_goal_3 initSM 5842 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5843 5842 859
    ({ rank := 0, op := "OpName.FW_float", ins := [5842], outs := [5843] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5842 5843 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5844 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5828)
        (denoteGraph_ringAttn sm_goal_3 initSM 5843) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8533 = denoteGraph_ringAttn sm_goal_3 initSM 5828 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8533 5828 851
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5828], outs := [8529, 8533], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5828 8533 [8529, 8533] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5844 8533 5843 860
    ({ rank := 0, op := "OpName.FW_add", ins := [8533, 5843], outs := [5844] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8533 5843 5844)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5846 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5844) (initSM 5845) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5846 8537 5845 862
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8537, 5845], outs := [5846] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8537 5845 5846)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8537 5844 861
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5844], outs := [8537, 8541], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5844 8537 [8537, 8541] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5845 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5847 =
      denoteGraph_ringAttn sm_goal_3 initSM 5846 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5847 8548 864
    ({ rank := 0, op := "OpName.FW_float", ins := [8548], outs := [5847] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8548 5847 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8548 5846 863
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5846 8548 [8548, 8552, 8556, 8560, 8564] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5849 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5847) (initSM 5848) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5849 5847 5848 868
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5847, 5848], outs := [5849] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5847 5848 5849 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5848 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5851 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5849) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5849).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5851 5849 872
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5849], outs := [5850, 5851, 5852], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5849 5850 5851 5852 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5833 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5833 8073 490
    ({ rank := 0, op := "OpName.FW_to", ins := [8073], outs := [5833] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8073 5833 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8073 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8073 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589_L22 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5834 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5834 8131 502
    ({ rank := 0, op := "OpName.FW_to", ins := [8131], outs := [5834] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8131 5834 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8131 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8131 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L22) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11381 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11377) (initPM 5829) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11381 16749 5829 1763
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16749, 5829], outs := [11381] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16749 5829 11381)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16749 11377 1761
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749, 16753], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11377 16749 [16749, 16753] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5829 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11383 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11381) (initPM 5831) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11383 11381 5831 1765
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11381, 5831], outs := [11383] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 11381 5831 11383 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5831 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11409 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11407) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11409 11407 1769
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11407], outs := [11409], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11407 11409 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11415 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11409) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11415 11409 1771
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11409], outs := [11415], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11409 11415 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11419 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11415) (initPM 5840) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11419 11415 5840 1773
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11415, 5840], outs := [11419] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11415 5840 11419)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5840 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11429 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11419) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11429 11419 1775
    ({ rank := 0, op := "OpName.FW_view", ins := [11419], outs := [11429], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11419 11429)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11433 =
      denoteGraph_ringAttn pm_goal_3 initPM 11429 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11433 11429 1777
    ({ rank := 0, op := "OpName.FW_float", ins := [11429], outs := [11433] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11429 11433 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11437 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11377)
        (denoteGraph_ringAttn pm_goal_3 initPM 11433) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16753 = denoteGraph_ringAttn pm_goal_3 initPM 11377 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16753 11377 1761
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749, 16753], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11377 16753 [16749, 16753] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11437 16753 11433 1779
    ({ rank := 0, op := "OpName.FW_add", ins := [16753, 11433], outs := [11437] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16753 11433 11437)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11441 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11437) (initPM 5845) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11441 16765 5845 1783
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16765, 5845], outs := [11441] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16765 5845 11441)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16765 11437 1781
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11437], outs := [16765, 16769], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11437 16765 [16765, 16769] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5845 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11443 =
      denoteGraph_ringAttn pm_goal_3 initPM 11441 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11443 16784 1787
    ({ rank := 0, op := "OpName.FW_float", ins := [16784], outs := [11443] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16784 11443 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16784 11441 1785
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11441 16784 [16784, 16788, 16792, 16796, 16800] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11449 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11443) (initPM 5848) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11449 11443 5848 1795
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [11443, 5848], outs := [11449] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 11443 5848 11449 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5848 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11453 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11449) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11449).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11453 11449 1803
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11449], outs := [11451, 11453, 11455], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 11449 11451 11453 11455 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11382 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11378) (initPM 5829) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11382 16757 5829 1764
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16757, 5829], outs := [11382] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16757 5829 11382)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16757 11378 1762
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757, 16761], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11378 16757 [16757, 16761] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5829 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11384 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11382) (initPM 5831) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11384 11382 5831 1766
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11382, 5831], outs := [11384] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 11382 5831 11384 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5831 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11410 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11408) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11410 11408 1770
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11408], outs := [11410], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11408 11410 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11416 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11410) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11416 11410 1772
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11410], outs := [11416], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11410 11416 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11420 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11416) (initPM 5840) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11420 11416 5840 1774
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11416, 5840], outs := [11420] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11416 5840 11420)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5840 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11430 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11420) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11430 11420 1776
    ({ rank := 1, op := "OpName.FW_view", ins := [11420], outs := [11430], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11420 11430)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11434 =
      denoteGraph_ringAttn pm_goal_3 initPM 11430 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11434 11430 1778
    ({ rank := 1, op := "OpName.FW_float", ins := [11430], outs := [11434] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11430 11434 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11438 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11378)
        (denoteGraph_ringAttn pm_goal_3 initPM 11434) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16761 = denoteGraph_ringAttn pm_goal_3 initPM 11378 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16761 11378 1762
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757, 16761], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11378 16761 [16757, 16761] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11438 16761 11434 1780
    ({ rank := 1, op := "OpName.FW_add", ins := [16761, 11434], outs := [11438] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16761 11434 11438)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11442 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11438) (initPM 5845) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11442 16773 5845 1784
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16773, 5845], outs := [11442] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16773 5845 11442)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16773 11438 1782
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11438], outs := [16773, 16777], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11438 16773 [16773, 16777] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5845 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11444 =
      denoteGraph_ringAttn pm_goal_3 initPM 11442 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11444 16807 1791
    ({ rank := 1, op := "OpName.FW_float", ins := [16807], outs := [11444] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16807 11444 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16807 11442 1786
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11442 16807 [16807, 16811, 16815, 16819, 16823] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11450 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11444) (initPM 5848) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11450 11444 5848 1799
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [11444, 5848], outs := [11450] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 11444 5848 11450 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5848 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11454 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11450) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11450).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11454 11450 1807
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11450], outs := [11452, 11454, 11456], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 11450 11452 11454 11456 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5833 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5833 15855 1041
    ({ rank := 1, op := "OpName.FW_to", ins := [15855], outs := [5833] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15855 5833 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15855 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15855 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589_L22 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5834 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5834 15961 1065
    ({ rank := 1, op := "OpName.FW_to", ins := [15961], outs := [5834] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15961 5834 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15961 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15961 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L22 commute theorems -/

-- Q sharding commute: SM 5832 = allGather0[PM 11383, PM 11384].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11377,
         denoteGraph_ringAttn pm_goal_3 initPM 11378])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024])
    (hw5586 : (initPM 5831).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5832 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11383,
         denoteGraph_ringAttn pm_goal_3 initPM 11384] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5829 = initPM 5829 := hb initGoal_5829 (by decide) rfl
  have hw5586e : initSM 5831 = initPM 5831 := hb initGoal_5831 (by decide) rfl
  rw [denote_sm_goal_3_5587_L22, denote_sm_goal_3_5585_L22,
      denote_pm_goal_3_10523_L22, denote_pm_goal_3_10521_L22,
      denote_pm_goal_3_10524_L22, denote_pm_goal_3_10522_L22]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11377) (initPM 5829)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11378) (initPM 5829)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5829) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5831) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape_L22 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5833).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588_L22, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape_L22 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5834).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589_L22, denote_pm_goal_3_5336]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))

-- K/V replication (cross-graph, full tensor): SM 5833 = PM 5833, SM 5834 = PM 5834.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5833 =
      denoteGraph_ringAttn pm_goal_3 initPM 5833 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588_L22, denote_pm_goal_3_5588_L22, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5834 =
      denoteGraph_ringAttn pm_goal_3 initPM 5834 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589_L22, denote_pm_goal_3_5589_L22, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L22 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L22_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11377,
         denoteGraph_ringAttn pm_goal_3 initPM 11378])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5836)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5837 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11407,
         denoteGraph_ringAttn pm_goal_3 initPM 11408] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5831).shape = [16, 64, 1024] := hPM 5831 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L22_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L22_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L22_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape_L22 initPM hPM
  have hVsh := pm_5589_shape_L22 initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11381).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L22, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11382).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L22, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 11383).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L22]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 11384).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L22]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5832).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5832).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5833).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5834).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 854)
  have bSM5587 : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5832 = denoteGraph_ringAttn sm_goal_3 initSM 5832 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5832 854 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5833 = denoteGraph_ringAttn sm_goal_3 initSM 5833 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5833 854 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5834 = denoteGraph_ringAttn sm_goal_3 initSM 5834 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5834 854 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1767)
  have bPM10523 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11383 = denoteGraph_ringAttn pm_goal_3 initPM 11383 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11383 1767 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11384 = denoteGraph_ringAttn pm_goal_3 initPM 11384 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11384 1767 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5833 = denoteGraph_ringAttn pm_goal_3 initPM 5833 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5833 1767 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5834 = denoteGraph_ringAttn pm_goal_3 initPM 5834 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5834 1767 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5835 = initSM 5835 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 854) initSM 5835 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5836 = initSM 5836 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 854) initSM 5836 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5835 = initPM 5835 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1767) initPM 5835 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5836 = initPM 5836 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1767) initPM 5836 (by decide) (by decide)
  have hw5590 : initSM 5835 = initPM 5835 := hb initGoal_5835 (by decide) rfl
  have hw5591 : initSM 5836 = initPM 5836 := hb initGoal_5836 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5832).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5833).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5834).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 0 0),
        (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5832 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11383,
        (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11384]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5833 =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5833
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5834 =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5834
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5833).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5834).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5836)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5835 =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5835
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_22.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM 5836 =
      (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5836
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 0 0),
       (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11383,
       (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11384]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 0 0),
          (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 1 0),
          (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 2 0),
          (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 4 0))
        (nR0_22.params.getD 0 1) (nR0_22.params.getD 1 1) (nR0_22.params.getD 2 1) (nR0_22.params.getD 3 1)
        (decide (nR0_22.params.getD 4 0 ≠ 0)) (nR0_22.params.getD 5 0)).shape
        = [2 * 2048, nR0_22.params.getD 0 1, nR0_22.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1767 -> take 1768)
  have e10523 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11383
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 11383 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11383 1767 1768 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11384
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 11384 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11384 1767 1768 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5833
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 5833 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5833 1767 1768 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5834
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 5834 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5834 1767 1768 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5835
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 5835 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5835 1767 1768 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 5836
      = (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 5836 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5836 1767 1768 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_22
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_22 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_22]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_22]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_22]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 854).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_22 nR0_22 nR1_22 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_22 buddy_r0_22 buddy_r1_22 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L22_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L22_r0_bridge, ← denote_pm_attn_L22_r1_bridge]


/-! ## L22 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5837 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11407,
         denoteGraph_ringAttn pm_goal_3 initPM 11408])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11407).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11408).shape = [2048, 16, 64])
    (hw5595 : (initPM 5840).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5843 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11433,
         denoteGraph_ringAttn pm_goal_3 initPM 11434] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5840 = initPM 5840 := hb initGoal_5840 (by decide) rfl
  rw [denote_sm_goal_3_5598_L22, denote_sm_goal_3_5597_L22, denote_sm_goal_3_5596_L22,
      denote_sm_goal_3_5594_L22, denote_sm_goal_3_5593_L22,
      denote_pm_goal_3_10573_L22, denote_pm_goal_3_10569_L22, denote_pm_goal_3_10559_L22,
      denote_pm_goal_3_10555_L22, denote_pm_goal_3_10549_L22,
      denote_pm_goal_3_10574_L22, denote_pm_goal_3_10570_L22, denote_pm_goal_3_10560_L22,
      denote_pm_goal_3_10556_L22, denote_pm_goal_3_10550_L22]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11407))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11408))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5840) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11407))) (initPM 5840)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11408))) (initPM 5840)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11407))) (initPM 5840),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11408))) (initPM 5840)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute_L22 (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11377,
         denoteGraph_ringAttn pm_goal_3 initPM 11378])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5843 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11433,
         denoteGraph_ringAttn pm_goal_3 initPM 11434])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11433).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11434).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5844 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11437,
         denoteGraph_ringAttn pm_goal_3 initPM 11438] := by
  rw [denote_sm_goal_3_5599_L22, denote_pm_goal_3_10577_L22, denote_pm_goal_3_10578_L22]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5844 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11437,
         denoteGraph_ringAttn pm_goal_3 initPM 11438])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11437).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11438).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5849 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11449,
         denoteGraph_ringAttn pm_goal_3 initPM 11450] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5845 = initPM 5845 := hb initGoal_5845 (by decide) rfl
  have hw5603 : initSM 5848 = initPM 5848 := hb initGoal_5848 (by decide) rfl
  have hw5603sh : (initPM 5848).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5848 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5848] using hsh
  rw [denote_sm_goal_3_5604_L22, denote_sm_goal_3_5602_L22, denote_sm_goal_3_5601_L22,
      denote_pm_goal_3_10589_L22, denote_pm_goal_3_10583_L22, denote_pm_goal_3_10581_L22,
      denote_pm_goal_3_10590_L22, denote_pm_goal_3_10584_L22, denote_pm_goal_3_10582_L22]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5845) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11437) (initPM 5845)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11438) (initPM 5845)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5848) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L22 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5844 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11437,
         denoteGraph_ringAttn pm_goal_3 initPM 11438])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11437).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11438).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5851 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11453,
         denoteGraph_ringAttn pm_goal_3 initPM 11454] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5848).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5848 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5848] using hsh
  have hnl := sm_pm_nl_L22_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 11449).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L22, denote_pm_goal_3_10583_L22, denote_pm_goal_3_10581_L22]
    exact nl_sh 2048 1024 64 _ (initPM 5848) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 11450).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L22, denote_pm_goal_3_10584_L22, denote_pm_goal_3_10582_L22]
    exact nl_sh 2048 1024 64 _ (initPM 5848) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5849).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606_L22, denote_pm_goal_3_10593_L22, denote_pm_goal_3_10594_L22]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5849).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11449).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11450).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L22 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L22_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11377,
         denoteGraph_ringAttn pm_goal_3 initPM 11378])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5837 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11407,
         denoteGraph_ringAttn pm_goal_3 initPM 11408])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11407).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11408).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024])
    (hw5595 : (initPM 5840).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5851 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11453,
         denoteGraph_ringAttn pm_goal_3 initPM 11454] := by
  have hreshape := sm_pm_reshape_float_L22_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11433).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L22, denote_pm_goal_3_10569_L22]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11434).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L22, denote_pm_goal_3_10570_L22]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L22 initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11437).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L22]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11438).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L22]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L22 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L22 router — fully assembled

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
theorem sm_pm_router_commute_L22_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5836)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11377,
         denoteGraph_ringAttn pm_goal_3 initPM 11378])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5851 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11453,
         denoteGraph_ringAttn pm_goal_3 initPM 11454] := by
  have hattn := sm_pm_attention_L22_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5831).shape = [16, 64, 1024] := hPM 5831 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5840).shape = [1024, 1024] := hPM 5840 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11381).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L22, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11382).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L22, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 11383).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L22]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 11384).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L22]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11383
      = denoteGraph_ringAttn pm_goal_3 initPM 11383 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11383 1767 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM 11384
      = denoteGraph_ringAttn pm_goal_3 initPM 11384 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11384 1767 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 11383
      = denoteGraph_ringAttn pm_goal_3 initPM 11383 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11383 1768 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM 11384
      = denoteGraph_ringAttn pm_goal_3 initPM 11384 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11384 1768 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11407).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L22_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_22 nR0_22 nR1_22 0 buddy_r0_22 (by decide)]
    have e0 : nR0_22.ins.getD 0 0 = 11383 := by decide
    have e1 : nR1_22.ins.getD 0 0 = 11384 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 0 0),
         (pm_goal_3.nodes.take 1767).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11408).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L22_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_22 nR0_22 nR1_22 1 buddy_r1_22 (by decide)]
    have e0 : nR0_22.ins.getD 0 0 = 11383 := by decide
    have e1 : nR1_22.ins.getD 0 0 = 11384 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_22.ins.getD 0 0),
         (pm_goal_3.nodes.take 1768).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_22.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L22_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L22_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5836)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _


-- ================= L22 MoE carry (sm_pm_carry_5877_commute) =================
theorem br_pm_16753 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16753 = denoteGraph_ringAttn pm_goal_3 initPM 11377 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16753 11377 1761
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749, 16753], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11377 16753 [16749, 16753] 2 (by decide) (by decide))
    rfl

theorem br_pm_16761 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16761 = denoteGraph_ringAttn pm_goal_3 initPM 11378 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16761 11378 1762
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757, 16761], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11378 16761 [16757, 16761] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11451 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11451 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11449) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 11449).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11451 11449 1803
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11449], outs := [11451, 11453, 11455], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 11449 11451 11453 11455 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11452 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11452 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11450) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 11450).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11452 11450 1807
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11450], outs := [11452, 11454, 11456], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 11450 11452 11454 11456 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11461 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11461 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16788)
        (denoteGraph_ringAttn pm_goal_3 initPM 11451)
        (denoteGraph_ringAttn pm_goal_3 initPM 11453)
        [initPM 11457, initPM 11458] [initPM 11459, initPM 11460]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 11461 16788 11451 11453 11457 11458 11459 11460 1811
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16788, 11451, 11453, 11457, 11458, 11459, 11460], outs := [11461], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16788 11451 11453 11457 11458 11459 11460 11461 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11457 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11458 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11459 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11460 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11462 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11462 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16811)
        (denoteGraph_ringAttn pm_goal_3 initPM 11452)
        (denoteGraph_ringAttn pm_goal_3 initPM 11454)
        [initPM 11457, initPM 11458] [initPM 11459, initPM 11460]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 11462 16811 11452 11454 11457 11458 11459 11460 1814
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16811, 11452, 11454, 11457, 11458, 11459, 11460], outs := [11462], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16811 11452 11454 11457 11458 11459 11460 11462 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11457 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11458 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11459 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11460 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11463 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11463 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16792) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11463 16792 1788
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16792], outs := [11463], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16792 11463 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11464 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11464 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16815) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11464 16815 1792
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16815], outs := [11464], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16815 11464 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11467 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11467 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11463) (initPM 5857) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11467 11463 5857 1796
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11463, 5857], outs := [11467] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11463 5857 11467)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5857 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11468 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11468 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11464) (initPM 5857) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11468 11464 5857 1800
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11464, 5857], outs := [11468] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11464 5857 11468)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5857 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11473 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11473 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 11467) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11473 11467 1804
    ({ rank := 0, op := "OpName.FW_view", ins := [11467], outs := [11473], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 11467 11473)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11474 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11474 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 11468) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11474 11468 1808
    ({ rank := 1, op := "OpName.FW_view", ins := [11468], outs := [11474], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 11468 11474)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11475 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11475 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 11473) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11475 11473 1812
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [11473], outs := [11475] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 11473 11475])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11476 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11476 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 11474) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11476 11474 1815
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [11474], outs := [11476] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 11474 11476])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11477 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11477 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16796) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11477 16796 1789
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16796], outs := [11477], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16796 11477 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11478 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11478 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16819) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11478 16819 1793
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16819], outs := [11478], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16819 11478 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11481 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11481 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11477) (initPM 5862) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11481 11477 5862 1797
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11477, 5862], outs := [11481] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11477 5862 11481)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5862 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11482 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11482 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11478) (initPM 5862) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11482 11478 5862 1801
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11478, 5862], outs := [11482] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11478 5862 11482)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5862 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11491 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11491 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11481) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11491 11481 1805
    ({ rank := 0, op := "OpName.FW_view", ins := [11481], outs := [11491], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 11481 11491)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11492 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11492 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11482) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11492 11482 1809
    ({ rank := 1, op := "OpName.FW_view", ins := [11482], outs := [11492], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 11482 11492)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11495 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11495 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16800) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11495 16800 1790
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16800], outs := [11495], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16800 11495 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11496 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11496 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16823) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11496 16823 1794
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16823], outs := [11496], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16823 11496 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11499 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11499 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11495) (initPM 5866) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11499 11495 5866 1798
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11495, 5866], outs := [11499] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11495 5866 11499)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5866 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11500 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11500 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11496) (initPM 5866) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11500 11496 5866 1802
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11496, 5866], outs := [11500] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11496 5866 11500)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5866 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11509 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11509 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11499) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11509 11499 1806
    ({ rank := 0, op := "OpName.FW_view", ins := [11499], outs := [11509], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 11499 11509)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11510 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11510 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11500) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11510 11500 1810
    ({ rank := 1, op := "OpName.FW_view", ins := [11500], outs := [11510], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 11500 11510)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11513 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11513 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 11491) (denoteGraph_ringAttn pm_goal_3 initPM 11509) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11513 11491 11509 1813
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [11491, 11509], outs := [11513] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 11491 11509 11513])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11514 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11514 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 11492) (denoteGraph_ringAttn pm_goal_3 initPM 11510) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11514 11492 11510 1816
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [11492, 11510], outs := [11514] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 11492 11510 11514])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11515 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11515 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11513) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11515 11513 1817
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11513], outs := [11515], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11513 11515 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11516 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11516 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11514) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11516 11514 1818
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11514], outs := [11516], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11514 11516 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11521 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11521 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11515) (initPM 5871) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11521 11515 5871 1819
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11515, 5871], outs := [11521] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11515 5871 11521)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5871 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11522 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11522 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11516) (initPM 5871) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11522 11516 5871 1820
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11516, 5871], outs := [11522] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11516 5871 11522)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5871 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11531 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11531 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11521) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11531 11521 1821
    ({ rank := 0, op := "OpName.FW_view", ins := [11521], outs := [11531], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11521 11531)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11532 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11532 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11522) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11532 11522 1822
    ({ rank := 1, op := "OpName.FW_view", ins := [11522], outs := [11532], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11522 11532)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11535 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11535 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 11475) (denoteGraph_ringAttn pm_goal_3 initPM 11531) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11535 11475 11531 1823
    ({ rank := 0, op := "OpName.FW_mul", ins := [11475, 11531], outs := [11535] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 11475 11531 11535])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11536 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11536 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 11476) (denoteGraph_ringAttn pm_goal_3 initPM 11532) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11536 11476 11532 1824
    ({ rank := 1, op := "OpName.FW_mul", ins := [11476, 11532], outs := [11536] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 11476 11532 11536])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11539 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11539 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11461) (denoteGraph_ringAttn pm_goal_3 initPM 11535) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11539 11461 11535 1825
    ({ rank := 0, op := "OpName.FW_add", ins := [11461, 11535], outs := [11539] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 11461 11535 11539)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11540 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11540 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11462) (denoteGraph_ringAttn pm_goal_3 initPM 11536) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11540 11462 11536 1826
    ({ rank := 1, op := "OpName.FW_add", ins := [11462, 11536], outs := [11540] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 11462 11536 11540)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11545 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11545 =
      denoteGraph_ringAttn pm_goal_3 initPM 11539 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11545 11539 1827
    ({ rank := 0, op := "OpName.FW_float", ins := [11539], outs := [11545] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11539 11545 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11546 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11546 =
      denoteGraph_ringAttn pm_goal_3 initPM 11540 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11546 11540 1828
    ({ rank := 1, op := "OpName.FW_float", ins := [11540], outs := [11546] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11540 11546 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11549 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11549 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16769) (denoteGraph_ringAttn pm_goal_3 initPM 11545) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11549 16769 11545 1829
    ({ rank := 0, op := "OpName.FW_add", ins := [16769, 11545], outs := [11549] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16769 11545 11549)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11550 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11550 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16777) (denoteGraph_ringAttn pm_goal_3 initPM 11546) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11550 16777 11546 1830
    ({ rank := 1, op := "OpName.FW_add", ins := [16777, 11546], outs := [11550] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16777 11546 11550)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16769 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16769 =
      denoteGraph_ringAttn pm_goal_3 initPM 11437 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16769 11437 1781
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11437], outs := [16765, 16769], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 11437 16765 16769 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16777 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16777 =
      denoteGraph_ringAttn pm_goal_3 initPM 11438 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16777 11438 1782
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11438], outs := [16773, 16777], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 11438 16773 16777 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16788 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16788 =
      denoteGraph_ringAttn pm_goal_3 initPM 11441 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16788 11441 1785
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 11441 16784 16788 16792 16796 16800 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16792 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16792 =
      denoteGraph_ringAttn pm_goal_3 initPM 11441 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16792 11441 1785
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 11441 16784 16788 16792 16796 16800 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16796 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16796 =
      denoteGraph_ringAttn pm_goal_3 initPM 11441 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16796 11441 1785
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 11441 16784 16788 16792 16796 16800 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16800 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16800 =
      denoteGraph_ringAttn pm_goal_3 initPM 11441 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16800 11441 1785
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 11441 16784 16788 16792 16796 16800 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16811 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16811 =
      denoteGraph_ringAttn pm_goal_3 initPM 11442 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16811 11442 1786
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 11442 16807 16811 16815 16819 16823 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16815 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16815 =
      denoteGraph_ringAttn pm_goal_3 initPM 11442 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16815 11442 1786
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 11442 16807 16811 16815 16819 16823 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16819 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16819 =
      denoteGraph_ringAttn pm_goal_3 initPM 11442 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16819 11442 1786
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 11442 16807 16811 16815 16819 16823 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16823 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16823 =
      denoteGraph_ringAttn pm_goal_3 initPM 11442 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16823 11442 1786
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 11442 16807 16811 16815 16819 16823 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5850 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5850 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5849) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5849).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5850 5849 872
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5849], outs := [5850, 5851, 5852], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5849 5850 5851 5852 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5855 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5855 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8552)
        (denoteGraph_ringAttn sm_goal_3 initSM 5850)
        (denoteGraph_ringAttn sm_goal_3 initSM 5851)
        (initSM 5853) (initSM 5854) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5855 8552 5850 5851 5853 5854 876
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8552, 5850, 5851, 5853, 5854], outs := [5855], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8552 5850 5851 5853 5854 5855 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5853 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5854 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5856 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5856 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8556) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5856 8556 865
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8556], outs := [5856], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8556 5856 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5858 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5858 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5856) (initSM 5857) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5858 5856 5857 869
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5856, 5857], outs := [5858] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5856 5857 5858)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5857 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5859 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5859 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5858) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5859 5858 873
    ({ rank := 0, op := "OpName.FW_view", ins := [5858], outs := [5859], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5858 5859)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5860 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5860 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5859) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5860 5859 877
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5859], outs := [5860] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5859 5860])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5861 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5861 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8560) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5861 8560 866
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8560], outs := [5861], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8560 5861 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5863 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5863 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5861) (initSM 5862) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5863 5861 5862 870
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5861, 5862], outs := [5863] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5861 5862 5863)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5862 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5864 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5864 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5863) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5864 5863 874
    ({ rank := 0, op := "OpName.FW_view", ins := [5863], outs := [5864], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5863 5864)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5865 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5865 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8564) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5865 8564 867
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8564], outs := [5865], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8564 5865 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5867 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5867 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5865) (initSM 5866) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5867 5865 5866 871
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5865, 5866], outs := [5867] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5865 5866 5867)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5866 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5868 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5868 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5867) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5868 5867 875
    ({ rank := 0, op := "OpName.FW_view", ins := [5867], outs := [5868], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5867 5868)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5869 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5869 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5864) (denoteGraph_ringAttn sm_goal_3 initSM 5868) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5869 5864 5868 878
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5864, 5868], outs := [5869] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5864 5868 5869])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5870 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5870 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5869) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5870 5869 879
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5869], outs := [5870], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5869 5870 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5872 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5872 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5870) (initSM 5871) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5872 5870 5871 880
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5870, 5871], outs := [5872] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5870 5871 5872)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5871 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5873 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5873 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5872) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5873 5872 881
    ({ rank := 0, op := "OpName.FW_view", ins := [5872], outs := [5873], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5872 5873)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5874 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5874 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5860) (denoteGraph_ringAttn sm_goal_3 initSM 5873) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5874 5860 5873 882
    ({ rank := 0, op := "OpName.FW_mul", ins := [5860, 5873], outs := [5874] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5860 5873 5874])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5875 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5875 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5855) (denoteGraph_ringAttn sm_goal_3 initSM 5874) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5875 5855 5874 883
    ({ rank := 0, op := "OpName.FW_add", ins := [5855, 5874], outs := [5875] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5855 5874 5875)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5876 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5876 =
      denoteGraph_ringAttn sm_goal_3 initSM 5875 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5876 5875 884
    ({ rank := 0, op := "OpName.FW_float", ins := [5875], outs := [5876] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5875 5876 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5877 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5877 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8541) (denoteGraph_ringAttn sm_goal_3 initSM 5876) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5877 8541 5876 885
    ({ rank := 0, op := "OpName.FW_add", ins := [8541, 5876], outs := [5877] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8541 5876 5877)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8541 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8541 =
      denoteGraph_ringAttn sm_goal_3 initSM 5844 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8541 5844 861
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5844], outs := [8537, 8541], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5844 8537 8541 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8552 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8552 =
      denoteGraph_ringAttn sm_goal_3 initSM 5846 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8552 5846 863
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5846 8548 8552 8556 8560 8564 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8556 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8556 =
      denoteGraph_ringAttn sm_goal_3 initSM 5846 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8556 5846 863
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5846 8548 8552 8556 8560 8564 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8560 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8560 =
      denoteGraph_ringAttn sm_goal_3 initSM 5846 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8560 5846 863
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5846 8548 8552 8556 8560 8564 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8564 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8564 =
      denoteGraph_ringAttn sm_goal_3 initSM 5846 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8564 5846 863
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5846 8548 8552 8556 8560 8564 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5844 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11437,
         denoteGraph_ringAttn pm_goal_3 initPM 11438])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11437).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11438).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5855 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11461,
         denoteGraph_ringAttn pm_goal_3 initPM 11462] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5845 = initPM 5845 := hb initGoal_5845 (by decide) rfl
  have hw5603sh : (initPM 5848).shape = [64, 1024] := by
    have hgh := hII initGoal_5848 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5848] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5608 : initSM 5853 = allGatherPrimDimN 0 2 0 [initPM 11457, initPM 11458] := by
    have hg := hII initGoal_5853 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5853, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 11457) (initPM 11458) []
        (by rw [h_ss_pm 11457 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5609 : initSM 5854 = allGatherPrimDimN 0 2 0 [initPM 11459, initPM 11460] := by
    have hg := hII initGoal_5854 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5854, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 11459) (initPM 11460) []
        (by rw [h_ss_pm 11459 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L22_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hrouter := sm_pm_router_commute_L22 initSM initPM hInit hcarry5599 h10577 h10578
  -- PM rms output shapes [2048, 1024]
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11441).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L22, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11442).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L22, rms_sh]; exact h10578
  -- PM nl output shapes [2048, 64]
  have h10589sh : (denoteGraph_ringAttn pm_goal_3 initPM 11449).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L22, denote_pm_goal_3_10583_L22, denote_pm_goal_3_10581_L22]
    exact nl_sh 2048 1024 64 _ (initPM 5848) (by rw [rms_sh]; exact h10577) hw5603sh
  have h10590sh : (denoteGraph_ringAttn pm_goal_3 initPM 11450).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L22, denote_pm_goal_3_10584_L22, denote_pm_goal_3_10582_L22]
    exact nl_sh 2048 1024 64 _ (initPM 5848) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5849).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10589sh
  -- MoE weight shapes
  have hw10597 : (initPM 11457).shape = [32,1024,1024] := h_ss_pm 11457 [32,1024,1024] (by decide)
  have hw10598 : (initPM 11458).shape = [32,1024,1024] := h_ss_pm 11458 [32,1024,1024] (by decide)
  have hw10599 : (initPM 11459).shape = [32,1024,512] := h_ss_pm 11459 [32,1024,512] (by decide)
  have hw10600 : (initPM 11460).shape = [32,1024,512] := h_ss_pm 11460 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10591canon : denoteGraph_ringAttn pm_goal_3 initPM 11451
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11449) 8 64).fst := by
    rw [br_pm_11451,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11449).shape.reverse.head?).getD 1 = 64 from by rw [h10589sh]; rfl]
  have h10592canon : denoteGraph_ringAttn pm_goal_3 initPM 11452
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11450) 8 64).fst := by
    rw [br_pm_11452,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11450).shape.reverse.head?).getD 1 = 64 from by rw [h10590sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10591sh : (denoteGraph_ringAttn pm_goal_3 initPM 11451).shape = [2048, 64] := by
    rw [h10591canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10589sh]; rfl)
  have h10592sh : (denoteGraph_ringAttn pm_goal_3 initPM 11452).shape = [2048, 64] := by
    rw [h10592canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10590sh]; rfl)
  have h10593canon : denoteGraph_ringAttn pm_goal_3 initPM 11453
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11449) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593_L22,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11449).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10589sh]; rfl]
  have h10594canon : denoteGraph_ringAttn pm_goal_3 initPM 11454
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11450) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594_L22,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11450).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10590sh]; rfl]
  have h10593sh : (denoteGraph_ringAttn pm_goal_3 initPM 11453).shape = [2048, 64] := by
    rw [h10593canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10589sh
  have h10594sh : (denoteGraph_ringAttn pm_goal_3 initPM 11454).shape = [2048, 64] := by
    rw [h10594canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10590sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 11441) (denoteGraph_ringAttn pm_goal_3 initPM 11442)
    (denoteGraph_ringAttn pm_goal_3 initPM 11451) (denoteGraph_ringAttn pm_goal_3 initPM 11452)
    (denoteGraph_ringAttn pm_goal_3 initPM 11453) (denoteGraph_ringAttn pm_goal_3 initPM 11454)
    (initPM 11457) (initPM 11458) (initPM 11459) (initPM 11460)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10581sh h10582sh h10591sh h10592sh h10593sh h10594sh hw10597 hw10598 hw10599 hw10600
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_11461, br_pm_11462, br_pm_16788, br_pm_16811,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5855, br_sm_8552, denote_sm_goal_3_5601_L22, br_sm_5850]
  rw [hrouter, h5608, h5609]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5849).shape.reverse.head?).getD 1 = 64 from by rw [hSM5604sh]; rfl]
  rw [hw5600, hcarry5599, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5845) 2048 1024 (by omega) (by omega) h10577 h10578]
  rw [← denote_pm_goal_3_10581_L22, ← denote_pm_goal_3_10582_L22]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10589sh h10590sh]
  rw [← h10591canon, ← h10592canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L22_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5844 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11437,
         denoteGraph_ringAttn pm_goal_3 initPM 11438])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11437).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11438).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5874
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11535,
           denoteGraph_ringAttn pm_goal_3 initPM 11536] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5845 = initPM 5845 := hb initGoal_5845 (by decide) rfl
  have hw5612 : initSM 5857 = initPM 5857 := hb initGoal_5857 (by decide) rfl
  have hw5617 : initSM 5862 = initPM 5862 := hb initGoal_5862 (by decide) rfl
  have hw5621 : initSM 5866 = initPM 5866 := hb initGoal_5866 (by decide) rfl
  have hw5626 : initSM 5871 = initPM 5871 := hb initGoal_5871 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5844) (initSM 5845)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11441,
           denoteGraph_ringAttn pm_goal_3 initPM 11442] := by
    rw [hcarry5599, hw5600,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5845) 2048 1024 (by omega) (by omega) h10577 h10578,
        ← denote_pm_goal_3_10581_L22, ← denote_pm_goal_3_10582_L22]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 11441 / 11442
  rw [br_pm_11535, br_pm_11536,
      br_pm_11475, br_pm_11473, br_pm_11467, br_pm_11463, br_pm_16792,
      br_pm_11531, br_pm_11521, br_pm_11515, br_pm_11513,
      br_pm_11491, br_pm_11481, br_pm_11477, br_pm_16796,
      br_pm_11509, br_pm_11499, br_pm_11495, br_pm_16800,
      br_pm_11476, br_pm_11474, br_pm_11468, br_pm_11464, br_pm_16815,
      br_pm_11532, br_pm_11522, br_pm_11516, br_pm_11514,
      br_pm_11492, br_pm_11482, br_pm_11478, br_pm_16819,
      br_pm_11510, br_pm_11500, br_pm_11496, br_pm_16823]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5846
  rw [br_sm_5874, br_sm_5860, br_sm_5859, br_sm_5858,
      br_sm_5856, br_sm_8556,
      br_sm_5873, br_sm_5872, br_sm_5870, br_sm_5869,
      br_sm_5864, br_sm_5863, br_sm_5861, br_sm_8560,
      br_sm_5868, br_sm_5867, br_sm_5865, br_sm_8564,
      denote_sm_goal_3_5601_L22]
  rw [hRMS, hw5612, hw5617, hw5621, hw5626]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 11441 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 11442 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581_L22, rms_sh]; exact h10577
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582_L22, rms_sh]; exact h10578
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5857).shape = [1, 1024] := h_ss_pm 5857 [1, 1024] (by decide)
  have hw29 : (initPM 5862).shape = [512, 1024] := h_ss_pm 5862 [512, 1024] (by decide)
  have hw33 : (initPM 5866).shape = [512, 1024] := h_ss_pm 5866 [512, 1024] (by decide)
  have hw38 : (initPM 5871).shape = [1024, 512] := h_ss_pm 5871 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5857) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5862) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5866) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5857)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5857)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5862)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5862)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5866)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5866)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5857), fw_linear (fw_view [2048, 1024] B) (initPM 5857)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5857)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5857))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5862), fw_linear (fw_view [2048, 1024] B) (initPM 5862)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5866), fw_linear (fw_view [2048, 1024] B) (initPM 5866)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5857)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5857)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5871) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866))))) (initPM 5871)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))))) (initPM 5871)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866))))) (initPM 5871), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))))) (initPM 5871)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866))))) (initPM 5871)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))))) (initPM 5871))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5857))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5857))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5866))))) (initPM 5871)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5862))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5866))))) (initPM 5871)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11549_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11549).shape = [2048, 1024] := by
  have h10517 := hbase345
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11433).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L22, denote_pm_goal_3_10569_L22]; rfl
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11437).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L22]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10517 h10573
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11441).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L22, rms_sh]; exact h10577
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 11461).shape = [2048, 1024] := by
    rw [br_pm_11461, br_pm_16788]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 11475).shape = [2048, 1] := by
    rw [br_pm_11475, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11473]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 11531).shape = [2048, 1024] := by
    rw [br_pm_11531]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 11535).shape = [2048, 1024] := by
    rw [br_pm_11535, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11461) (denoteGraph_ringAttn pm_goal_3 initPM 11535)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have h16379sh : (denoteGraph_ringAttn pm_goal_3 initPM 16769).shape = [2048, 1024] := by
    rw [br_pm_16769]; exact h10577
  have h10685sh : (denoteGraph_ringAttn pm_goal_3 initPM 11545).shape = [2048, 1024] := by
    rw [br_pm_11545, br_pm_11539]; exact hinnerA
  rw [br_pm_11549]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16379sh h10685sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11550_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11550).shape = [2048, 1024] := by
  have h10518 := hbase346
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11434).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L22, denote_pm_goal_3_10570_L22]; rfl
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11438).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L22]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10518 h10574
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11442).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L22, rms_sh]; exact h10578
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 11462).shape = [2048, 1024] := by
    rw [br_pm_11462, br_pm_16811]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 11476).shape = [2048, 1] := by
    rw [br_pm_11476, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11474]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 11532).shape = [2048, 1024] := by
    rw [br_pm_11532]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 11536).shape = [2048, 1024] := by
    rw [br_pm_11536, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11462) (denoteGraph_ringAttn pm_goal_3 initPM 11536)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  have h16387sh : (denoteGraph_ringAttn pm_goal_3 initPM 16777).shape = [2048, 1024] := by
    rw [br_pm_16777]; exact h10578
  have h10686sh : (denoteGraph_ringAttn pm_goal_3 initPM 11546).shape = [2048, 1024] := by
    rw [br_pm_11546, br_pm_11540]; exact hinnerB
  rw [br_pm_11550]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16387sh h10686sh

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L22_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L22_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L22
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L22_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L22
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L22_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L22_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L22_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L22_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L22_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11549_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11550_shape
