/-
  Pattern_3_L21_spike.lean — L21 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L21-specific TIDs.  The L21 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L21's Q path
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

/-! ## L21 attention node declarations + buddy proofs.
SM attn node index 819; PM r0 = 1697; PM r1 = 1698. -/

def nSM_21 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5783, 5784, 5785, 5786, 5787], outs := [5788],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_21 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11211, 5784, 5785, 5786, 5787], outs := [11235],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11212, 5784, 5785, 5786, 5787], outs := [11236],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_21 : ringAttnBuddies sm_goal_3 nSM_21 = [nSM_21] := by
  show (List.filter (fun m => decide (m.op = nSM_21.op) && decide (m.params = nSM_21.params) &&
      decide (m.ins.getD 3 0 = nSM_21.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_21.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_21]
  rw [show (List.filter (fun m => decide (m.op = nSM_21.op) && decide (m.params = nSM_21.params) &&
      decide (m.ins.getD 3 0 = nSM_21.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_21.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_21] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_21 : ringAttnBuddies pm_goal_3 nR0_21 = [nR0_21, nR1_21] := by
  show (List.filter (fun m => decide (m.op = nR0_21.op) && decide (m.params = nR0_21.params) &&
      decide (m.ins.getD 3 0 = nR0_21.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_21.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_21, nR1_21]
  rw [show (List.filter (fun m => decide (m.op = nR0_21.op) && decide (m.params = nR0_21.params) &&
      decide (m.ins.getD 3 0 = nR0_21.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_21.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_21, nR1_21] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_21 : ringAttnBuddies pm_goal_3 nR1_21 = [nR0_21, nR1_21] := by
  show (List.filter (fun m => decide (m.op = nR1_21.op) && decide (m.params = nR1_21.params) &&
      decide (m.ins.getD 3 0 = nR1_21.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_21.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_21, nR1_21]
  rw [show (List.filter (fun m => decide (m.op = nR1_21.op) && decide (m.params = nR1_21.params) &&
      decide (m.ins.getD 3 0 = nR1_21.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_21.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_21, nR1_21] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L21 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L21_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5788
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_21 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5788
      = (sm_goal_3.nodes.take 820).foldl (applyNodeRingAttn sm_goal_3) initSM 5788 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5788 820 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 820 = sm_goal_3.nodes.take 819 ++ [nSM_21] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5783 5784 5785 5786 5787 5788 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L21_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11235
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_21 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11235
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11235 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11235 1698 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1698 = pm_goal_3.nodes.take 1697 ++ [nR0_21] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 11211 5784 5785 5786 5787 11235 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L21_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11236
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_21 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11236
      = (pm_goal_3.nodes.take 1699).foldl (applyNodeRingAttn pm_goal_3) initPM 11236 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11236 1699 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1699 = pm_goal_3.nodes.take 1698 ++ [nR1_21] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 11212 5784 5785 5786 5787 11236 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L21) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5781 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5779) (initSM 5780) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5781 8490 5780 817
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8490, 5780], outs := [5781] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8490 5780 5781)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8490 5779 816
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5779], outs := [8490, 8494], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5779 8490 [8490, 8494] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5780 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5783 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5781) (initSM 5782) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5783 5781 5782 818
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5781, 5782], outs := [5783] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5781 5782 5783 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5782 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5789 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5788) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5789 5788 820
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5788], outs := [5789], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5788 5789 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5790 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5789) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5790 5789 821
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5789], outs := [5790], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5789 5790 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5792 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5790) (initSM 5791) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5792 5790 5791 822
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5790, 5791], outs := [5792] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5790 5791 5792)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5791 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5793 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5792) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5793 5792 823
    ({ rank := 0, op := "OpName.FW_view", ins := [5792], outs := [5793], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5792 5793)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5794 =
      denoteGraph_ringAttn sm_goal_3 initSM 5793 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5794 5793 824
    ({ rank := 0, op := "OpName.FW_float", ins := [5793], outs := [5794] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5793 5794 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5795 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5779)
        (denoteGraph_ringAttn sm_goal_3 initSM 5794) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8494 = denoteGraph_ringAttn sm_goal_3 initSM 5779 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8494 5779 816
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5779], outs := [8490, 8494], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5779 8494 [8490, 8494] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5795 8494 5794 825
    ({ rank := 0, op := "OpName.FW_add", ins := [8494, 5794], outs := [5795] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8494 5794 5795)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5797 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5795) (initSM 5796) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5797 8498 5796 827
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8498, 5796], outs := [5797] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8498 5796 5797)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8498 5795 826
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5795], outs := [8498, 8502], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5795 8498 [8498, 8502] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5796 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5798 =
      denoteGraph_ringAttn sm_goal_3 initSM 5797 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5798 8509 829
    ({ rank := 0, op := "OpName.FW_float", ins := [8509], outs := [5798] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8509 5798 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8509 5797 828
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5797 8509 [8509, 8513, 8517, 8521, 8525] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5800 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5798) (initSM 5799) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5800 5798 5799 833
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5798, 5799], outs := [5800] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5798 5799 5800 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5799 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5802 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5800) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5800).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5802 5800 837
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5800], outs := [5801, 5802, 5803], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5800 5801 5802 5803 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5784 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5784 8069 489
    ({ rank := 0, op := "OpName.FW_to", ins := [8069], outs := [5784] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8069 5784 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8069 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8069 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589_L21 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5785 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5785 8127 501
    ({ rank := 0, op := "OpName.FW_to", ins := [8127], outs := [5785] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8127 5785 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8127 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8127 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L21) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11209 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11205) (initPM 5780) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11209 16671 5780 1693
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16671, 5780], outs := [11209] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16671 5780 11209)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16671 11205 1691
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671, 16675], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11205 16671 [16671, 16675] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5780 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11211 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11209) (initPM 5782) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11211 11209 5782 1695
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11209, 5782], outs := [11211] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 11209 5782 11211 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5782 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11237 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11235) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11237 11235 1699
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11235], outs := [11237], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11235 11237 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11243 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11237) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11243 11237 1701
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11237], outs := [11243], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11237 11243 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11247 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11243) (initPM 5791) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11247 11243 5791 1703
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11243, 5791], outs := [11247] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11243 5791 11247)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5791 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11257 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11247) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11257 11247 1705
    ({ rank := 0, op := "OpName.FW_view", ins := [11247], outs := [11257], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11247 11257)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11261 =
      denoteGraph_ringAttn pm_goal_3 initPM 11257 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11261 11257 1707
    ({ rank := 0, op := "OpName.FW_float", ins := [11257], outs := [11261] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11257 11261 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11265 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11205)
        (denoteGraph_ringAttn pm_goal_3 initPM 11261) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16675 = denoteGraph_ringAttn pm_goal_3 initPM 11205 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16675 11205 1691
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671, 16675], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11205 16675 [16671, 16675] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11265 16675 11261 1709
    ({ rank := 0, op := "OpName.FW_add", ins := [16675, 11261], outs := [11265] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16675 11261 11265)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11269 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11265) (initPM 5796) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11269 16687 5796 1713
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16687, 5796], outs := [11269] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16687 5796 11269)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16687 11265 1711
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11265], outs := [16687, 16691], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11265 16687 [16687, 16691] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5796 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11271 =
      denoteGraph_ringAttn pm_goal_3 initPM 11269 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11271 16706 1717
    ({ rank := 0, op := "OpName.FW_float", ins := [16706], outs := [11271] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16706 11271 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16706 11269 1715
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11269 16706 [16706, 16710, 16714, 16718, 16722] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11277 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11271) (initPM 5799) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11277 11271 5799 1725
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [11271, 5799], outs := [11277] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 11271 5799 11277 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5799 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11281 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11277) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11277).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11281 11277 1733
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11277], outs := [11279, 11281, 11283], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 11277 11279 11281 11283 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11210 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11206) (initPM 5780) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11210 16679 5780 1694
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16679, 5780], outs := [11210] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16679 5780 11210)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16679 11206 1692
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679, 16683], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11206 16679 [16679, 16683] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5780 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11212 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11210) (initPM 5782) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11212 11210 5782 1696
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11210, 5782], outs := [11212] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 11210 5782 11212 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5782 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11238 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11236) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11238 11236 1700
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11236], outs := [11238], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11236 11238 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11244 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11238) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11244 11238 1702
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11238], outs := [11244], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11238 11244 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11248 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11244) (initPM 5791) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11248 11244 5791 1704
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11244, 5791], outs := [11248] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11244 5791 11248)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5791 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11258 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11248) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11258 11248 1706
    ({ rank := 1, op := "OpName.FW_view", ins := [11248], outs := [11258], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11248 11258)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11262 =
      denoteGraph_ringAttn pm_goal_3 initPM 11258 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11262 11258 1708
    ({ rank := 1, op := "OpName.FW_float", ins := [11258], outs := [11262] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11258 11262 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11266 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11206)
        (denoteGraph_ringAttn pm_goal_3 initPM 11262) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16683 = denoteGraph_ringAttn pm_goal_3 initPM 11206 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16683 11206 1692
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679, 16683], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11206 16683 [16679, 16683] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11266 16683 11262 1710
    ({ rank := 1, op := "OpName.FW_add", ins := [16683, 11262], outs := [11266] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16683 11262 11266)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11270 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11266) (initPM 5796) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11270 16695 5796 1714
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16695, 5796], outs := [11270] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16695 5796 11270)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16695 11266 1712
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11266], outs := [16695, 16699], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11266 16695 [16695, 16699] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5796 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11272 =
      denoteGraph_ringAttn pm_goal_3 initPM 11270 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11272 16729 1721
    ({ rank := 1, op := "OpName.FW_float", ins := [16729], outs := [11272] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16729 11272 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16729 11270 1716
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11270 16729 [16729, 16733, 16737, 16741, 16745] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11278 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11272) (initPM 5799) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11278 11272 5799 1729
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [11272, 5799], outs := [11278] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 11272 5799 11278 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5799 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11282 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11278) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11278).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11282 11278 1737
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11278], outs := [11280, 11282, 11284], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 11278 11280 11282 11284 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5784 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5784 15851 1040
    ({ rank := 1, op := "OpName.FW_to", ins := [15851], outs := [5784] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15851 5784 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15851 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15851 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589_L21 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5785 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5785 15957 1064
    ({ rank := 1, op := "OpName.FW_to", ins := [15957], outs := [5785] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15957 5785 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15957 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15957 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L21 commute theorems -/

-- Q sharding commute: SM 5783 = allGather0[PM 11211, PM 11212].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11205,
         denoteGraph_ringAttn pm_goal_3 initPM 11206])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024])
    (hw5586 : (initPM 5782).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5783 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11211,
         denoteGraph_ringAttn pm_goal_3 initPM 11212] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5780 = initPM 5780 := hb initGoal_5780 (by decide) rfl
  have hw5586e : initSM 5782 = initPM 5782 := hb initGoal_5782 (by decide) rfl
  rw [denote_sm_goal_3_5587_L21, denote_sm_goal_3_5585_L21,
      denote_pm_goal_3_10523_L21, denote_pm_goal_3_10521_L21,
      denote_pm_goal_3_10524_L21, denote_pm_goal_3_10522_L21]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11205) (initPM 5780)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11206) (initPM 5780)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5780) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5782) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape_L21 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5784).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588_L21, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape_L21 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5785).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589_L21, denote_pm_goal_3_5336]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))

-- K/V replication (cross-graph, full tensor): SM 5784 = PM 5784, SM 5785 = PM 5785.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5784 =
      denoteGraph_ringAttn pm_goal_3 initPM 5784 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588_L21, denote_pm_goal_3_5588_L21, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5785 =
      denoteGraph_ringAttn pm_goal_3 initPM 5785 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589_L21, denote_pm_goal_3_5589_L21, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L21 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L21_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11205,
         denoteGraph_ringAttn pm_goal_3 initPM 11206])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5787)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5788 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11235,
         denoteGraph_ringAttn pm_goal_3 initPM 11236] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5782).shape = [16, 64, 1024] := hPM 5782 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L21_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L21_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L21_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape_L21 initPM hPM
  have hVsh := pm_5589_shape_L21 initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11209).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L21, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11210).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L21, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 11211).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L21]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 11212).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L21]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5783).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5783).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5784).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5785).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 819)
  have bSM5587 : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5783 = denoteGraph_ringAttn sm_goal_3 initSM 5783 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5783 819 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5784 = denoteGraph_ringAttn sm_goal_3 initSM 5784 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5784 819 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5785 = denoteGraph_ringAttn sm_goal_3 initSM 5785 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5785 819 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1697)
  have bPM10523 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11211 = denoteGraph_ringAttn pm_goal_3 initPM 11211 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11211 1697 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11212 = denoteGraph_ringAttn pm_goal_3 initPM 11212 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11212 1697 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5784 = denoteGraph_ringAttn pm_goal_3 initPM 5784 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5784 1697 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5785 = denoteGraph_ringAttn pm_goal_3 initPM 5785 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5785 1697 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5786 = initSM 5786 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 819) initSM 5786 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5787 = initSM 5787 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 819) initSM 5787 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5786 = initPM 5786 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1697) initPM 5786 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5787 = initPM 5787 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1697) initPM 5787 (by decide) (by decide)
  have hw5590 : initSM 5786 = initPM 5786 := hb initGoal_5786 (by decide) rfl
  have hw5591 : initSM 5787 = initPM 5787 := hb initGoal_5787 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5783).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5784).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5785).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
        (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5783 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11211,
        (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11212]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5784 =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5784
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5785 =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5785
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5784).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5785).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5787)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5786 =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5786
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_21.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM 5787 =
      (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5787
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
       (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11211,
       (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11212]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
          (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 1 0),
          (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 2 0),
          (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 4 0))
        (nR0_21.params.getD 0 1) (nR0_21.params.getD 1 1) (nR0_21.params.getD 2 1) (nR0_21.params.getD 3 1)
        (decide (nR0_21.params.getD 4 0 ≠ 0)) (nR0_21.params.getD 5 0)).shape
        = [2 * 2048, nR0_21.params.getD 0 1, nR0_21.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1697 -> take 1698)
  have e10523 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11211
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11211 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11211 1697 1698 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11212
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11212 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11212 1697 1698 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5784
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 5784 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5784 1697 1698 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5785
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 5785 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5785 1697 1698 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5786
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 5786 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5786 1697 1698 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 5787
      = (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 5787 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5787 1697 1698 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_21
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_21 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_21]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_21]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_21]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 819).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_21 nR0_21 nR1_21 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_21 buddy_r0_21 buddy_r1_21 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L21_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L21_r0_bridge, ← denote_pm_attn_L21_r1_bridge]


/-! ## L21 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5788 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11235,
         denoteGraph_ringAttn pm_goal_3 initPM 11236])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11235).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11236).shape = [2048, 16, 64])
    (hw5595 : (initPM 5791).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5794 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11261,
         denoteGraph_ringAttn pm_goal_3 initPM 11262] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5791 = initPM 5791 := hb initGoal_5791 (by decide) rfl
  rw [denote_sm_goal_3_5598_L21, denote_sm_goal_3_5597_L21, denote_sm_goal_3_5596_L21,
      denote_sm_goal_3_5594_L21, denote_sm_goal_3_5593_L21,
      denote_pm_goal_3_10573_L21, denote_pm_goal_3_10569_L21, denote_pm_goal_3_10559_L21,
      denote_pm_goal_3_10555_L21, denote_pm_goal_3_10549_L21,
      denote_pm_goal_3_10574_L21, denote_pm_goal_3_10570_L21, denote_pm_goal_3_10560_L21,
      denote_pm_goal_3_10556_L21, denote_pm_goal_3_10550_L21]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11235))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11236))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5791) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11235))) (initPM 5791)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11236))) (initPM 5791)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11235))) (initPM 5791),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11236))) (initPM 5791)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute_L21 (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11205,
         denoteGraph_ringAttn pm_goal_3 initPM 11206])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5794 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11261,
         denoteGraph_ringAttn pm_goal_3 initPM 11262])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11261).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11262).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5795 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11265,
         denoteGraph_ringAttn pm_goal_3 initPM 11266] := by
  rw [denote_sm_goal_3_5599_L21, denote_pm_goal_3_10577_L21, denote_pm_goal_3_10578_L21]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5795 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11265,
         denoteGraph_ringAttn pm_goal_3 initPM 11266])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5800 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11277,
         denoteGraph_ringAttn pm_goal_3 initPM 11278] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5796 = initPM 5796 := hb initGoal_5796 (by decide) rfl
  have hw5603 : initSM 5799 = initPM 5799 := hb initGoal_5799 (by decide) rfl
  have hw5603sh : (initPM 5799).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5799 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5799] using hsh
  rw [denote_sm_goal_3_5604_L21, denote_sm_goal_3_5602_L21, denote_sm_goal_3_5601_L21,
      denote_pm_goal_3_10589_L21, denote_pm_goal_3_10583_L21, denote_pm_goal_3_10581_L21,
      denote_pm_goal_3_10590_L21, denote_pm_goal_3_10584_L21, denote_pm_goal_3_10582_L21]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5796) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11265) (initPM 5796)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11266) (initPM 5796)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5799) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L21 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5795 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11265,
         denoteGraph_ringAttn pm_goal_3 initPM 11266])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5802 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11281,
         denoteGraph_ringAttn pm_goal_3 initPM 11282] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5799).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5799 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5799] using hsh
  have hnl := sm_pm_nl_L21_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 11277).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L21, denote_pm_goal_3_10583_L21, denote_pm_goal_3_10581_L21]
    exact nl_sh 2048 1024 64 _ (initPM 5799) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 11278).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L21, denote_pm_goal_3_10584_L21, denote_pm_goal_3_10582_L21]
    exact nl_sh 2048 1024 64 _ (initPM 5799) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5800).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606_L21, denote_pm_goal_3_10593_L21, denote_pm_goal_3_10594_L21]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5800).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11277).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11278).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L21 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L21_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11205,
         denoteGraph_ringAttn pm_goal_3 initPM 11206])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5788 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11235,
         denoteGraph_ringAttn pm_goal_3 initPM 11236])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11235).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11236).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024])
    (hw5595 : (initPM 5791).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5802 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11281,
         denoteGraph_ringAttn pm_goal_3 initPM 11282] := by
  have hreshape := sm_pm_reshape_float_L21_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11261).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L21, denote_pm_goal_3_10569_L21]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11262).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L21, denote_pm_goal_3_10570_L21]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L21 initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L21]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L21]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L21 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L21 router — fully assembled

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
theorem sm_pm_router_commute_L21_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5787)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11205,
         denoteGraph_ringAttn pm_goal_3 initPM 11206])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5802 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11281,
         denoteGraph_ringAttn pm_goal_3 initPM 11282] := by
  have hattn := sm_pm_attention_L21_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5782).shape = [16, 64, 1024] := hPM 5782 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5791).shape = [1024, 1024] := hPM 5791 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 11209).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L21, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 11210).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L21, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 11211).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L21]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 11212).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L21]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11211
      = denoteGraph_ringAttn pm_goal_3 initPM 11211 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11211 1697 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11212
      = denoteGraph_ringAttn pm_goal_3 initPM 11212 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11212 1697 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11211
      = denoteGraph_ringAttn pm_goal_3 initPM 11211 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11211 1698 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11212
      = denoteGraph_ringAttn pm_goal_3 initPM 11212 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11212 1698 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 11235).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L21_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_21 nR0_21 nR1_21 0 buddy_r0_21 (by decide)]
    have e0 : nR0_21.ins.getD 0 0 = 11211 := by decide
    have e1 : nR1_21.ins.getD 0 0 = 11212 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
         (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 11236).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L21_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_21 nR0_21 nR1_21 1 buddy_r1_21 (by decide)]
    have e0 : nR0_21.ins.getD 0 0 = 11211 := by decide
    have e1 : nR1_21.ins.getD 0 0 = 11212 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
         (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L21_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L21_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5787)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _


-- ================= L21 MoE carry (sm_pm_carry_5828_commute) =================
theorem br_pm_16675 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16675 = denoteGraph_ringAttn pm_goal_3 initPM 11205 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16675 11205 1691
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671, 16675], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11205 16675 [16671, 16675] 2 (by decide) (by decide))
    rfl

theorem br_pm_16683 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16683 = denoteGraph_ringAttn pm_goal_3 initPM 11206 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16683 11206 1692
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679, 16683], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11206 16683 [16679, 16683] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11279 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11279 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11277) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 11277).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11279 11277 1733
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11277], outs := [11279, 11281, 11283], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 11277 11279 11281 11283 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11280 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11280 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11278) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 11278).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11280 11278 1737
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11278], outs := [11280, 11282, 11284], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 11278 11280 11282 11284 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11289 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11289 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16710)
        (denoteGraph_ringAttn pm_goal_3 initPM 11279)
        (denoteGraph_ringAttn pm_goal_3 initPM 11281)
        [initPM 11285, initPM 11286] [initPM 11287, initPM 11288]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 11289 16710 11279 11281 11285 11286 11287 11288 1741
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16710, 11279, 11281, 11285, 11286, 11287, 11288], outs := [11289], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16710 11279 11281 11285 11286 11287 11288 11289 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11285 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11286 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11287 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11288 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11290 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11290 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16733)
        (denoteGraph_ringAttn pm_goal_3 initPM 11280)
        (denoteGraph_ringAttn pm_goal_3 initPM 11282)
        [initPM 11285, initPM 11286] [initPM 11287, initPM 11288]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 11290 16733 11280 11282 11285 11286 11287 11288 1744
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16733, 11280, 11282, 11285, 11286, 11287, 11288], outs := [11290], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16733 11280 11282 11285 11286 11287 11288 11290 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11285 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11286 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11287 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 11288 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11291 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11291 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16714) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11291 16714 1718
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16714], outs := [11291], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16714 11291 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11292 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11292 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16737) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11292 16737 1722
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16737], outs := [11292], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16737 11292 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11295 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11295 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11291) (initPM 5808) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11295 11291 5808 1726
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11291, 5808], outs := [11295] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11291 5808 11295)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5808 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11296 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11296 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11292) (initPM 5808) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11296 11292 5808 1730
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11292, 5808], outs := [11296] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11292 5808 11296)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5808 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11301 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11301 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 11295) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11301 11295 1734
    ({ rank := 0, op := "OpName.FW_view", ins := [11295], outs := [11301], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 11295 11301)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11302 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11302 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 11296) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11302 11296 1738
    ({ rank := 1, op := "OpName.FW_view", ins := [11296], outs := [11302], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 11296 11302)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11303 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11303 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 11301) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11303 11301 1742
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [11301], outs := [11303] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 11301 11303])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11304 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11304 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 11302) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11304 11302 1745
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [11302], outs := [11304] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 11302 11304])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11305 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11305 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16718) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11305 16718 1719
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16718], outs := [11305], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16718 11305 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11306 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11306 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16741) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11306 16741 1723
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16741], outs := [11306], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16741 11306 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11309 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11309 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11305) (initPM 5813) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11309 11305 5813 1727
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11305, 5813], outs := [11309] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11305 5813 11309)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5813 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11310 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11310 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11306) (initPM 5813) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11310 11306 5813 1731
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11306, 5813], outs := [11310] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11306 5813 11310)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5813 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11319 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11319 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11309) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11319 11309 1735
    ({ rank := 0, op := "OpName.FW_view", ins := [11309], outs := [11319], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 11309 11319)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11320 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11320 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11310) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11320 11310 1739
    ({ rank := 1, op := "OpName.FW_view", ins := [11310], outs := [11320], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 11310 11320)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11323 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11323 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16722) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11323 16722 1720
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16722], outs := [11323], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16722 11323 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11324 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11324 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16745) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11324 16745 1724
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16745], outs := [11324], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16745 11324 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11327 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11327 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11323) (initPM 5817) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11327 11323 5817 1728
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11323, 5817], outs := [11327] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11323 5817 11327)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5817 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11328 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11328 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11324) (initPM 5817) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11328 11324 5817 1732
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11324, 5817], outs := [11328] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11324 5817 11328)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5817 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11337 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11337 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11327) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11337 11327 1736
    ({ rank := 0, op := "OpName.FW_view", ins := [11327], outs := [11337], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 11327 11337)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11338 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11338 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11328) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11338 11328 1740
    ({ rank := 1, op := "OpName.FW_view", ins := [11328], outs := [11338], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 11328 11338)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11341 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11341 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 11319) (denoteGraph_ringAttn pm_goal_3 initPM 11337) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11341 11319 11337 1743
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [11319, 11337], outs := [11341] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 11319 11337 11341])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11342 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11342 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 11320) (denoteGraph_ringAttn pm_goal_3 initPM 11338) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11342 11320 11338 1746
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [11320, 11338], outs := [11342] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 11320 11338 11342])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11343 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11343 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11341) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11343 11341 1747
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11341], outs := [11343], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11341 11343 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11344 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11344 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 11342) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11344 11342 1748
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11342], outs := [11344], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11342 11344 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11349 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11349 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11343) (initPM 5822) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11349 11343 5822 1749
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11343, 5822], outs := [11349] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11343 5822 11349)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5822 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11350 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11350 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11344) (initPM 5822) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11350 11344 5822 1750
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11344, 5822], outs := [11350] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11344 5822 11350)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5822 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11359 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11359 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11349) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11359 11349 1751
    ({ rank := 0, op := "OpName.FW_view", ins := [11349], outs := [11359], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11349 11359)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11360 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11360 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11350) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11360 11350 1752
    ({ rank := 1, op := "OpName.FW_view", ins := [11350], outs := [11360], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11350 11360)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11363 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11363 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 11303) (denoteGraph_ringAttn pm_goal_3 initPM 11359) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11363 11303 11359 1753
    ({ rank := 0, op := "OpName.FW_mul", ins := [11303, 11359], outs := [11363] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 11303 11359 11363])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11364 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11364 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 11304) (denoteGraph_ringAttn pm_goal_3 initPM 11360) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11364 11304 11360 1754
    ({ rank := 1, op := "OpName.FW_mul", ins := [11304, 11360], outs := [11364] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 11304 11360 11364])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11367 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11367 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11289) (denoteGraph_ringAttn pm_goal_3 initPM 11363) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11367 11289 11363 1755
    ({ rank := 0, op := "OpName.FW_add", ins := [11289, 11363], outs := [11367] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 11289 11363 11367)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11368 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11368 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11290) (denoteGraph_ringAttn pm_goal_3 initPM 11364) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11368 11290 11364 1756
    ({ rank := 1, op := "OpName.FW_add", ins := [11290, 11364], outs := [11368] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 11290 11364 11368)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11373 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11373 =
      denoteGraph_ringAttn pm_goal_3 initPM 11367 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11373 11367 1757
    ({ rank := 0, op := "OpName.FW_float", ins := [11367], outs := [11373] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11367 11373 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11374 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11374 =
      denoteGraph_ringAttn pm_goal_3 initPM 11368 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11374 11368 1758
    ({ rank := 1, op := "OpName.FW_float", ins := [11368], outs := [11374] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11368 11374 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11377 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11377 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16691) (denoteGraph_ringAttn pm_goal_3 initPM 11373) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11377 16691 11373 1759
    ({ rank := 0, op := "OpName.FW_add", ins := [16691, 11373], outs := [11377] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16691 11373 11377)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11378 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11378 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16699) (denoteGraph_ringAttn pm_goal_3 initPM 11374) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11378 16699 11374 1760
    ({ rank := 1, op := "OpName.FW_add", ins := [16699, 11374], outs := [11378] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16699 11374 11378)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16691 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16691 =
      denoteGraph_ringAttn pm_goal_3 initPM 11265 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16691 11265 1711
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11265], outs := [16687, 16691], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 11265 16687 16691 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16699 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16699 =
      denoteGraph_ringAttn pm_goal_3 initPM 11266 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16699 11266 1712
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11266], outs := [16695, 16699], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 11266 16695 16699 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16710 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16710 =
      denoteGraph_ringAttn pm_goal_3 initPM 11269 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16710 11269 1715
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 11269 16706 16710 16714 16718 16722 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16714 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16714 =
      denoteGraph_ringAttn pm_goal_3 initPM 11269 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16714 11269 1715
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 11269 16706 16710 16714 16718 16722 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16718 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16718 =
      denoteGraph_ringAttn pm_goal_3 initPM 11269 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16718 11269 1715
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 11269 16706 16710 16714 16718 16722 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16722 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16722 =
      denoteGraph_ringAttn pm_goal_3 initPM 11269 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16722 11269 1715
    ({ rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 11269 16706 16710 16714 16718 16722 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16733 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16733 =
      denoteGraph_ringAttn pm_goal_3 initPM 11270 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16733 11270 1716
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 11270 16729 16733 16737 16741 16745 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16737 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16737 =
      denoteGraph_ringAttn pm_goal_3 initPM 11270 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16737 11270 1716
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 11270 16729 16733 16737 16741 16745 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16741 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16741 =
      denoteGraph_ringAttn pm_goal_3 initPM 11270 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16741 11270 1716
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 11270 16729 16733 16737 16741 16745 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16745 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16745 =
      denoteGraph_ringAttn pm_goal_3 initPM 11270 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16745 11270 1716
    ({ rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 11270 16729 16733 16737 16741 16745 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5801 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5801 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5800) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5800).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5801 5800 837
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5800], outs := [5801, 5802, 5803], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5800 5801 5802 5803 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5806 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5806 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8513)
        (denoteGraph_ringAttn sm_goal_3 initSM 5801)
        (denoteGraph_ringAttn sm_goal_3 initSM 5802)
        (initSM 5804) (initSM 5805) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5806 8513 5801 5802 5804 5805 841
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8513, 5801, 5802, 5804, 5805], outs := [5806], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8513 5801 5802 5804 5805 5806 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5804 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5805 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5807 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5807 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8517) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5807 8517 830
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8517], outs := [5807], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8517 5807 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5809 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5809 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5807) (initSM 5808) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5809 5807 5808 834
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5807, 5808], outs := [5809] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5807 5808 5809)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5808 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5810 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5810 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5809) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5810 5809 838
    ({ rank := 0, op := "OpName.FW_view", ins := [5809], outs := [5810], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5809 5810)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5811 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5811 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5810) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5811 5810 842
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5810], outs := [5811] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5810 5811])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5812 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5812 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8521) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5812 8521 831
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8521], outs := [5812], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8521 5812 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5814 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5814 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5812) (initSM 5813) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5814 5812 5813 835
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5812, 5813], outs := [5814] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5812 5813 5814)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5813 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5815 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5815 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5814) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5815 5814 839
    ({ rank := 0, op := "OpName.FW_view", ins := [5814], outs := [5815], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5814 5815)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5816 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5816 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8525) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5816 8525 832
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8525], outs := [5816], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8525 5816 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5818 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5818 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5816) (initSM 5817) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5818 5816 5817 836
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5816, 5817], outs := [5818] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5816 5817 5818)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5817 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5819 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5819 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5818) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5819 5818 840
    ({ rank := 0, op := "OpName.FW_view", ins := [5818], outs := [5819], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5818 5819)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5820 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5820 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5815) (denoteGraph_ringAttn sm_goal_3 initSM 5819) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5820 5815 5819 843
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5815, 5819], outs := [5820] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5815 5819 5820])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5821 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5821 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5820) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5821 5820 844
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5820], outs := [5821], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5820 5821 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5823 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5823 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5821) (initSM 5822) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5823 5821 5822 845
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5821, 5822], outs := [5823] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5821 5822 5823)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5822 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5824 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5824 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5823) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5824 5823 846
    ({ rank := 0, op := "OpName.FW_view", ins := [5823], outs := [5824], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5823 5824)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5825 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5825 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5811) (denoteGraph_ringAttn sm_goal_3 initSM 5824) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5825 5811 5824 847
    ({ rank := 0, op := "OpName.FW_mul", ins := [5811, 5824], outs := [5825] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5811 5824 5825])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5826 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5826 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5806) (denoteGraph_ringAttn sm_goal_3 initSM 5825) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5826 5806 5825 848
    ({ rank := 0, op := "OpName.FW_add", ins := [5806, 5825], outs := [5826] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5806 5825 5826)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5827 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5827 =
      denoteGraph_ringAttn sm_goal_3 initSM 5826 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5827 5826 849
    ({ rank := 0, op := "OpName.FW_float", ins := [5826], outs := [5827] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5826 5827 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5828 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8502) (denoteGraph_ringAttn sm_goal_3 initSM 5827) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5828 8502 5827 850
    ({ rank := 0, op := "OpName.FW_add", ins := [8502, 5827], outs := [5828] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8502 5827 5828)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8502 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8502 =
      denoteGraph_ringAttn sm_goal_3 initSM 5795 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8502 5795 826
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5795], outs := [8498, 8502], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5795 8498 8502 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8513 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8513 =
      denoteGraph_ringAttn sm_goal_3 initSM 5797 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8513 5797 828
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5797 8509 8513 8517 8521 8525 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8517 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8517 =
      denoteGraph_ringAttn sm_goal_3 initSM 5797 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8517 5797 828
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5797 8509 8513 8517 8521 8525 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8521 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8521 =
      denoteGraph_ringAttn sm_goal_3 initSM 5797 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8521 5797 828
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5797 8509 8513 8517 8521 8525 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8525 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8525 =
      denoteGraph_ringAttn sm_goal_3 initSM 5797 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8525 5797 828
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5797 8509 8513 8517 8521 8525 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5795 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11265,
         denoteGraph_ringAttn pm_goal_3 initPM 11266])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5806 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11289,
         denoteGraph_ringAttn pm_goal_3 initPM 11290] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5796 = initPM 5796 := hb initGoal_5796 (by decide) rfl
  have hw5603sh : (initPM 5799).shape = [64, 1024] := by
    have hgh := hII initGoal_5799 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5799] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5608 : initSM 5804 = allGatherPrimDimN 0 2 0 [initPM 11285, initPM 11286] := by
    have hg := hII initGoal_5804 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5804, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 11285) (initPM 11286) []
        (by rw [h_ss_pm 11285 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5609 : initSM 5805 = allGatherPrimDimN 0 2 0 [initPM 11287, initPM 11288] := by
    have hg := hII initGoal_5805 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5805, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 11287) (initPM 11288) []
        (by rw [h_ss_pm 11287 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L21_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hrouter := sm_pm_router_commute_L21 initSM initPM hInit hcarry5599 h10577 h10578
  -- PM rms output shapes [2048, 1024]
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11269).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L21, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11270).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L21, rms_sh]; exact h10578
  -- PM nl output shapes [2048, 64]
  have h10589sh : (denoteGraph_ringAttn pm_goal_3 initPM 11277).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L21, denote_pm_goal_3_10583_L21, denote_pm_goal_3_10581_L21]
    exact nl_sh 2048 1024 64 _ (initPM 5799) (by rw [rms_sh]; exact h10577) hw5603sh
  have h10590sh : (denoteGraph_ringAttn pm_goal_3 initPM 11278).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L21, denote_pm_goal_3_10584_L21, denote_pm_goal_3_10582_L21]
    exact nl_sh 2048 1024 64 _ (initPM 5799) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5800).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10589sh
  -- MoE weight shapes
  have hw10597 : (initPM 11285).shape = [32,1024,1024] := h_ss_pm 11285 [32,1024,1024] (by decide)
  have hw10598 : (initPM 11286).shape = [32,1024,1024] := h_ss_pm 11286 [32,1024,1024] (by decide)
  have hw10599 : (initPM 11287).shape = [32,1024,512] := h_ss_pm 11287 [32,1024,512] (by decide)
  have hw10600 : (initPM 11288).shape = [32,1024,512] := h_ss_pm 11288 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10591canon : denoteGraph_ringAttn pm_goal_3 initPM 11279
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11277) 8 64).fst := by
    rw [br_pm_11279,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11277).shape.reverse.head?).getD 1 = 64 from by rw [h10589sh]; rfl]
  have h10592canon : denoteGraph_ringAttn pm_goal_3 initPM 11280
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11278) 8 64).fst := by
    rw [br_pm_11280,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11278).shape.reverse.head?).getD 1 = 64 from by rw [h10590sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10591sh : (denoteGraph_ringAttn pm_goal_3 initPM 11279).shape = [2048, 64] := by
    rw [h10591canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10589sh]; rfl)
  have h10592sh : (denoteGraph_ringAttn pm_goal_3 initPM 11280).shape = [2048, 64] := by
    rw [h10592canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10590sh]; rfl)
  have h10593canon : denoteGraph_ringAttn pm_goal_3 initPM 11281
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11277) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593_L21,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11277).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10589sh]; rfl]
  have h10594canon : denoteGraph_ringAttn pm_goal_3 initPM 11282
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11278) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594_L21,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 11278).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10590sh]; rfl]
  have h10593sh : (denoteGraph_ringAttn pm_goal_3 initPM 11281).shape = [2048, 64] := by
    rw [h10593canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10589sh
  have h10594sh : (denoteGraph_ringAttn pm_goal_3 initPM 11282).shape = [2048, 64] := by
    rw [h10594canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10590sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 11269) (denoteGraph_ringAttn pm_goal_3 initPM 11270)
    (denoteGraph_ringAttn pm_goal_3 initPM 11279) (denoteGraph_ringAttn pm_goal_3 initPM 11280)
    (denoteGraph_ringAttn pm_goal_3 initPM 11281) (denoteGraph_ringAttn pm_goal_3 initPM 11282)
    (initPM 11285) (initPM 11286) (initPM 11287) (initPM 11288)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10581sh h10582sh h10591sh h10592sh h10593sh h10594sh hw10597 hw10598 hw10599 hw10600
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_11289, br_pm_11290, br_pm_16710, br_pm_16733,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5806, br_sm_8513, denote_sm_goal_3_5601_L21, br_sm_5801]
  rw [hrouter, h5608, h5609]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5800).shape.reverse.head?).getD 1 = 64 from by rw [hSM5604sh]; rfl]
  rw [hw5600, hcarry5599, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5796) 2048 1024 (by omega) (by omega) h10577 h10578]
  rw [← denote_pm_goal_3_10581_L21, ← denote_pm_goal_3_10582_L21]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10589sh h10590sh]
  rw [← h10591canon, ← h10592canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L21_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5795 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11265,
         denoteGraph_ringAttn pm_goal_3 initPM 11266])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5825
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11363,
           denoteGraph_ringAttn pm_goal_3 initPM 11364] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5796 = initPM 5796 := hb initGoal_5796 (by decide) rfl
  have hw5612 : initSM 5808 = initPM 5808 := hb initGoal_5808 (by decide) rfl
  have hw5617 : initSM 5813 = initPM 5813 := hb initGoal_5813 (by decide) rfl
  have hw5621 : initSM 5817 = initPM 5817 := hb initGoal_5817 (by decide) rfl
  have hw5626 : initSM 5822 = initPM 5822 := hb initGoal_5822 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5795) (initSM 5796)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11269,
           denoteGraph_ringAttn pm_goal_3 initPM 11270] := by
    rw [hcarry5599, hw5600,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5796) 2048 1024 (by omega) (by omega) h10577 h10578,
        ← denote_pm_goal_3_10581_L21, ← denote_pm_goal_3_10582_L21]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 11269 / 11270
  rw [br_pm_11363, br_pm_11364,
      br_pm_11303, br_pm_11301, br_pm_11295, br_pm_11291, br_pm_16714,
      br_pm_11359, br_pm_11349, br_pm_11343, br_pm_11341,
      br_pm_11319, br_pm_11309, br_pm_11305, br_pm_16718,
      br_pm_11337, br_pm_11327, br_pm_11323, br_pm_16722,
      br_pm_11304, br_pm_11302, br_pm_11296, br_pm_11292, br_pm_16737,
      br_pm_11360, br_pm_11350, br_pm_11344, br_pm_11342,
      br_pm_11320, br_pm_11310, br_pm_11306, br_pm_16741,
      br_pm_11338, br_pm_11328, br_pm_11324, br_pm_16745]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5797
  rw [br_sm_5825, br_sm_5811, br_sm_5810, br_sm_5809,
      br_sm_5807, br_sm_8517,
      br_sm_5824, br_sm_5823, br_sm_5821, br_sm_5820,
      br_sm_5815, br_sm_5814, br_sm_5812, br_sm_8521,
      br_sm_5819, br_sm_5818, br_sm_5816, br_sm_8525,
      denote_sm_goal_3_5601_L21]
  rw [hRMS, hw5612, hw5617, hw5621, hw5626]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 11269 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 11270 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581_L21, rms_sh]; exact h10577
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582_L21, rms_sh]; exact h10578
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5808).shape = [1, 1024] := h_ss_pm 5808 [1, 1024] (by decide)
  have hw29 : (initPM 5813).shape = [512, 1024] := h_ss_pm 5813 [512, 1024] (by decide)
  have hw33 : (initPM 5817).shape = [512, 1024] := h_ss_pm 5817 [512, 1024] (by decide)
  have hw38 : (initPM 5822).shape = [1024, 512] := h_ss_pm 5822 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5808) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5813) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5817) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5808)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5808)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5813)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5813)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5817)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5817)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5808), fw_linear (fw_view [2048, 1024] B) (initPM 5808)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5808)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5808))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5813), fw_linear (fw_view [2048, 1024] B) (initPM 5813)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5817), fw_linear (fw_view [2048, 1024] B) (initPM 5817)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5808)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5808)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5822) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817))))) (initPM 5822)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))))) (initPM 5822)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817))))) (initPM 5822), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))))) (initPM 5822)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817))))) (initPM 5822)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))))) (initPM 5822))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5808))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5808))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5817))))) (initPM 5822)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5813))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5817))))) (initPM 5822)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11377_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11377).shape = [2048, 1024] := by
  have h10517 := hbase345
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 11261).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L21, denote_pm_goal_3_10569_L21]; rfl
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L21]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10517 h10573
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11269).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L21, rms_sh]; exact h10577
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 11289).shape = [2048, 1024] := by
    rw [br_pm_11289, br_pm_16710]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 11303).shape = [2048, 1] := by
    rw [br_pm_11303, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11301]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 11359).shape = [2048, 1024] := by
    rw [br_pm_11359]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 11363).shape = [2048, 1024] := by
    rw [br_pm_11363, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11289) (denoteGraph_ringAttn pm_goal_3 initPM 11363)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have h16379sh : (denoteGraph_ringAttn pm_goal_3 initPM 16691).shape = [2048, 1024] := by
    rw [br_pm_16691]; exact h10577
  have h10685sh : (denoteGraph_ringAttn pm_goal_3 initPM 11373).shape = [2048, 1024] := by
    rw [br_pm_11373, br_pm_11367]; exact hinnerA
  rw [br_pm_11377]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16379sh h10685sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11378_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11378).shape = [2048, 1024] := by
  have h10518 := hbase346
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 11262).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L21, denote_pm_goal_3_10570_L21]; rfl
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L21]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10518 h10574
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11270).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L21, rms_sh]; exact h10578
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 11290).shape = [2048, 1024] := by
    rw [br_pm_11290, br_pm_16733]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 11304).shape = [2048, 1] := by
    rw [br_pm_11304, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11302]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 11360).shape = [2048, 1024] := by
    rw [br_pm_11360]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 11364).shape = [2048, 1024] := by
    rw [br_pm_11364, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11290) (denoteGraph_ringAttn pm_goal_3 initPM 11364)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  have h16387sh : (denoteGraph_ringAttn pm_goal_3 initPM 16699).shape = [2048, 1024] := by
    rw [br_pm_16699]; exact h10578
  have h10686sh : (denoteGraph_ringAttn pm_goal_3 initPM 11374).shape = [2048, 1024] := by
    rw [br_pm_11374, br_pm_11368]; exact hinnerB
  rw [br_pm_11378]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16387sh h10686sh

-- ===== carry_5828 =====
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_carry_5828_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5787)).getD (t + 1) 0 ≤ 4096)
    (hcarry5779 : denoteGraph_ringAttn sm_goal_3 initSM 5779 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11205,
         denoteGraph_ringAttn pm_goal_3 initPM 11206])
    (h11205 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024])
    (h11206 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5828 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11377,
         denoteGraph_ringAttn pm_goal_3 initPM 11378] := by
  have hattn := sm_pm_attention_L21_commute initSM initPM hSM hPM hInit hcarry5779 h11205 h11206 h_bound
  have hw5635 : (initPM 5782).shape = [16, 64, 1024] := hPM 5782 [16, 64, 1024] (by decide)
  have hw5644 : (initPM 5791).shape = [1024, 1024] := hPM 5791 [1024, 1024] (by decide)
  have h10693 : (denoteGraph_ringAttn pm_goal_3 initPM 11209).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L21, rms_sh]; exact h11205
  have h10694 : (denoteGraph_ringAttn pm_goal_3 initPM 11210).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L21, rms_sh]; exact h11206
  have h10695d : (denoteGraph_ringAttn pm_goal_3 initPM 11211).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L21]; exact ph_lin_shape_gen _ _ 2048 16 h10693 hw5635
  have h10696d : (denoteGraph_ringAttn pm_goal_3 initPM 11212).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L21]; exact ph_lin_shape_gen _ _ 2048 16 h10694 hw5635
  -- folded-store bridges at the two attention Q tids
  have b1487_10695 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11211
      = denoteGraph_ringAttn pm_goal_3 initPM 11211 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11211 1697 (by decide) (by decide)).symm
  have b1487_10696 : (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM 11212
      = denoteGraph_ringAttn pm_goal_3 initPM 11212 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11212 1697 (by decide) (by decide)).symm
  have b1488_10695 : (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11211
      = denoteGraph_ringAttn pm_goal_3 initPM 11211 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11211 1698 (by decide) (by decide)).symm
  have b1488_10696 : (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM 11212
      = denoteGraph_ringAttn pm_goal_3 initPM 11212 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11212 1698 (by decide) (by decide)).symm
  have h10719 : (denoteGraph_ringAttn pm_goal_3 initPM 11235).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L21_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_21 nR0_21 nR1_21 0 buddy_r0_21 (by decide)]
    have e0 : nR0_21.ins.getD 0 0 = 11211 := by decide
    have e1 : nR1_21.ins.getD 0 0 = 11212 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
         (pm_goal_3.nodes.take 1697).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1487_10695, b1487_10696]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10695d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10720 : (denoteGraph_ringAttn pm_goal_3 initPM 11236).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L21_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_21 nR0_21 nR1_21 1 buddy_r1_21 (by decide)]
    have e0 : nR0_21.ins.getD 0 0 = 11211 := by decide
    have e1 : nR1_21.ins.getD 0 0 = 11212 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_21.ins.getD 0 0),
         (pm_goal_3.nodes.take 1698).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_21.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1488_10695, b1488_10696]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10695d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl

  have hreshape := sm_pm_reshape_float_L21_commute initSM initPM hInit hattn h10719 h10720 hw5644
  have h10745 : (denoteGraph_ringAttn pm_goal_3 initPM 11261).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L21, denote_pm_goal_3_10569_L21]; rfl
  have h10746 : (denoteGraph_ringAttn pm_goal_3 initPM 11262).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L21, denote_pm_goal_3_10570_L21]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L21 initSM initPM hcarry5779 hreshape h11205 h11206 h10745 h10746
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 11265).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L21]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h11205 h10745
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 11266).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L21]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h11206 h10746
  have hgmm := sm_pm_moe_gmm_L21_commute initSM initPM hInit hPM hcarry5599 h10577 h10578
  have hgate := sm_pm_gate_mul_L21_commute initSM initPM hInit hPM hcarry5599 h10577 h10578
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 11269).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L21, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 11270).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L21, rms_sh]; exact h10578
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 11289).shape = [2048, 1024] := by
    rw [br_pm_11289, br_pm_16710]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 11290).shape = [2048, 1024] := by
    rw [br_pm_11290, br_pm_16733]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 11303).shape = [2048, 1] := by
    rw [br_pm_11303, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11301]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 11359).shape = [2048, 1024] := by
    rw [br_pm_11359]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 11363).shape = [2048, 1024] := by
    rw [br_pm_11363, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 11304).shape = [2048, 1] := by
    rw [br_pm_11304, TrainVerify.Denote.fw_sigmoid_shape, br_pm_11302]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 11360).shape = [2048, 1024] := by
    rw [br_pm_11360]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 11364).shape = [2048, 1024] := by
    rw [br_pm_11364, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11289) (denoteGraph_ringAttn pm_goal_3 initPM 11363)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11290) (denoteGraph_ringAttn pm_goal_3 initPM 11364)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  -- === assemble ===
  rw [br_pm_11377, br_pm_16691, br_pm_11373, br_pm_11367,
      br_pm_11378, br_pm_16699, br_pm_11374, br_pm_11368]
  rw [br_sm_5828, br_sm_8502, br_sm_5827, br_sm_5826]
  rw [hcarry5599, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 11289) (denoteGraph_ringAttn pm_goal_3 initPM 11290)
        (denoteGraph_ringAttn pm_goal_3 initPM 11363) (denoteGraph_ringAttn pm_goal_3 initPM 11364)
        h10601sh h10602sh h10675sh h10676sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 11265) (denoteGraph_ringAttn pm_goal_3 initPM 11266)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11289) (denoteGraph_ringAttn pm_goal_3 initPM 11363))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11290) (denoteGraph_ringAttn pm_goal_3 initPM 11364))
        h10577 h10578 hinnerA hinnerB]


end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L21
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L21
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L21_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L21_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L21_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11377_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11378_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5828_commute
