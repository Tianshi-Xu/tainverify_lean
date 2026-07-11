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

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L21
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L21_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L21
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L21_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L21_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L21_hbound_witness
