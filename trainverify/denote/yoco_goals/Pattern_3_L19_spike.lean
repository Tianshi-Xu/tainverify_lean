/-
  Pattern_3_L19_spike.lean — L19 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L19-specific TIDs.  The L19 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L19's Q path
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

/-! ## L19 attention node declarations + buddy proofs.
SM attn node index 749; PM r0 = 1557; PM r1 = 1558. -/

def nSM_19 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5685, 5686, 5687, 5688, 5689], outs := [5690],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_19 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10867, 5686, 5687, 5688, 5689], outs := [10891],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_19 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10868, 5686, 5687, 5688, 5689], outs := [10892],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_19 : ringAttnBuddies sm_goal_3 nSM_19 = [nSM_19] := by
  show (List.filter (fun m => decide (m.op = nSM_19.op) && decide (m.params = nSM_19.params) &&
      decide (m.ins.getD 3 0 = nSM_19.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_19.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_19]
  rw [show (List.filter (fun m => decide (m.op = nSM_19.op) && decide (m.params = nSM_19.params) &&
      decide (m.ins.getD 3 0 = nSM_19.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_19.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_19] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_19 : ringAttnBuddies pm_goal_3 nR0_19 = [nR0_19, nR1_19] := by
  show (List.filter (fun m => decide (m.op = nR0_19.op) && decide (m.params = nR0_19.params) &&
      decide (m.ins.getD 3 0 = nR0_19.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_19.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_19, nR1_19]
  rw [show (List.filter (fun m => decide (m.op = nR0_19.op) && decide (m.params = nR0_19.params) &&
      decide (m.ins.getD 3 0 = nR0_19.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_19.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_19, nR1_19] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_19 : ringAttnBuddies pm_goal_3 nR1_19 = [nR0_19, nR1_19] := by
  show (List.filter (fun m => decide (m.op = nR1_19.op) && decide (m.params = nR1_19.params) &&
      decide (m.ins.getD 3 0 = nR1_19.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_19.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_19, nR1_19]
  rw [show (List.filter (fun m => decide (m.op = nR1_19.op) && decide (m.params = nR1_19.params) &&
      decide (m.ins.getD 3 0 = nR1_19.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_19.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_19, nR1_19] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L19 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L19_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5690
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_19 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5690
      = (sm_goal_3.nodes.take 750).foldl (applyNodeRingAttn sm_goal_3) initSM 5690 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5690 750 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 750 = sm_goal_3.nodes.take 749 ++ [nSM_19] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5685 5686 5687 5688 5689 5690 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L19_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10891
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_19 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10891
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10891 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10891 1558 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1558 = pm_goal_3.nodes.take 1557 ++ [nR0_19] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10867 5686 5687 5688 5689 10891 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L19_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10892
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_19 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10892
      = (pm_goal_3.nodes.take 1559).foldl (applyNodeRingAttn pm_goal_3) initPM 10892 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10892 1559 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1559 = pm_goal_3.nodes.take 1558 ++ [nR1_19] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10868 5686 5687 5688 5689 10892 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L19) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5683 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5681) (initSM 5682) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5683 8412 5682 747
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8412, 5682], outs := [5683] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8412 5682 5683)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8412 5681 746
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5681], outs := [8412, 8416], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5681 8412 [8412, 8416] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5682 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5685 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5683) (initSM 5684) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5685 5683 5684 748
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5683, 5684], outs := [5685] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5683 5684 5685 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5684 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5691 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5690) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5691 5690 750
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5690], outs := [5691], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5690 5691 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5692 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5691) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5692 5691 751
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5691], outs := [5692], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5691 5692 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5694 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5692) (initSM 5693) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5694 5692 5693 752
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5692, 5693], outs := [5694] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5692 5693 5694)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5693 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5695 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5694) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5695 5694 753
    ({ rank := 0, op := "OpName.FW_view", ins := [5694], outs := [5695], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5694 5695)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5696 =
      denoteGraph_ringAttn sm_goal_3 initSM 5695 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5696 5695 754
    ({ rank := 0, op := "OpName.FW_float", ins := [5695], outs := [5696] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5695 5696 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5697 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5681)
        (denoteGraph_ringAttn sm_goal_3 initSM 5696) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8416 = denoteGraph_ringAttn sm_goal_3 initSM 5681 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8416 5681 746
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5681], outs := [8412, 8416], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5681 8416 [8412, 8416] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5697 8416 5696 755
    ({ rank := 0, op := "OpName.FW_add", ins := [8416, 5696], outs := [5697] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8416 5696 5697)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5699 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5697) (initSM 5698) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5699 8420 5698 757
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8420, 5698], outs := [5699] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8420 5698 5699)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8420 5697 756
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5697], outs := [8420, 8424], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5697 8420 [8420, 8424] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5698 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5700 =
      denoteGraph_ringAttn sm_goal_3 initSM 5699 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5700 8431 759
    ({ rank := 0, op := "OpName.FW_float", ins := [8431], outs := [5700] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8431 5700 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8431 5699 758
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5699 8431 [8431, 8435, 8439, 8443, 8447] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5702 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5700) (initSM 5701) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5702 5700 5701 763
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5700, 5701], outs := [5702] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5700 5701 5702 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5701 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5704 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5702) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5702).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5704 5702 767
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5702], outs := [5703, 5704, 5705], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5702 5703 5704 5705 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5686 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5686 8061 487
    ({ rank := 0, op := "OpName.FW_to", ins := [8061], outs := [5686] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8061 5686 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8061 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8061 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589_L19 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5687 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5687 8119 499
    ({ rank := 0, op := "OpName.FW_to", ins := [8119], outs := [5687] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8119 5687 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8119 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8119 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L19) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10865 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10861) (initPM 5682) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10865 16515 5682 1553
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16515, 5682], outs := [10865] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16515 5682 10865)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16515 10861 1551
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515, 16519], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10861 16515 [16515, 16519] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5682 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10867 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10865) (initPM 5684) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10867 10865 5684 1555
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10865, 5684], outs := [10867] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 10865 5684 10867 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5684 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10893 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10891) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10893 10891 1559
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10891], outs := [10893], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10891 10893 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10899 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10893) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10899 10893 1561
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10893], outs := [10899], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10893 10899 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10903 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10899) (initPM 5693) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10903 10899 5693 1563
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10899, 5693], outs := [10903] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10899 5693 10903)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5693 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10913 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10903) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10913 10903 1565
    ({ rank := 0, op := "OpName.FW_view", ins := [10903], outs := [10913], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10903 10913)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10917 =
      denoteGraph_ringAttn pm_goal_3 initPM 10913 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10917 10913 1567
    ({ rank := 0, op := "OpName.FW_float", ins := [10913], outs := [10917] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10913 10917 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10921 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10861)
        (denoteGraph_ringAttn pm_goal_3 initPM 10917) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16519 = denoteGraph_ringAttn pm_goal_3 initPM 10861 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16519 10861 1551
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515, 16519], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10861 16519 [16515, 16519] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10921 16519 10917 1569
    ({ rank := 0, op := "OpName.FW_add", ins := [16519, 10917], outs := [10921] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16519 10917 10921)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10925 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10921) (initPM 5698) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10925 16531 5698 1573
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16531, 5698], outs := [10925] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16531 5698 10925)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16531 10921 1571
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10921], outs := [16531, 16535], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10921 16531 [16531, 16535] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5698 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10927 =
      denoteGraph_ringAttn pm_goal_3 initPM 10925 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10927 16550 1577
    ({ rank := 0, op := "OpName.FW_float", ins := [16550], outs := [10927] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16550 10927 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16550 10925 1575
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10925 16550 [16550, 16554, 16558, 16562, 16566] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10933 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10927) (initPM 5701) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10933 10927 5701 1585
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [10927, 5701], outs := [10933] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 10927 5701 10933 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5701 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10937 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10933) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10933).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10937 10933 1593
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10933], outs := [10935, 10937, 10939], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 10933 10935 10937 10939 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10866 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10862) (initPM 5682) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10866 16523 5682 1554
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16523, 5682], outs := [10866] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16523 5682 10866)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16523 10862 1552
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523, 16527], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10862 16523 [16523, 16527] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5682 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10868 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10866) (initPM 5684) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10868 10866 5684 1556
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10866, 5684], outs := [10868] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 10866 5684 10868 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5684 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10894 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10892) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10894 10892 1560
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10892], outs := [10894], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10892 10894 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10900 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10894) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10900 10894 1562
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10894], outs := [10900], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10894 10900 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10904 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10900) (initPM 5693) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10904 10900 5693 1564
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10900, 5693], outs := [10904] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10900 5693 10904)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5693 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10914 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10904) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10914 10904 1566
    ({ rank := 1, op := "OpName.FW_view", ins := [10904], outs := [10914], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10904 10914)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10918 =
      denoteGraph_ringAttn pm_goal_3 initPM 10914 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10918 10914 1568
    ({ rank := 1, op := "OpName.FW_float", ins := [10914], outs := [10918] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10914 10918 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10922 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10862)
        (denoteGraph_ringAttn pm_goal_3 initPM 10918) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16527 = denoteGraph_ringAttn pm_goal_3 initPM 10862 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16527 10862 1552
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523, 16527], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10862 16527 [16523, 16527] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10922 16527 10918 1570
    ({ rank := 1, op := "OpName.FW_add", ins := [16527, 10918], outs := [10922] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16527 10918 10922)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10926 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10922) (initPM 5698) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10926 16539 5698 1574
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16539, 5698], outs := [10926] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16539 5698 10926)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16539 10922 1572
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10922], outs := [16539, 16543], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10922 16539 [16539, 16543] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5698 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10928 =
      denoteGraph_ringAttn pm_goal_3 initPM 10926 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10928 16573 1581
    ({ rank := 1, op := "OpName.FW_float", ins := [16573], outs := [10928] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16573 10928 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16573 10926 1576
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10926 16573 [16573, 16577, 16581, 16585, 16589] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10934 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10928) (initPM 5701) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10934 10928 5701 1589
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [10928, 5701], outs := [10934] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 10928 5701 10934 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5701 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10938 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10934) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10934).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10938 10934 1597
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10934], outs := [10936, 10938, 10940], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 10934 10936 10938 10940 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5686 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5686 15843 1038
    ({ rank := 1, op := "OpName.FW_to", ins := [15843], outs := [5686] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15843 5686 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15843 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15843 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589_L19 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5687 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5687 15949 1062
    ({ rank := 1, op := "OpName.FW_to", ins := [15949], outs := [5687] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15949 5687 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15949 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15949 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L19 commute theorems -/

-- Q sharding commute: SM 5685 = allGather0[PM 10867, PM 10868].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10861,
         denoteGraph_ringAttn pm_goal_3 initPM 10862])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024])
    (hw5586 : (initPM 5684).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5685 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10867,
         denoteGraph_ringAttn pm_goal_3 initPM 10868] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5682 = initPM 5682 := hb initGoal_5682 (by decide) rfl
  have hw5586e : initSM 5684 = initPM 5684 := hb initGoal_5684 (by decide) rfl
  rw [denote_sm_goal_3_5587_L19, denote_sm_goal_3_5585_L19,
      denote_pm_goal_3_10523_L19, denote_pm_goal_3_10521_L19,
      denote_pm_goal_3_10524_L19, denote_pm_goal_3_10522_L19]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10861) (initPM 5682)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10862) (initPM 5682)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5682) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5684) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape_L19 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5686).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588_L19, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape_L19 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5687).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589_L19, denote_pm_goal_3_5336]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))

-- K/V replication (cross-graph, full tensor): SM 5686 = PM 5686, SM 5687 = PM 5687.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5686 =
      denoteGraph_ringAttn pm_goal_3 initPM 5686 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588_L19, denote_pm_goal_3_5588_L19, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5687 =
      denoteGraph_ringAttn pm_goal_3 initPM 5687 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589_L19, denote_pm_goal_3_5589_L19, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L19 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L19_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10861,
         denoteGraph_ringAttn pm_goal_3 initPM 10862])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5690 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10891,
         denoteGraph_ringAttn pm_goal_3 initPM 10892] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5684).shape = [16, 64, 1024] := hPM 5684 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L19_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L19_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L19_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape_L19 initPM hPM
  have hVsh := pm_5589_shape_L19 initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10865).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L19, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10866).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L19, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 10867).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L19]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 10868).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L19]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5685).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5685).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5686).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5687).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 749)
  have bSM5587 : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5685 = denoteGraph_ringAttn sm_goal_3 initSM 5685 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5685 749 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5686 = denoteGraph_ringAttn sm_goal_3 initSM 5686 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5686 749 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5687 = denoteGraph_ringAttn sm_goal_3 initSM 5687 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5687 749 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1557)
  have bPM10523 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10867 = denoteGraph_ringAttn pm_goal_3 initPM 10867 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10867 1557 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10868 = denoteGraph_ringAttn pm_goal_3 initPM 10868 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10868 1557 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5686 = denoteGraph_ringAttn pm_goal_3 initPM 5686 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5686 1557 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5687 = denoteGraph_ringAttn pm_goal_3 initPM 5687 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5687 1557 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5688 = initSM 5688 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 749) initSM 5688 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5689 = initSM 5689 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 749) initSM 5689 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5688 = initPM 5688 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1557) initPM 5688 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5689 = initPM 5689 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1557) initPM 5689 (by decide) (by decide)
  have hw5590 : initSM 5688 = initPM 5688 := hb initGoal_5688 (by decide) rfl
  have hw5591 : initSM 5689 = initPM 5689 := hb initGoal_5689 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5685).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5686).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5687).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
        (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5685 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10867,
        (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10868]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5686 =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5686
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5687 =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5687
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5686).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5687).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5689)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5688 =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5688
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_19.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM 5689 =
      (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5689
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
       (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10867,
       (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10868]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
          (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 1 0),
          (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 2 0),
          (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 4 0))
        (nR0_19.params.getD 0 1) (nR0_19.params.getD 1 1) (nR0_19.params.getD 2 1) (nR0_19.params.getD 3 1)
        (decide (nR0_19.params.getD 4 0 ≠ 0)) (nR0_19.params.getD 5 0)).shape
        = [2 * 2048, nR0_19.params.getD 0 1, nR0_19.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1557 -> take 1558)
  have e10523 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10867
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10867 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10867 1557 1558 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10868
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10868 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10868 1557 1558 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5686
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 5686 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5686 1557 1558 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5687
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 5687 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5687 1557 1558 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5688
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 5688 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5688 1557 1558 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 5689
      = (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 5689 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5689 1557 1558 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_19
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_19 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_19]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_19]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_19]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 749).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_19 nR0_19 nR1_19 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_19 buddy_r0_19 buddy_r1_19 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L19_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L19_r0_bridge, ← denote_pm_attn_L19_r1_bridge]


/-! ## L19 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5690 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10891,
         denoteGraph_ringAttn pm_goal_3 initPM 10892])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10891).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10892).shape = [2048, 16, 64])
    (hw5595 : (initPM 5693).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5696 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10917,
         denoteGraph_ringAttn pm_goal_3 initPM 10918] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5693 = initPM 5693 := hb initGoal_5693 (by decide) rfl
  rw [denote_sm_goal_3_5598_L19, denote_sm_goal_3_5597_L19, denote_sm_goal_3_5596_L19,
      denote_sm_goal_3_5594_L19, denote_sm_goal_3_5593_L19,
      denote_pm_goal_3_10573_L19, denote_pm_goal_3_10569_L19, denote_pm_goal_3_10559_L19,
      denote_pm_goal_3_10555_L19, denote_pm_goal_3_10549_L19,
      denote_pm_goal_3_10574_L19, denote_pm_goal_3_10570_L19, denote_pm_goal_3_10560_L19,
      denote_pm_goal_3_10556_L19, denote_pm_goal_3_10550_L19]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10891))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10892))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5693) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10891))) (initPM 5693)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10892))) (initPM 5693)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10891))) (initPM 5693),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10892))) (initPM 5693)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute_L19 (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10861,
         denoteGraph_ringAttn pm_goal_3 initPM 10862])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5696 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10917,
         denoteGraph_ringAttn pm_goal_3 initPM 10918])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10917).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10918).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5697 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10921,
         denoteGraph_ringAttn pm_goal_3 initPM 10922] := by
  rw [denote_sm_goal_3_5599_L19, denote_pm_goal_3_10577_L19, denote_pm_goal_3_10578_L19]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5697 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10921,
         denoteGraph_ringAttn pm_goal_3 initPM 10922])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5702 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10933,
         denoteGraph_ringAttn pm_goal_3 initPM 10934] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5698 = initPM 5698 := hb initGoal_5698 (by decide) rfl
  have hw5603 : initSM 5701 = initPM 5701 := hb initGoal_5701 (by decide) rfl
  have hw5603sh : (initPM 5701).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5701 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5701] using hsh
  rw [denote_sm_goal_3_5604_L19, denote_sm_goal_3_5602_L19, denote_sm_goal_3_5601_L19,
      denote_pm_goal_3_10589_L19, denote_pm_goal_3_10583_L19, denote_pm_goal_3_10581_L19,
      denote_pm_goal_3_10590_L19, denote_pm_goal_3_10584_L19, denote_pm_goal_3_10582_L19]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5698) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10921) (initPM 5698)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10922) (initPM 5698)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5701) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L19 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5697 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10921,
         denoteGraph_ringAttn pm_goal_3 initPM 10922])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5704 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10937,
         denoteGraph_ringAttn pm_goal_3 initPM 10938] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5701).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5701 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5701] using hsh
  have hnl := sm_pm_nl_L19_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 10933).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L19, denote_pm_goal_3_10583_L19, denote_pm_goal_3_10581_L19]
    exact nl_sh 2048 1024 64 _ (initPM 5701) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 10934).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L19, denote_pm_goal_3_10584_L19, denote_pm_goal_3_10582_L19]
    exact nl_sh 2048 1024 64 _ (initPM 5701) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5702).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606_L19, denote_pm_goal_3_10593_L19, denote_pm_goal_3_10594_L19]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5702).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10933).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10934).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L19 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L19_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10861,
         denoteGraph_ringAttn pm_goal_3 initPM 10862])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5690 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10891,
         denoteGraph_ringAttn pm_goal_3 initPM 10892])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10891).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10892).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024])
    (hw5595 : (initPM 5693).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5704 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10937,
         denoteGraph_ringAttn pm_goal_3 initPM 10938] := by
  have hreshape := sm_pm_reshape_float_L19_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10917).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L19, denote_pm_goal_3_10569_L19]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10918).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L19, denote_pm_goal_3_10570_L19]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L19 initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L19]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L19]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L19 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L19 router — fully assembled

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
theorem sm_pm_router_commute_L19_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10861,
         denoteGraph_ringAttn pm_goal_3 initPM 10862])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5704 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10937,
         denoteGraph_ringAttn pm_goal_3 initPM 10938] := by
  have hattn := sm_pm_attention_L19_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5684).shape = [16, 64, 1024] := hPM 5684 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5693).shape = [1024, 1024] := hPM 5693 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10865).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L19, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10866).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L19, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10867).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L19]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10868).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L19]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10867
      = denoteGraph_ringAttn pm_goal_3 initPM 10867 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10867 1557 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10868
      = denoteGraph_ringAttn pm_goal_3 initPM 10868 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10868 1557 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10867
      = denoteGraph_ringAttn pm_goal_3 initPM 10867 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10867 1558 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10868
      = denoteGraph_ringAttn pm_goal_3 initPM 10868 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10868 1558 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10891).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L19_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_19 nR0_19 nR1_19 0 buddy_r0_19 (by decide)]
    have e0 : nR0_19.ins.getD 0 0 = 10867 := by decide
    have e1 : nR1_19.ins.getD 0 0 = 10868 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
         (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10892).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L19_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_19 nR0_19 nR1_19 1 buddy_r1_19 (by decide)]
    have e0 : nR0_19.ins.getD 0 0 = 10867 := by decide
    have e1 : nR1_19.ins.getD 0 0 = 10868 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
         (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L19_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L19_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _


-- ================= L19 MoE carry (sm_pm_carry_5730_commute) =================
theorem br_pm_16519 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16519 = denoteGraph_ringAttn pm_goal_3 initPM 10861 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16519 10861 1551
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515, 16519], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10861 16519 [16515, 16519] 2 (by decide) (by decide))
    rfl

theorem br_pm_16527 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16527 = denoteGraph_ringAttn pm_goal_3 initPM 10862 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16527 10862 1552
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523, 16527], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10862 16527 [16523, 16527] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10935 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10935 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10933) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10933).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10935 10933 1593
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10933], outs := [10935, 10937, 10939], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 10933 10935 10937 10939 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10936 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10936 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10934) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10934).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10936 10934 1597
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10934], outs := [10936, 10938, 10940], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 10934 10936 10938 10940 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10945 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10945 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16554)
        (denoteGraph_ringAttn pm_goal_3 initPM 10935)
        (denoteGraph_ringAttn pm_goal_3 initPM 10937)
        [initPM 10941, initPM 10942] [initPM 10943, initPM 10944]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10945 16554 10935 10937 10941 10942 10943 10944 1601
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16554, 10935, 10937, 10941, 10942, 10943, 10944], outs := [10945], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16554 10935 10937 10941 10942 10943 10944 10945 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10941 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10942 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10943 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10944 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10946 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10946 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16577)
        (denoteGraph_ringAttn pm_goal_3 initPM 10936)
        (denoteGraph_ringAttn pm_goal_3 initPM 10938)
        [initPM 10941, initPM 10942] [initPM 10943, initPM 10944]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10946 16577 10936 10938 10941 10942 10943 10944 1604
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16577, 10936, 10938, 10941, 10942, 10943, 10944], outs := [10946], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16577 10936 10938 10941 10942 10943 10944 10946 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10941 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10942 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10943 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10944 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10947 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10947 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16558) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10947 16558 1578
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16558], outs := [10947], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16558 10947 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10948 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10948 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16581) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10948 16581 1582
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16581], outs := [10948], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16581 10948 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10951 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10951 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10947) (initPM 5710) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10951 10947 5710 1586
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10947, 5710], outs := [10951] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10947 5710 10951)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5710 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10952 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10952 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10948) (initPM 5710) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10952 10948 5710 1590
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10948, 5710], outs := [10952] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10948 5710 10952)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5710 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10957 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10957 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10951) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10957 10951 1594
    ({ rank := 0, op := "OpName.FW_view", ins := [10951], outs := [10957], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 10951 10957)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10958 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10958 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10952) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10958 10952 1598
    ({ rank := 1, op := "OpName.FW_view", ins := [10952], outs := [10958], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 10952 10958)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10959 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10959 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10957) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10959 10957 1602
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [10957], outs := [10959] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 10957 10959])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10960 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10960 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10958) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10960 10958 1605
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [10958], outs := [10960] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 10958 10960])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10961 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10961 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16562) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10961 16562 1579
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16562], outs := [10961], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16562 10961 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10962 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10962 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16585) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10962 16585 1583
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16585], outs := [10962], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16585 10962 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10965 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10965 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10961) (initPM 5715) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10965 10961 5715 1587
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10961, 5715], outs := [10965] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10961 5715 10965)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5715 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10966 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10966 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10962) (initPM 5715) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10966 10962 5715 1591
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10962, 5715], outs := [10966] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10962 5715 10966)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5715 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10975 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10975 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10965) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10975 10965 1595
    ({ rank := 0, op := "OpName.FW_view", ins := [10965], outs := [10975], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10965 10975)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10976 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10976 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10966) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10976 10966 1599
    ({ rank := 1, op := "OpName.FW_view", ins := [10966], outs := [10976], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10966 10976)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10979 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10979 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16566) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10979 16566 1580
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16566], outs := [10979], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16566 10979 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10980 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10980 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16589) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10980 16589 1584
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16589], outs := [10980], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16589 10980 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10983 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10983 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10979) (initPM 5719) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10983 10979 5719 1588
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10979, 5719], outs := [10983] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10979 5719 10983)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5719 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10984 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10984 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10980) (initPM 5719) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10984 10980 5719 1592
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10980, 5719], outs := [10984] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10980 5719 10984)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5719 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10993 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10993 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10983) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10993 10983 1596
    ({ rank := 0, op := "OpName.FW_view", ins := [10983], outs := [10993], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10983 10993)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10994 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10994 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10984) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10994 10984 1600
    ({ rank := 1, op := "OpName.FW_view", ins := [10984], outs := [10994], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10984 10994)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10997 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10997 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10975) (denoteGraph_ringAttn pm_goal_3 initPM 10993) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10997 10975 10993 1603
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [10975, 10993], outs := [10997] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 10975 10993 10997])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10998 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10998 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10976) (denoteGraph_ringAttn pm_goal_3 initPM 10994) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10998 10976 10994 1606
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [10976, 10994], outs := [10998] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 10976 10994 10998])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10999 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10999 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10997) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10999 10997 1607
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10997], outs := [10999], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10997 10999 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11000 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11000 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10998) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11000 10998 1608
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10998], outs := [11000], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10998 11000 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11005 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11005 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10999) (initPM 5724) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11005 10999 5724 1609
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10999, 5724], outs := [11005] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10999 5724 11005)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5724 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11006 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11006 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11000) (initPM 5724) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11006 11000 5724 1610
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11000, 5724], outs := [11006] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11000 5724 11006)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5724 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11015 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11015 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11005) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11015 11005 1611
    ({ rank := 0, op := "OpName.FW_view", ins := [11005], outs := [11015], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11005 11015)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11016 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11016 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11006) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11016 11006 1612
    ({ rank := 1, op := "OpName.FW_view", ins := [11006], outs := [11016], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11006 11016)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11019 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11019 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10959) (denoteGraph_ringAttn pm_goal_3 initPM 11015) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11019 10959 11015 1613
    ({ rank := 0, op := "OpName.FW_mul", ins := [10959, 11015], outs := [11019] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 10959 11015 11019])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11020 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11020 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10960) (denoteGraph_ringAttn pm_goal_3 initPM 11016) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11020 10960 11016 1614
    ({ rank := 1, op := "OpName.FW_mul", ins := [10960, 11016], outs := [11020] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 10960 11016 11020])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11023 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11023 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10945) (denoteGraph_ringAttn pm_goal_3 initPM 11019) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11023 10945 11019 1615
    ({ rank := 0, op := "OpName.FW_add", ins := [10945, 11019], outs := [11023] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 10945 11019 11023)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11024 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11024 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10946) (denoteGraph_ringAttn pm_goal_3 initPM 11020) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11024 10946 11020 1616
    ({ rank := 1, op := "OpName.FW_add", ins := [10946, 11020], outs := [11024] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 10946 11020 11024)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11029 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11029 =
      denoteGraph_ringAttn pm_goal_3 initPM 11023 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11029 11023 1617
    ({ rank := 0, op := "OpName.FW_float", ins := [11023], outs := [11029] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11023 11029 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11030 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11030 =
      denoteGraph_ringAttn pm_goal_3 initPM 11024 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11030 11024 1618
    ({ rank := 1, op := "OpName.FW_float", ins := [11024], outs := [11030] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11024 11030 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11033 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11033 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16535) (denoteGraph_ringAttn pm_goal_3 initPM 11029) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11033 16535 11029 1619
    ({ rank := 0, op := "OpName.FW_add", ins := [16535, 11029], outs := [11033] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16535 11029 11033)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_11034 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11034 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16543) (denoteGraph_ringAttn pm_goal_3 initPM 11030) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11034 16543 11030 1620
    ({ rank := 1, op := "OpName.FW_add", ins := [16543, 11030], outs := [11034] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16543 11030 11034)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16535 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16535 =
      denoteGraph_ringAttn pm_goal_3 initPM 10921 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16535 10921 1571
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10921], outs := [16531, 16535], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 10921 16531 16535 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16543 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16543 =
      denoteGraph_ringAttn pm_goal_3 initPM 10922 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16543 10922 1572
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10922], outs := [16539, 16543], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 10922 16539 16543 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16554 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16554 =
      denoteGraph_ringAttn pm_goal_3 initPM 10925 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16554 10925 1575
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 10925 16550 16554 16558 16562 16566 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16558 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16558 =
      denoteGraph_ringAttn pm_goal_3 initPM 10925 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16558 10925 1575
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 10925 16550 16554 16558 16562 16566 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16562 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16562 =
      denoteGraph_ringAttn pm_goal_3 initPM 10925 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16562 10925 1575
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 10925 16550 16554 16558 16562 16566 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16566 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16566 =
      denoteGraph_ringAttn pm_goal_3 initPM 10925 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16566 10925 1575
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 10925 16550 16554 16558 16562 16566 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16577 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16577 =
      denoteGraph_ringAttn pm_goal_3 initPM 10926 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16577 10926 1576
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 10926 16573 16577 16581 16585 16589 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16581 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16581 =
      denoteGraph_ringAttn pm_goal_3 initPM 10926 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16581 10926 1576
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 10926 16573 16577 16581 16585 16589 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16585 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16585 =
      denoteGraph_ringAttn pm_goal_3 initPM 10926 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16585 10926 1576
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 10926 16573 16577 16581 16585 16589 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16589 =
      denoteGraph_ringAttn pm_goal_3 initPM 10926 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16589 10926 1576
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 10926 16573 16577 16581 16585 16589 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5703 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5703 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5702) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5702).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5703 5702 767
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5702], outs := [5703, 5704, 5705], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5702 5703 5704 5705 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5708 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5708 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8435)
        (denoteGraph_ringAttn sm_goal_3 initSM 5703)
        (denoteGraph_ringAttn sm_goal_3 initSM 5704)
        (initSM 5706) (initSM 5707) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5708 8435 5703 5704 5706 5707 771
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8435, 5703, 5704, 5706, 5707], outs := [5708], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8435 5703 5704 5706 5707 5708 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5706 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5707 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5709 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5709 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8439) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5709 8439 760
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8439], outs := [5709], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8439 5709 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5711 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5711 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5709) (initSM 5710) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5711 5709 5710 764
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5709, 5710], outs := [5711] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5709 5710 5711)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5710 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5712 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5712 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5711) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5712 5711 768
    ({ rank := 0, op := "OpName.FW_view", ins := [5711], outs := [5712], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5711 5712)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5713 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5713 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5712) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5713 5712 772
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5712], outs := [5713] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5712 5713])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5714 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5714 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8443) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5714 8443 761
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8443], outs := [5714], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8443 5714 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5716 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5716 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5714) (initSM 5715) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5716 5714 5715 765
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5714, 5715], outs := [5716] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5714 5715 5716)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5715 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5717 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5717 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5716) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5717 5716 769
    ({ rank := 0, op := "OpName.FW_view", ins := [5716], outs := [5717], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5716 5717)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5718 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5718 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8447) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5718 8447 762
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8447], outs := [5718], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8447 5718 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5720 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5720 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5718) (initSM 5719) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5720 5718 5719 766
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5718, 5719], outs := [5720] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5718 5719 5720)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5719 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5721 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5721 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5720) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5721 5720 770
    ({ rank := 0, op := "OpName.FW_view", ins := [5720], outs := [5721], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5720 5721)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5722 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5722 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5717) (denoteGraph_ringAttn sm_goal_3 initSM 5721) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5722 5717 5721 773
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5717, 5721], outs := [5722] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5717 5721 5722])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5723 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5723 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5722) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5723 5722 774
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5722], outs := [5723], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5722 5723 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5725 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5725 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5723) (initSM 5724) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5725 5723 5724 775
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5723, 5724], outs := [5725] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5723 5724 5725)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5724 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5726 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5726 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5725) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5726 5725 776
    ({ rank := 0, op := "OpName.FW_view", ins := [5725], outs := [5726], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5725 5726)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5727 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5727 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5713) (denoteGraph_ringAttn sm_goal_3 initSM 5726) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5727 5713 5726 777
    ({ rank := 0, op := "OpName.FW_mul", ins := [5713, 5726], outs := [5727] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5713 5726 5727])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5728 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5728 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5708) (denoteGraph_ringAttn sm_goal_3 initSM 5727) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5728 5708 5727 778
    ({ rank := 0, op := "OpName.FW_add", ins := [5708, 5727], outs := [5728] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5708 5727 5728)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5729 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5729 =
      denoteGraph_ringAttn sm_goal_3 initSM 5728 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5729 5728 779
    ({ rank := 0, op := "OpName.FW_float", ins := [5728], outs := [5729] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5728 5729 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5730 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8424) (denoteGraph_ringAttn sm_goal_3 initSM 5729) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5730 8424 5729 780
    ({ rank := 0, op := "OpName.FW_add", ins := [8424, 5729], outs := [5730] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8424 5729 5730)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8424 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8424 =
      denoteGraph_ringAttn sm_goal_3 initSM 5697 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8424 5697 756
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5697], outs := [8420, 8424], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5697 8420 8424 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8435 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8435 =
      denoteGraph_ringAttn sm_goal_3 initSM 5699 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8435 5699 758
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5699 8431 8435 8439 8443 8447 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8439 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8439 =
      denoteGraph_ringAttn sm_goal_3 initSM 5699 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8439 5699 758
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5699 8431 8435 8439 8443 8447 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8443 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8443 =
      denoteGraph_ringAttn sm_goal_3 initSM 5699 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8443 5699 758
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5699 8431 8435 8439 8443 8447 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8447 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8447 =
      denoteGraph_ringAttn sm_goal_3 initSM 5699 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8447 5699 758
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5699 8431 8435 8439 8443 8447 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5697 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10921,
         denoteGraph_ringAttn pm_goal_3 initPM 10922])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5708 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10945,
         denoteGraph_ringAttn pm_goal_3 initPM 10946] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5698 = initPM 5698 := hb initGoal_5698 (by decide) rfl
  have hw5603sh : (initPM 5701).shape = [64, 1024] := by
    have hgh := hII initGoal_5701 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5701] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5608 : initSM 5706 = allGatherPrimDimN 0 2 0 [initPM 10941, initPM 10942] := by
    have hg := hII initGoal_5706 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5706, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10941) (initPM 10942) []
        (by rw [h_ss_pm 10941 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5609 : initSM 5707 = allGatherPrimDimN 0 2 0 [initPM 10943, initPM 10944] := by
    have hg := hII initGoal_5707 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5707, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10943) (initPM 10944) []
        (by rw [h_ss_pm 10943 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L19_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hrouter := sm_pm_router_commute_L19 initSM initPM hInit hcarry5599 h10577 h10578
  -- PM rms output shapes [2048, 1024]
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10925).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L19, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10926).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L19, rms_sh]; exact h10578
  -- PM nl output shapes [2048, 64]
  have h10589sh : (denoteGraph_ringAttn pm_goal_3 initPM 10933).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L19, denote_pm_goal_3_10583_L19, denote_pm_goal_3_10581_L19]
    exact nl_sh 2048 1024 64 _ (initPM 5701) (by rw [rms_sh]; exact h10577) hw5603sh
  have h10590sh : (denoteGraph_ringAttn pm_goal_3 initPM 10934).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L19, denote_pm_goal_3_10584_L19, denote_pm_goal_3_10582_L19]
    exact nl_sh 2048 1024 64 _ (initPM 5701) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5702).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10589sh
  -- MoE weight shapes
  have hw10597 : (initPM 10941).shape = [32,1024,1024] := h_ss_pm 10941 [32,1024,1024] (by decide)
  have hw10598 : (initPM 10942).shape = [32,1024,1024] := h_ss_pm 10942 [32,1024,1024] (by decide)
  have hw10599 : (initPM 10943).shape = [32,1024,512] := h_ss_pm 10943 [32,1024,512] (by decide)
  have hw10600 : (initPM 10944).shape = [32,1024,512] := h_ss_pm 10944 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10591canon : denoteGraph_ringAttn pm_goal_3 initPM 10935
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10933) 8 64).fst := by
    rw [br_pm_10935,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10933).shape.reverse.head?).getD 1 = 64 from by rw [h10589sh]; rfl]
  have h10592canon : denoteGraph_ringAttn pm_goal_3 initPM 10936
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10934) 8 64).fst := by
    rw [br_pm_10936,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10934).shape.reverse.head?).getD 1 = 64 from by rw [h10590sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10591sh : (denoteGraph_ringAttn pm_goal_3 initPM 10935).shape = [2048, 64] := by
    rw [h10591canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10589sh]; rfl)
  have h10592sh : (denoteGraph_ringAttn pm_goal_3 initPM 10936).shape = [2048, 64] := by
    rw [h10592canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10590sh]; rfl)
  have h10593canon : denoteGraph_ringAttn pm_goal_3 initPM 10937
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10933) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593_L19,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10933).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10589sh]; rfl]
  have h10594canon : denoteGraph_ringAttn pm_goal_3 initPM 10938
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10934) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594_L19,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10934).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10590sh]; rfl]
  have h10593sh : (denoteGraph_ringAttn pm_goal_3 initPM 10937).shape = [2048, 64] := by
    rw [h10593canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10589sh
  have h10594sh : (denoteGraph_ringAttn pm_goal_3 initPM 10938).shape = [2048, 64] := by
    rw [h10594canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10590sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 10925) (denoteGraph_ringAttn pm_goal_3 initPM 10926)
    (denoteGraph_ringAttn pm_goal_3 initPM 10935) (denoteGraph_ringAttn pm_goal_3 initPM 10936)
    (denoteGraph_ringAttn pm_goal_3 initPM 10937) (denoteGraph_ringAttn pm_goal_3 initPM 10938)
    (initPM 10941) (initPM 10942) (initPM 10943) (initPM 10944)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10581sh h10582sh h10591sh h10592sh h10593sh h10594sh hw10597 hw10598 hw10599 hw10600
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_10945, br_pm_10946, br_pm_16554, br_pm_16577,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5708, br_sm_8435, denote_sm_goal_3_5601_L19, br_sm_5703]
  rw [hrouter, h5608, h5609]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5702).shape.reverse.head?).getD 1 = 64 from by rw [hSM5604sh]; rfl]
  rw [hw5600, hcarry5599, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5698) 2048 1024 (by omega) (by omega) h10577 h10578]
  rw [← denote_pm_goal_3_10581_L19, ← denote_pm_goal_3_10582_L19]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10589sh h10590sh]
  rw [← h10591canon, ← h10592canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L19_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5697 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10921,
         denoteGraph_ringAttn pm_goal_3 initPM 10922])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5727
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 11019,
           denoteGraph_ringAttn pm_goal_3 initPM 11020] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5698 = initPM 5698 := hb initGoal_5698 (by decide) rfl
  have hw5612 : initSM 5710 = initPM 5710 := hb initGoal_5710 (by decide) rfl
  have hw5617 : initSM 5715 = initPM 5715 := hb initGoal_5715 (by decide) rfl
  have hw5621 : initSM 5719 = initPM 5719 := hb initGoal_5719 (by decide) rfl
  have hw5626 : initSM 5724 = initPM 5724 := hb initGoal_5724 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5697) (initSM 5698)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10925,
           denoteGraph_ringAttn pm_goal_3 initPM 10926] := by
    rw [hcarry5599, hw5600,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5698) 2048 1024 (by omega) (by omega) h10577 h10578,
        ← denote_pm_goal_3_10581_L19, ← denote_pm_goal_3_10582_L19]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 10925 / 10926
  rw [br_pm_11019, br_pm_11020,
      br_pm_10959, br_pm_10957, br_pm_10951, br_pm_10947, br_pm_16558,
      br_pm_11015, br_pm_11005, br_pm_10999, br_pm_10997,
      br_pm_10975, br_pm_10965, br_pm_10961, br_pm_16562,
      br_pm_10993, br_pm_10983, br_pm_10979, br_pm_16566,
      br_pm_10960, br_pm_10958, br_pm_10952, br_pm_10948, br_pm_16581,
      br_pm_11016, br_pm_11006, br_pm_11000, br_pm_10998,
      br_pm_10976, br_pm_10966, br_pm_10962, br_pm_16585,
      br_pm_10994, br_pm_10984, br_pm_10980, br_pm_16589]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5699
  rw [br_sm_5727, br_sm_5713, br_sm_5712, br_sm_5711,
      br_sm_5709, br_sm_8439,
      br_sm_5726, br_sm_5725, br_sm_5723, br_sm_5722,
      br_sm_5717, br_sm_5716, br_sm_5714, br_sm_8443,
      br_sm_5721, br_sm_5720, br_sm_5718, br_sm_8447,
      denote_sm_goal_3_5601_L19]
  rw [hRMS, hw5612, hw5617, hw5621, hw5626]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 10925 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 10926 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581_L19, rms_sh]; exact h10577
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582_L19, rms_sh]; exact h10578
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5710).shape = [1, 1024] := h_ss_pm 5710 [1, 1024] (by decide)
  have hw29 : (initPM 5715).shape = [512, 1024] := h_ss_pm 5715 [512, 1024] (by decide)
  have hw33 : (initPM 5719).shape = [512, 1024] := h_ss_pm 5719 [512, 1024] (by decide)
  have hw38 : (initPM 5724).shape = [1024, 512] := h_ss_pm 5724 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5710) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5715) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5719) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5710)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5710)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5715)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5715)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5719)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5719)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5710), fw_linear (fw_view [2048, 1024] B) (initPM 5710)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5710)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5710))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5715), fw_linear (fw_view [2048, 1024] B) (initPM 5715)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5719), fw_linear (fw_view [2048, 1024] B) (initPM 5719)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5710)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5710)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5724) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719))))) (initPM 5724)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))))) (initPM 5724)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719))))) (initPM 5724), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))))) (initPM 5724)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719))))) (initPM 5724)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))))) (initPM 5724))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5710))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5710))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5719))))) (initPM 5724)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5715))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5719))))) (initPM 5724)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11033_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024] := by
  have h10517 := hbase345
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10917).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L19, denote_pm_goal_3_10569_L19]; rfl
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L19]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10517 h10573
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10925).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L19, rms_sh]; exact h10577
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 10945).shape = [2048, 1024] := by
    rw [br_pm_10945, br_pm_16554]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 10959).shape = [2048, 1] := by
    rw [br_pm_10959, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10957]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 11015).shape = [2048, 1024] := by
    rw [br_pm_11015]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 11019).shape = [2048, 1024] := by
    rw [br_pm_11019, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10945) (denoteGraph_ringAttn pm_goal_3 initPM 11019)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have h16379sh : (denoteGraph_ringAttn pm_goal_3 initPM 16535).shape = [2048, 1024] := by
    rw [br_pm_16535]; exact h10577
  have h10685sh : (denoteGraph_ringAttn pm_goal_3 initPM 11029).shape = [2048, 1024] := by
    rw [br_pm_11029, br_pm_11023]; exact hinnerA
  rw [br_pm_11033]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16379sh h10685sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_11034_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024] := by
  have h10518 := hbase346
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10918).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L19, denote_pm_goal_3_10570_L19]; rfl
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L19]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10518 h10574
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10926).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L19, rms_sh]; exact h10578
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 10946).shape = [2048, 1024] := by
    rw [br_pm_10946, br_pm_16577]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 10960).shape = [2048, 1] := by
    rw [br_pm_10960, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10958]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 11016).shape = [2048, 1024] := by
    rw [br_pm_11016]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 11020).shape = [2048, 1024] := by
    rw [br_pm_11020, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10946) (denoteGraph_ringAttn pm_goal_3 initPM 11020)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  have h16387sh : (denoteGraph_ringAttn pm_goal_3 initPM 16543).shape = [2048, 1024] := by
    rw [br_pm_16543]; exact h10578
  have h10686sh : (denoteGraph_ringAttn pm_goal_3 initPM 11030).shape = [2048, 1024] := by
    rw [br_pm_11030, br_pm_11024]; exact hinnerB
  rw [br_pm_11034]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16387sh h10686sh

-- ===== carry_5730 =====
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_carry_5730_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t + 1) 0 ≤ 4096)
    (hcarry5681 : denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10861,
         denoteGraph_ringAttn pm_goal_3 initPM 10862])
    (h10861 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024])
    (h10862 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5730 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11033,
         denoteGraph_ringAttn pm_goal_3 initPM 11034] := by
  have hattn := sm_pm_attention_L19_commute initSM initPM hSM hPM hInit hcarry5681 h10861 h10862 h_bound
  have hw5635 : (initPM 5684).shape = [16, 64, 1024] := hPM 5684 [16, 64, 1024] (by decide)
  have hw5644 : (initPM 5693).shape = [1024, 1024] := hPM 5693 [1024, 1024] (by decide)
  have h10693 : (denoteGraph_ringAttn pm_goal_3 initPM 10865).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L19, rms_sh]; exact h10861
  have h10694 : (denoteGraph_ringAttn pm_goal_3 initPM 10866).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L19, rms_sh]; exact h10862
  have h10695d : (denoteGraph_ringAttn pm_goal_3 initPM 10867).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L19]; exact ph_lin_shape_gen _ _ 2048 16 h10693 hw5635
  have h10696d : (denoteGraph_ringAttn pm_goal_3 initPM 10868).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L19]; exact ph_lin_shape_gen _ _ 2048 16 h10694 hw5635
  -- folded-store bridges at the two attention Q tids
  have b1487_10695 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10867
      = denoteGraph_ringAttn pm_goal_3 initPM 10867 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10867 1557 (by decide) (by decide)).symm
  have b1487_10696 : (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM 10868
      = denoteGraph_ringAttn pm_goal_3 initPM 10868 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10868 1557 (by decide) (by decide)).symm
  have b1488_10695 : (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10867
      = denoteGraph_ringAttn pm_goal_3 initPM 10867 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10867 1558 (by decide) (by decide)).symm
  have b1488_10696 : (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM 10868
      = denoteGraph_ringAttn pm_goal_3 initPM 10868 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10868 1558 (by decide) (by decide)).symm
  have h10719 : (denoteGraph_ringAttn pm_goal_3 initPM 10891).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L19_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_19 nR0_19 nR1_19 0 buddy_r0_19 (by decide)]
    have e0 : nR0_19.ins.getD 0 0 = 10867 := by decide
    have e1 : nR1_19.ins.getD 0 0 = 10868 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
         (pm_goal_3.nodes.take 1557).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1487_10695, b1487_10696]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10695d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10720 : (denoteGraph_ringAttn pm_goal_3 initPM 10892).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L19_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_19 nR0_19 nR1_19 1 buddy_r1_19 (by decide)]
    have e0 : nR0_19.ins.getD 0 0 = 10867 := by decide
    have e1 : nR1_19.ins.getD 0 0 = 10868 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_19.ins.getD 0 0),
         (pm_goal_3.nodes.take 1558).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_19.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1488_10695, b1488_10696]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10695d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl

  have hreshape := sm_pm_reshape_float_L19_commute initSM initPM hInit hattn h10719 h10720 hw5644
  have h10745 : (denoteGraph_ringAttn pm_goal_3 initPM 10917).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L19, denote_pm_goal_3_10569_L19]; rfl
  have h10746 : (denoteGraph_ringAttn pm_goal_3 initPM 10918).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L19, denote_pm_goal_3_10570_L19]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L19 initSM initPM hcarry5681 hreshape h10861 h10862 h10745 h10746
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L19]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10861 h10745
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L19]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10862 h10746
  have hgmm := sm_pm_moe_gmm_L19_commute initSM initPM hInit hPM hcarry5599 h10577 h10578
  have hgate := sm_pm_gate_mul_L19_commute initSM initPM hInit hPM hcarry5599 h10577 h10578
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10925).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L19, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10926).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L19, rms_sh]; exact h10578
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 10945).shape = [2048, 1024] := by
    rw [br_pm_10945, br_pm_16554]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 10946).shape = [2048, 1024] := by
    rw [br_pm_10946, br_pm_16577]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 10959).shape = [2048, 1] := by
    rw [br_pm_10959, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10957]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 11015).shape = [2048, 1024] := by
    rw [br_pm_11015]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 11019).shape = [2048, 1024] := by
    rw [br_pm_11019, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 10960).shape = [2048, 1] := by
    rw [br_pm_10960, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10958]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 11016).shape = [2048, 1024] := by
    rw [br_pm_11016]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 11020).shape = [2048, 1024] := by
    rw [br_pm_11020, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10945) (denoteGraph_ringAttn pm_goal_3 initPM 11019)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10946) (denoteGraph_ringAttn pm_goal_3 initPM 11020)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  -- === assemble ===
  rw [br_pm_11033, br_pm_16535, br_pm_11029, br_pm_11023,
      br_pm_11034, br_pm_16543, br_pm_11030, br_pm_11024]
  rw [br_sm_5730, br_sm_8424, br_sm_5729, br_sm_5728]
  rw [hcarry5599, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10945) (denoteGraph_ringAttn pm_goal_3 initPM 10946)
        (denoteGraph_ringAttn pm_goal_3 initPM 11019) (denoteGraph_ringAttn pm_goal_3 initPM 11020)
        h10601sh h10602sh h10675sh h10676sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10921) (denoteGraph_ringAttn pm_goal_3 initPM 10922)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10945) (denoteGraph_ringAttn pm_goal_3 initPM 11019))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10946) (denoteGraph_ringAttn pm_goal_3 initPM 11020))
        h10577 h10578 hinnerA hinnerB]

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L19
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L19
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L19_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L19_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L19_hbound_witness

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11033_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_11034_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5730_commute
