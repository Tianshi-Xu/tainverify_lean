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
theorem denote_sm_goal_3_5585 (initSM : Store) :
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
theorem denote_sm_goal_3_5587 (initSM : Store) :
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
theorem denote_sm_goal_3_5593 (initSM : Store) :
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
theorem denote_sm_goal_3_5594 (initSM : Store) :
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
theorem denote_sm_goal_3_5596 (initSM : Store) :
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
theorem denote_sm_goal_3_5597 (initSM : Store) :
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
theorem denote_sm_goal_3_5598 (initSM : Store) :
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
theorem denote_sm_goal_3_5599 (initSM : Store) :
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
theorem denote_sm_goal_3_5601 (initSM : Store) :
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
theorem denote_sm_goal_3_5602 (initSM : Store) :
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
theorem denote_sm_goal_3_5604 (initSM : Store) :
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
theorem denote_sm_goal_3_5606 (initSM : Store) :
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
theorem denote_sm_goal_3_5588 (initSM : Store) :
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
theorem denote_sm_goal_3_5589 (initSM : Store) :
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
theorem denote_pm_goal_3_10521 (initPM : Store) :
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
theorem denote_pm_goal_3_10523 (initPM : Store) :
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
theorem denote_pm_goal_3_10549 (initPM : Store) :
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
theorem denote_pm_goal_3_10555 (initPM : Store) :
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
theorem denote_pm_goal_3_10559 (initPM : Store) :
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
theorem denote_pm_goal_3_10569 (initPM : Store) :
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
theorem denote_pm_goal_3_10573 (initPM : Store) :
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
theorem denote_pm_goal_3_10577 (initPM : Store) :
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
theorem denote_pm_goal_3_10581 (initPM : Store) :
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
theorem denote_pm_goal_3_10583 (initPM : Store) :
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
theorem denote_pm_goal_3_10589 (initPM : Store) :
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
theorem denote_pm_goal_3_10593 (initPM : Store) :
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
theorem denote_pm_goal_3_10522 (initPM : Store) :
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
theorem denote_pm_goal_3_10524 (initPM : Store) :
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
theorem denote_pm_goal_3_10550 (initPM : Store) :
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
theorem denote_pm_goal_3_10556 (initPM : Store) :
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
theorem denote_pm_goal_3_10560 (initPM : Store) :
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
theorem denote_pm_goal_3_10570 (initPM : Store) :
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
theorem denote_pm_goal_3_10574 (initPM : Store) :
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
theorem denote_pm_goal_3_10578 (initPM : Store) :
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
theorem denote_pm_goal_3_10582 (initPM : Store) :
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
theorem denote_pm_goal_3_10584 (initPM : Store) :
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
theorem denote_pm_goal_3_10590 (initPM : Store) :
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
theorem denote_pm_goal_3_10594 (initPM : Store) :
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
theorem denote_pm_goal_3_5588 (initPM : Store) :
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
theorem denote_pm_goal_3_5589 (initPM : Store) :
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
  rw [denote_sm_goal_3_5587, denote_sm_goal_3_5585,
      denote_pm_goal_3_10523, denote_pm_goal_3_10521,
      denote_pm_goal_3_10524, denote_pm_goal_3_10522]
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
theorem pm_5588_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5686).shape = [4096, 4, 64] := by
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
    (denoteGraph_ringAttn pm_goal_3 initPM 5687).shape = [4096, 4, 64] := by
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
  rw [denote_sm_goal_3_5588, denote_pm_goal_3_5588, ← denote_sm_goal_3_5343,
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
  rw [denote_sm_goal_3_5589, denote_pm_goal_3_5589, ← denote_sm_goal_3_5344,
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
  have hKsh := pm_5588_shape initPM hPM
  have hVsh := pm_5589_shape initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10865).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10866).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 10867).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 10868).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
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
  rw [denote_sm_goal_3_5598, denote_sm_goal_3_5597, denote_sm_goal_3_5596,
      denote_sm_goal_3_5594, denote_sm_goal_3_5593,
      denote_pm_goal_3_10573, denote_pm_goal_3_10569, denote_pm_goal_3_10559,
      denote_pm_goal_3_10555, denote_pm_goal_3_10549,
      denote_pm_goal_3_10574, denote_pm_goal_3_10570, denote_pm_goal_3_10560,
      denote_pm_goal_3_10556, denote_pm_goal_3_10550]
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
theorem sm_pm_carry_5599_commute (initSM initPM : Store)
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
  rw [denote_sm_goal_3_5599, denote_pm_goal_3_10577, denote_pm_goal_3_10578]
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
  rw [denote_sm_goal_3_5604, denote_sm_goal_3_5602, denote_sm_goal_3_5601,
      denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581,
      denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
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
    rw [denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581]
    exact nl_sh 2048 1024 64 _ (initPM 5701) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 10934).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
    exact nl_sh 2048 1024 64 _ (initPM 5701) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5702).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606, denote_pm_goal_3_10593, denote_pm_goal_3_10594]
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
    rw [denote_pm_goal_3_10573, denote_pm_goal_3_10569]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10918).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574, denote_pm_goal_3_10570]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10921).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10922).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
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
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10866).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10867).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10868).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
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

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L19_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L19
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L19_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L19_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L19_hbound_witness
