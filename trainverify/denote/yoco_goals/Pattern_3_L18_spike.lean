/-
  Pattern_3_L18_spike.lean — L18 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L18-specific TIDs.  The L18 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L18's Q path
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

/-! ## L18 attention node declarations + buddy proofs.
SM attn node index 714; PM r0 = 1487; PM r1 = 1488. -/

def nSM_18 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5636, 5637, 5638, 5639, 5640], outs := [5641],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_18 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10695, 5637, 5638, 5639, 5640], outs := [10719],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_18 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10696, 5637, 5638, 5639, 5640], outs := [10720],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_18 : ringAttnBuddies sm_goal_3 nSM_18 = [nSM_18] := by
  show (List.filter (fun m => decide (m.op = nSM_18.op) && decide (m.params = nSM_18.params) &&
      decide (m.ins.getD 3 0 = nSM_18.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_18.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_18]
  rw [show (List.filter (fun m => decide (m.op = nSM_18.op) && decide (m.params = nSM_18.params) &&
      decide (m.ins.getD 3 0 = nSM_18.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_18.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_18] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_18 : ringAttnBuddies pm_goal_3 nR0_18 = [nR0_18, nR1_18] := by
  show (List.filter (fun m => decide (m.op = nR0_18.op) && decide (m.params = nR0_18.params) &&
      decide (m.ins.getD 3 0 = nR0_18.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_18.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_18, nR1_18]
  rw [show (List.filter (fun m => decide (m.op = nR0_18.op) && decide (m.params = nR0_18.params) &&
      decide (m.ins.getD 3 0 = nR0_18.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_18.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_18, nR1_18] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_18 : ringAttnBuddies pm_goal_3 nR1_18 = [nR0_18, nR1_18] := by
  show (List.filter (fun m => decide (m.op = nR1_18.op) && decide (m.params = nR1_18.params) &&
      decide (m.ins.getD 3 0 = nR1_18.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_18.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_18, nR1_18]
  rw [show (List.filter (fun m => decide (m.op = nR1_18.op) && decide (m.params = nR1_18.params) &&
      decide (m.ins.getD 3 0 = nR1_18.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_18.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_18, nR1_18] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L18 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L18_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5641
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_18 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5641
      = (sm_goal_3.nodes.take 715).foldl (applyNodeRingAttn sm_goal_3) initSM 5641 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5641 715 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 715 = sm_goal_3.nodes.take 714 ++ [nSM_18] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5636 5637 5638 5639 5640 5641 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L18_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10719
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_18 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10719
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 10719 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10719 1488 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1488 = pm_goal_3.nodes.take 1487 ++ [nR0_18] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10695 5637 5638 5639 5640 10719 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L18_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10720
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_18 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10720
      = (pm_goal_3.nodes.take 1489).foldl (applyNodeRingAttn pm_goal_3) initPM 10720 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10720 1489 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1489 = pm_goal_3.nodes.take 1488 ++ [nR1_18] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10696 5637 5638 5639 5640 10720 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L18) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5634 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5632) (initSM 5633) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5634 8373 5633 712
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8373, 5633], outs := [5634] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8373 5633 5634)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8373 5632 711
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5632], outs := [8373, 8377], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5632 8373 [8373, 8377] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5633 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5636 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5634) (initSM 5635) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5636 5634 5635 713
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5634, 5635], outs := [5636] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5634 5635 5636 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5635 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5642 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5641) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5642 5641 715
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5641], outs := [5642], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5641 5642 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5643 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5642) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5643 5642 716
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5642], outs := [5643], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5642 5643 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5645 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5643) (initSM 5644) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5645 5643 5644 717
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5643, 5644], outs := [5645] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5643 5644 5645)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5644 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5646 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5645) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5646 5645 718
    ({ rank := 0, op := "OpName.FW_view", ins := [5645], outs := [5646], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5645 5646)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5647 =
      denoteGraph_ringAttn sm_goal_3 initSM 5646 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5647 5646 719
    ({ rank := 0, op := "OpName.FW_float", ins := [5646], outs := [5647] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5646 5647 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5648 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5632)
        (denoteGraph_ringAttn sm_goal_3 initSM 5647) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8377 = denoteGraph_ringAttn sm_goal_3 initSM 5632 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8377 5632 711
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5632], outs := [8373, 8377], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5632 8377 [8373, 8377] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5648 8377 5647 720
    ({ rank := 0, op := "OpName.FW_add", ins := [8377, 5647], outs := [5648] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8377 5647 5648)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5650 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5648) (initSM 5649) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5650 8381 5649 722
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8381, 5649], outs := [5650] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8381 5649 5650)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8381 5648 721
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5648], outs := [8381, 8385], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5648 8381 [8381, 8385] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5649 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5651 =
      denoteGraph_ringAttn sm_goal_3 initSM 5650 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5651 8392 724
    ({ rank := 0, op := "OpName.FW_float", ins := [8392], outs := [5651] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8392 5651 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8392 5650 723
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5650 8392 [8392, 8396, 8400, 8404, 8408] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5653 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5651) (initSM 5652) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5653 5651 5652 728
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5651, 5652], outs := [5653] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5651 5652 5653 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5652 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5655 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5653) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5653).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5655 5653 732
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5653], outs := [5654, 5655, 5656], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5653 5654 5655 5656 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5637 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5637 8057 486
    ({ rank := 0, op := "OpName.FW_to", ins := [8057], outs := [5637] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8057 5637 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8057 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8057 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5638 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5638 8115 498
    ({ rank := 0, op := "OpName.FW_to", ins := [8115], outs := [5638] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8115 5638 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8115 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8115 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L18) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10693 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10689) (initPM 5633) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10693 16437 5633 1483
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16437, 5633], outs := [10693] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16437 5633 10693)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16437 10689 1481
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437, 16441], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10689 16437 [16437, 16441] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5633 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10695 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10693) (initPM 5635) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10695 10693 5635 1485
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10693, 5635], outs := [10695] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 10693 5635 10695 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5635 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10721 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10719) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10721 10719 1489
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10719], outs := [10721], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10719 10721 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10727 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10721) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10727 10721 1491
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10721], outs := [10727], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10721 10727 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10731 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10727) (initPM 5644) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10731 10727 5644 1493
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10727, 5644], outs := [10731] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10727 5644 10731)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5644 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10741 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10731) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10741 10731 1495
    ({ rank := 0, op := "OpName.FW_view", ins := [10731], outs := [10741], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10731 10741)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10745 =
      denoteGraph_ringAttn pm_goal_3 initPM 10741 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10745 10741 1497
    ({ rank := 0, op := "OpName.FW_float", ins := [10741], outs := [10745] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10741 10745 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10749 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10689)
        (denoteGraph_ringAttn pm_goal_3 initPM 10745) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16441 = denoteGraph_ringAttn pm_goal_3 initPM 10689 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16441 10689 1481
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437, 16441], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10689 16441 [16437, 16441] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10749 16441 10745 1499
    ({ rank := 0, op := "OpName.FW_add", ins := [16441, 10745], outs := [10749] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16441 10745 10749)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10753 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10749) (initPM 5649) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10753 16453 5649 1503
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16453, 5649], outs := [10753] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16453 5649 10753)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16453 10749 1501
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10749], outs := [16453, 16457], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10749 16453 [16453, 16457] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5649 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10755 =
      denoteGraph_ringAttn pm_goal_3 initPM 10753 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10755 16472 1507
    ({ rank := 0, op := "OpName.FW_float", ins := [16472], outs := [10755] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16472 10755 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16472 10753 1505
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10753 16472 [16472, 16476, 16480, 16484, 16488] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10761 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10755) (initPM 5652) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10761 10755 5652 1515
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [10755, 5652], outs := [10761] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 10755 5652 10761 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5652 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10765 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10761) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10761).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10765 10761 1523
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10761], outs := [10763, 10765, 10767], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 10761 10763 10765 10767 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10694 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10690) (initPM 5633) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10694 16445 5633 1484
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16445, 5633], outs := [10694] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16445 5633 10694)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16445 10690 1482
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445, 16449], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10690 16445 [16445, 16449] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5633 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10696 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10694) (initPM 5635) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10696 10694 5635 1486
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10694, 5635], outs := [10696] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 10694 5635 10696 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5635 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10722 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10720) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10722 10720 1490
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10720], outs := [10722], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10720 10722 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10728 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10722) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10728 10722 1492
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10722], outs := [10728], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10722 10728 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10732 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10728) (initPM 5644) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10732 10728 5644 1494
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10728, 5644], outs := [10732] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10728 5644 10732)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5644 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10742 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10732) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10742 10732 1496
    ({ rank := 1, op := "OpName.FW_view", ins := [10732], outs := [10742], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10732 10742)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10746 =
      denoteGraph_ringAttn pm_goal_3 initPM 10742 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10746 10742 1498
    ({ rank := 1, op := "OpName.FW_float", ins := [10742], outs := [10746] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10742 10746 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10750 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10690)
        (denoteGraph_ringAttn pm_goal_3 initPM 10746) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16449 = denoteGraph_ringAttn pm_goal_3 initPM 10690 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16449 10690 1482
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445, 16449], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10690 16449 [16445, 16449] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10750 16449 10746 1500
    ({ rank := 1, op := "OpName.FW_add", ins := [16449, 10746], outs := [10750] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16449 10746 10750)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10754 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10750) (initPM 5649) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10754 16461 5649 1504
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16461, 5649], outs := [10754] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16461 5649 10754)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16461 10750 1502
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10750], outs := [16461, 16465], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10750 16461 [16461, 16465] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5649 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10756 =
      denoteGraph_ringAttn pm_goal_3 initPM 10754 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10756 16495 1511
    ({ rank := 1, op := "OpName.FW_float", ins := [16495], outs := [10756] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16495 10756 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16495 10754 1506
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10754 16495 [16495, 16499, 16503, 16507, 16511] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10762 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10756) (initPM 5652) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10762 10756 5652 1519
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [10756, 5652], outs := [10762] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 10756 5652 10762 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5652 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10766 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10762) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10762).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10766 10762 1527
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10762], outs := [10764, 10766, 10768], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 10762 10764 10766 10768 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5637 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5637 15839 1037
    ({ rank := 1, op := "OpName.FW_to", ins := [15839], outs := [5637] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15839 5637 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15839 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15839 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5638 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5638 15945 1061
    ({ rank := 1, op := "OpName.FW_to", ins := [15945], outs := [5638] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15945 5638 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15945 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15945 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L18 commute theorems -/

-- Q sharding commute: SM 5636 = allGather0[PM 10695, PM 10696].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10689,
         denoteGraph_ringAttn pm_goal_3 initPM 10690])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024])
    (hw5586 : (initPM 5635).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5636 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10695,
         denoteGraph_ringAttn pm_goal_3 initPM 10696] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5633 = initPM 5633 := hb initGoal_5633 (by decide) rfl
  have hw5586e : initSM 5635 = initPM 5635 := hb initGoal_5635 (by decide) rfl
  rw [denote_sm_goal_3_5587, denote_sm_goal_3_5585,
      denote_pm_goal_3_10523, denote_pm_goal_3_10521,
      denote_pm_goal_3_10524, denote_pm_goal_3_10522]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10689) (initPM 5633)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10690) (initPM 5633)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5633) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5635) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5637).shape = [4096, 4, 64] := by
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
    (denoteGraph_ringAttn pm_goal_3 initPM 5638).shape = [4096, 4, 64] := by
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

-- K/V replication (cross-graph, full tensor): SM 5637 = PM 5637, SM 5638 = PM 5638.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5637 =
      denoteGraph_ringAttn pm_goal_3 initPM 5637 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588, denote_pm_goal_3_5588, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5638 =
      denoteGraph_ringAttn pm_goal_3 initPM 5638 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589, denote_pm_goal_3_5589, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L18 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L18_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10689,
         denoteGraph_ringAttn pm_goal_3 initPM 10690])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5641 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10719,
         denoteGraph_ringAttn pm_goal_3 initPM 10720] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5635).shape = [16, 64, 1024] := hPM 5635 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L18_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L18_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L18_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape initPM hPM
  have hVsh := pm_5589_shape initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10693).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10694).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 10695).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 10696).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5636).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5636).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5637).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5638).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 714)
  have bSM5587 : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5636 = denoteGraph_ringAttn sm_goal_3 initSM 5636 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5636 714 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5637 = denoteGraph_ringAttn sm_goal_3 initSM 5637 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5637 714 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5638 = denoteGraph_ringAttn sm_goal_3 initSM 5638 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5638 714 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1487)
  have bPM10523 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10695 = denoteGraph_ringAttn pm_goal_3 initPM 10695 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10695 1487 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10696 = denoteGraph_ringAttn pm_goal_3 initPM 10696 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10696 1487 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5637 = denoteGraph_ringAttn pm_goal_3 initPM 5637 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5637 1487 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5638 = denoteGraph_ringAttn pm_goal_3 initPM 5638 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5638 1487 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5639 = initSM 5639 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 714) initSM 5639 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5640 = initSM 5640 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 714) initSM 5640 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5639 = initPM 5639 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1487) initPM 5639 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5640 = initPM 5640 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1487) initPM 5640 (by decide) (by decide)
  have hw5590 : initSM 5639 = initPM 5639 := hb initGoal_5639 (by decide) rfl
  have hw5591 : initSM 5640 = initPM 5640 := hb initGoal_5640 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5636).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5637).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5638).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 0 0),
        (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5636 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10695,
        (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10696]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5637 =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5637
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5638 =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5638
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5637).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5638).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5640)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5639 =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5639
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_18.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM 5640 =
      (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5640
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 0 0),
       (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10695,
       (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10696]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 0 0),
          (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 1 0),
          (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 2 0),
          (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 4 0))
        (nR0_18.params.getD 0 1) (nR0_18.params.getD 1 1) (nR0_18.params.getD 2 1) (nR0_18.params.getD 3 1)
        (decide (nR0_18.params.getD 4 0 ≠ 0)) (nR0_18.params.getD 5 0)).shape
        = [2 * 2048, nR0_18.params.getD 0 1, nR0_18.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1487 -> take 1488)
  have e10523 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10695
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 10695 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10695 1487 1488 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10696
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 10696 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10696 1487 1488 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5637
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 5637 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5637 1487 1488 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5638
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 5638 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5638 1487 1488 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5639
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 5639 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5639 1487 1488 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 5640
      = (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 5640 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5640 1487 1488 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_18
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_18 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_18]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_18]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_18]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 714).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_18 nR0_18 nR1_18 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_18 buddy_r0_18 buddy_r1_18 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L18_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L18_r0_bridge, ← denote_pm_attn_L18_r1_bridge]


/-! ## L18 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5641 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10719,
         denoteGraph_ringAttn pm_goal_3 initPM 10720])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10719).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10720).shape = [2048, 16, 64])
    (hw5595 : (initPM 5644).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5647 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10745,
         denoteGraph_ringAttn pm_goal_3 initPM 10746] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5644 = initPM 5644 := hb initGoal_5644 (by decide) rfl
  rw [denote_sm_goal_3_5598, denote_sm_goal_3_5597, denote_sm_goal_3_5596,
      denote_sm_goal_3_5594, denote_sm_goal_3_5593,
      denote_pm_goal_3_10573, denote_pm_goal_3_10569, denote_pm_goal_3_10559,
      denote_pm_goal_3_10555, denote_pm_goal_3_10549,
      denote_pm_goal_3_10574, denote_pm_goal_3_10570, denote_pm_goal_3_10560,
      denote_pm_goal_3_10556, denote_pm_goal_3_10550]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10719))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10720))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5644) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10719))) (initPM 5644)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10720))) (initPM 5644)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10719))) (initPM 5644),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10720))) (initPM 5644)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10689,
         denoteGraph_ringAttn pm_goal_3 initPM 10690])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5647 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10745,
         denoteGraph_ringAttn pm_goal_3 initPM 10746])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10745).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10746).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5648 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10749,
         denoteGraph_ringAttn pm_goal_3 initPM 10750] := by
  rw [denote_sm_goal_3_5599, denote_pm_goal_3_10577, denote_pm_goal_3_10578]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5648 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10749,
         denoteGraph_ringAttn pm_goal_3 initPM 10750])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5653 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10761,
         denoteGraph_ringAttn pm_goal_3 initPM 10762] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5649 = initPM 5649 := hb initGoal_5649 (by decide) rfl
  have hw5603 : initSM 5652 = initPM 5652 := hb initGoal_5652 (by decide) rfl
  have hw5603sh : (initPM 5652).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5652 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5652] using hsh
  rw [denote_sm_goal_3_5604, denote_sm_goal_3_5602, denote_sm_goal_3_5601,
      denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581,
      denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5649) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10749) (initPM 5649)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10750) (initPM 5649)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5652) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L18 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5648 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10749,
         denoteGraph_ringAttn pm_goal_3 initPM 10750])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5655 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10765,
         denoteGraph_ringAttn pm_goal_3 initPM 10766] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5652).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5652 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5652] using hsh
  have hnl := sm_pm_nl_L18_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 10761).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581]
    exact nl_sh 2048 1024 64 _ (initPM 5652) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 10762).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
    exact nl_sh 2048 1024 64 _ (initPM 5652) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5653).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606, denote_pm_goal_3_10593, denote_pm_goal_3_10594]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5653).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10761).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10762).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L18 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L18_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10689,
         denoteGraph_ringAttn pm_goal_3 initPM 10690])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5641 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10719,
         denoteGraph_ringAttn pm_goal_3 initPM 10720])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10719).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10720).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024])
    (hw5595 : (initPM 5644).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5655 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10765,
         denoteGraph_ringAttn pm_goal_3 initPM 10766] := by
  have hreshape := sm_pm_reshape_float_L18_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10745).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573, denote_pm_goal_3_10569]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10746).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574, denote_pm_goal_3_10570]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L18 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L18 router — fully assembled

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
theorem sm_pm_router_commute_L18_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5632 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10689,
         denoteGraph_ringAttn pm_goal_3 initPM 10690])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5655 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10765,
         denoteGraph_ringAttn pm_goal_3 initPM 10766] := by
  have hattn := sm_pm_attention_L18_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5635).shape = [16, 64, 1024] := hPM 5635 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5644).shape = [1024, 1024] := hPM 5644 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10693).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10694).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10695).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10696).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10695
      = denoteGraph_ringAttn pm_goal_3 initPM 10695 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10695 1487 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM 10696
      = denoteGraph_ringAttn pm_goal_3 initPM 10696 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10696 1487 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 10695
      = denoteGraph_ringAttn pm_goal_3 initPM 10695 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10695 1488 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM 10696
      = denoteGraph_ringAttn pm_goal_3 initPM 10696 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10696 1488 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10719).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L18_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_18 nR0_18 nR1_18 0 buddy_r0_18 (by decide)]
    have e0 : nR0_18.ins.getD 0 0 = 10695 := by decide
    have e1 : nR1_18.ins.getD 0 0 = 10696 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 0 0),
         (pm_goal_3.nodes.take 1487).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10720).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L18_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_18 nR0_18 nR1_18 1 buddy_r1_18 (by decide)]
    have e0 : nR0_18.ins.getD 0 0 = 10695 := by decide
    have e1 : nR1_18.ins.getD 0 0 = 10696 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_18.ins.getD 0 0),
         (pm_goal_3.nodes.take 1488).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_18.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L18_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L18_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L18
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L18_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L18_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L18_hbound_witness
