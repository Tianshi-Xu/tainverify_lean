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
theorem denote_sm_goal_3_5585_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5587_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5593_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5594_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5596_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5597_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5598_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5599_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5601_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5602_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5604_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5606_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5588_L18 (initSM : Store) :
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
theorem denote_sm_goal_3_5589_L18 (initSM : Store) :
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
theorem denote_pm_goal_3_10521_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10523_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10549_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10555_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10559_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10569_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10573_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10577_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10581_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10583_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10589_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10593_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10522_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10524_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10550_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10556_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10560_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10570_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10574_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10578_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10582_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10584_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10590_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_10594_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_5588_L18 (initPM : Store) :
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
theorem denote_pm_goal_3_5589_L18 (initPM : Store) :
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
  rw [denote_sm_goal_3_5587_L18, denote_sm_goal_3_5585_L18,
      denote_pm_goal_3_10523_L18, denote_pm_goal_3_10521_L18,
      denote_pm_goal_3_10524_L18, denote_pm_goal_3_10522_L18]
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
theorem pm_5588_shape_L18 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5637).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5588_L18, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5589_shape_L18 (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5638).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5589_L18, denote_pm_goal_3_5336]
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
  rw [denote_sm_goal_3_5588_L18, denote_pm_goal_3_5588_L18, ← denote_sm_goal_3_5343,
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
  rw [denote_sm_goal_3_5589_L18, denote_pm_goal_3_5589_L18, ← denote_sm_goal_3_5344,
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
  have hKsh := pm_5588_shape_L18 initPM hPM
  have hVsh := pm_5589_shape_L18 initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10693).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521_L18, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10694).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L18, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 10695).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L18]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 10696).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L18]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
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
  rw [denote_sm_goal_3_5598_L18, denote_sm_goal_3_5597_L18, denote_sm_goal_3_5596_L18,
      denote_sm_goal_3_5594_L18, denote_sm_goal_3_5593_L18,
      denote_pm_goal_3_10573_L18, denote_pm_goal_3_10569_L18, denote_pm_goal_3_10559_L18,
      denote_pm_goal_3_10555_L18, denote_pm_goal_3_10549_L18,
      denote_pm_goal_3_10574_L18, denote_pm_goal_3_10570_L18, denote_pm_goal_3_10560_L18,
      denote_pm_goal_3_10556_L18, denote_pm_goal_3_10550_L18]
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
theorem sm_pm_carry_5599_commute_L18 (initSM initPM : Store)
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
  rw [denote_sm_goal_3_5599_L18, denote_pm_goal_3_10577_L18, denote_pm_goal_3_10578_L18]
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
  rw [denote_sm_goal_3_5604_L18, denote_sm_goal_3_5602_L18, denote_sm_goal_3_5601_L18,
      denote_pm_goal_3_10589_L18, denote_pm_goal_3_10583_L18, denote_pm_goal_3_10581_L18,
      denote_pm_goal_3_10590_L18, denote_pm_goal_3_10584_L18, denote_pm_goal_3_10582_L18]
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
    rw [denote_pm_goal_3_10589_L18, denote_pm_goal_3_10583_L18, denote_pm_goal_3_10581_L18]
    exact nl_sh 2048 1024 64 _ (initPM 5652) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 10762).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L18, denote_pm_goal_3_10584_L18, denote_pm_goal_3_10582_L18]
    exact nl_sh 2048 1024 64 _ (initPM 5652) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5653).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606_L18, denote_pm_goal_3_10593_L18, denote_pm_goal_3_10594_L18]
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
    rw [denote_pm_goal_3_10573_L18, denote_pm_goal_3_10569_L18]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10746).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L18, denote_pm_goal_3_10570_L18]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute_L18 initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L18]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L18]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
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
    rw [denote_pm_goal_3_10521_L18, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10694).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522_L18, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10695).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523_L18]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10696).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524_L18]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
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


-- ================= L18 MoE carry (sm_pm_carry_5681_commute) =================
theorem br_pm_16441 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16441 = denoteGraph_ringAttn pm_goal_3 initPM 10689 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16441 10689 1481
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437, 16441], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10689 16441 [16437, 16441] 2 (by decide) (by decide))
    rfl

theorem br_pm_16449 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16449 = denoteGraph_ringAttn pm_goal_3 initPM 10690 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16449 10690 1482
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445, 16449], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10690 16449 [16445, 16449] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10763 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10763 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10761) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10761).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10763 10761 1523
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10761], outs := [10763, 10765, 10767], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 10761 10763 10765 10767 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10764 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10764 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10762) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10762).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10764 10762 1527
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10762], outs := [10764, 10766, 10768], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 10762 10764 10766 10768 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10773 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10773 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16476)
        (denoteGraph_ringAttn pm_goal_3 initPM 10763)
        (denoteGraph_ringAttn pm_goal_3 initPM 10765)
        [initPM 10769, initPM 10770] [initPM 10771, initPM 10772]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10773 16476 10763 10765 10769 10770 10771 10772 1531
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16476, 10763, 10765, 10769, 10770, 10771, 10772], outs := [10773], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16476 10763 10765 10769 10770 10771 10772 10773 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10769 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10770 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10771 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10772 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10774 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10774 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16499)
        (denoteGraph_ringAttn pm_goal_3 initPM 10764)
        (denoteGraph_ringAttn pm_goal_3 initPM 10766)
        [initPM 10769, initPM 10770] [initPM 10771, initPM 10772]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10774 16499 10764 10766 10769 10770 10771 10772 1534
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16499, 10764, 10766, 10769, 10770, 10771, 10772], outs := [10774], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16499 10764 10766 10769 10770 10771 10772 10774 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10769 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10770 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10771 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10772 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10775 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10775 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16480) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10775 16480 1508
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16480], outs := [10775], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16480 10775 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10776 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10776 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16503) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10776 16503 1512
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16503], outs := [10776], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16503 10776 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10779 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10779 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10775) (initPM 5661) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10779 10775 5661 1516
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10775, 5661], outs := [10779] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10775 5661 10779)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5661 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10780 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10780 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10776) (initPM 5661) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10780 10776 5661 1520
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10776, 5661], outs := [10780] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10776 5661 10780)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5661 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10785 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10785 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10779) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10785 10779 1524
    ({ rank := 0, op := "OpName.FW_view", ins := [10779], outs := [10785], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 10779 10785)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10786 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10786 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10780) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10786 10780 1528
    ({ rank := 1, op := "OpName.FW_view", ins := [10780], outs := [10786], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 10780 10786)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10787 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10787 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10785) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10787 10785 1532
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [10785], outs := [10787] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 10785 10787])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10788 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10788 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10786) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10788 10786 1535
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [10786], outs := [10788] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 10786 10788])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10789 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10789 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16484) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10789 16484 1509
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16484], outs := [10789], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16484 10789 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10790 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10790 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16507) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10790 16507 1513
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16507], outs := [10790], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16507 10790 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10793 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10793 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10789) (initPM 5666) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10793 10789 5666 1517
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10789, 5666], outs := [10793] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10789 5666 10793)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5666 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10794 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10794 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10790) (initPM 5666) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10794 10790 5666 1521
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10790, 5666], outs := [10794] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10790 5666 10794)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5666 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10803 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10803 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10793) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10803 10793 1525
    ({ rank := 0, op := "OpName.FW_view", ins := [10793], outs := [10803], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10793 10803)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10804 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10804 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10794) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10804 10794 1529
    ({ rank := 1, op := "OpName.FW_view", ins := [10794], outs := [10804], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10794 10804)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10807 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10807 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16488) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10807 16488 1510
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16488], outs := [10807], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16488 10807 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10808 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10808 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16511) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10808 16511 1514
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16511], outs := [10808], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16511 10808 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10811 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10811 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10807) (initPM 5670) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10811 10807 5670 1518
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10807, 5670], outs := [10811] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10807 5670 10811)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5670 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10812 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10812 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10808) (initPM 5670) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10812 10808 5670 1522
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10808, 5670], outs := [10812] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10808 5670 10812)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5670 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10821 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10821 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10811) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10821 10811 1526
    ({ rank := 0, op := "OpName.FW_view", ins := [10811], outs := [10821], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10811 10821)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10822 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10822 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10812) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10822 10812 1530
    ({ rank := 1, op := "OpName.FW_view", ins := [10812], outs := [10822], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10812 10822)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10825 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10825 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10803) (denoteGraph_ringAttn pm_goal_3 initPM 10821) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10825 10803 10821 1533
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [10803, 10821], outs := [10825] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 10803 10821 10825])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10826 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10826 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10804) (denoteGraph_ringAttn pm_goal_3 initPM 10822) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10826 10804 10822 1536
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [10804, 10822], outs := [10826] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 10804 10822 10826])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10827 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10827 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10825) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10827 10825 1537
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10825], outs := [10827], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10825 10827 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10828 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10828 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10826) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10828 10826 1538
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10826], outs := [10828], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10826 10828 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10833 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10833 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10827) (initPM 5675) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10833 10827 5675 1539
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10827, 5675], outs := [10833] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10827 5675 10833)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5675 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10834 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10834 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10828) (initPM 5675) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10834 10828 5675 1540
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10828, 5675], outs := [10834] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10828 5675 10834)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5675 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10843 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10843 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10833) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10843 10833 1541
    ({ rank := 0, op := "OpName.FW_view", ins := [10833], outs := [10843], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10833 10843)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10844 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10844 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10834) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10844 10834 1542
    ({ rank := 1, op := "OpName.FW_view", ins := [10834], outs := [10844], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10834 10844)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10847 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10847 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10787) (denoteGraph_ringAttn pm_goal_3 initPM 10843) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10847 10787 10843 1543
    ({ rank := 0, op := "OpName.FW_mul", ins := [10787, 10843], outs := [10847] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 10787 10843 10847])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10848 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10848 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10788) (denoteGraph_ringAttn pm_goal_3 initPM 10844) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10848 10788 10844 1544
    ({ rank := 1, op := "OpName.FW_mul", ins := [10788, 10844], outs := [10848] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 10788 10844 10848])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10851 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10851 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10773) (denoteGraph_ringAttn pm_goal_3 initPM 10847) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10851 10773 10847 1545
    ({ rank := 0, op := "OpName.FW_add", ins := [10773, 10847], outs := [10851] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 10773 10847 10851)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10852 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10852 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10774) (denoteGraph_ringAttn pm_goal_3 initPM 10848) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10852 10774 10848 1546
    ({ rank := 1, op := "OpName.FW_add", ins := [10774, 10848], outs := [10852] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 10774 10848 10852)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10857 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10857 =
      denoteGraph_ringAttn pm_goal_3 initPM 10851 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10857 10851 1547
    ({ rank := 0, op := "OpName.FW_float", ins := [10851], outs := [10857] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10851 10857 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10858 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10858 =
      denoteGraph_ringAttn pm_goal_3 initPM 10852 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10858 10852 1548
    ({ rank := 1, op := "OpName.FW_float", ins := [10852], outs := [10858] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10852 10858 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10861 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10861 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16457) (denoteGraph_ringAttn pm_goal_3 initPM 10857) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10861 16457 10857 1549
    ({ rank := 0, op := "OpName.FW_add", ins := [16457, 10857], outs := [10861] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16457 10857 10861)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10862 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10862 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16465) (denoteGraph_ringAttn pm_goal_3 initPM 10858) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10862 16465 10858 1550
    ({ rank := 1, op := "OpName.FW_add", ins := [16465, 10858], outs := [10862] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16465 10858 10862)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16457 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16457 =
      denoteGraph_ringAttn pm_goal_3 initPM 10749 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16457 10749 1501
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10749], outs := [16453, 16457], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 10749 16453 16457 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16465 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16465 =
      denoteGraph_ringAttn pm_goal_3 initPM 10750 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16465 10750 1502
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10750], outs := [16461, 16465], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 10750 16461 16465 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16476 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16476 =
      denoteGraph_ringAttn pm_goal_3 initPM 10753 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16476 10753 1505
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 10753 16472 16476 16480 16484 16488 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16480 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16480 =
      denoteGraph_ringAttn pm_goal_3 initPM 10753 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16480 10753 1505
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 10753 16472 16476 16480 16484 16488 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16484 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16484 =
      denoteGraph_ringAttn pm_goal_3 initPM 10753 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16484 10753 1505
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 10753 16472 16476 16480 16484 16488 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16488 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16488 =
      denoteGraph_ringAttn pm_goal_3 initPM 10753 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16488 10753 1505
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 10753 16472 16476 16480 16484 16488 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16499 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16499 =
      denoteGraph_ringAttn pm_goal_3 initPM 10754 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16499 10754 1506
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 10754 16495 16499 16503 16507 16511 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16503 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16503 =
      denoteGraph_ringAttn pm_goal_3 initPM 10754 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16503 10754 1506
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 10754 16495 16499 16503 16507 16511 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16507 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16507 =
      denoteGraph_ringAttn pm_goal_3 initPM 10754 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16507 10754 1506
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 10754 16495 16499 16503 16507 16511 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16511 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16511 =
      denoteGraph_ringAttn pm_goal_3 initPM 10754 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16511 10754 1506
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 10754 16495 16499 16503 16507 16511 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5654 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5654 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5653) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5653).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5654 5653 732
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5653], outs := [5654, 5655, 5656], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5653 5654 5655 5656 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5659 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5659 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8396)
        (denoteGraph_ringAttn sm_goal_3 initSM 5654)
        (denoteGraph_ringAttn sm_goal_3 initSM 5655)
        (initSM 5657) (initSM 5658) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5659 8396 5654 5655 5657 5658 736
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8396, 5654, 5655, 5657, 5658], outs := [5659], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8396 5654 5655 5657 5658 5659 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5657 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5658 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5660 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5660 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8400) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5660 8400 725
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8400], outs := [5660], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8400 5660 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5662 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5662 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5660) (initSM 5661) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5662 5660 5661 729
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5660, 5661], outs := [5662] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5660 5661 5662)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5661 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5663 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5663 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5662) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5663 5662 733
    ({ rank := 0, op := "OpName.FW_view", ins := [5662], outs := [5663], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5662 5663)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5664 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5664 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5663) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5664 5663 737
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5663], outs := [5664] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5663 5664])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5665 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5665 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8404) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5665 8404 726
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8404], outs := [5665], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8404 5665 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5667 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5667 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5665) (initSM 5666) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5667 5665 5666 730
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5665, 5666], outs := [5667] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5665 5666 5667)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5666 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5668 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5668 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5667) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5668 5667 734
    ({ rank := 0, op := "OpName.FW_view", ins := [5667], outs := [5668], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5667 5668)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5669 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5669 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8408) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5669 8408 727
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8408], outs := [5669], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8408 5669 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5671 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5671 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5669) (initSM 5670) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5671 5669 5670 731
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5669, 5670], outs := [5671] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5669 5670 5671)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5670 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5672 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5672 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5671) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5672 5671 735
    ({ rank := 0, op := "OpName.FW_view", ins := [5671], outs := [5672], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5671 5672)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5673 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5673 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5668) (denoteGraph_ringAttn sm_goal_3 initSM 5672) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5673 5668 5672 738
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5668, 5672], outs := [5673] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5668 5672 5673])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5674 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5674 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5673) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5674 5673 739
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5673], outs := [5674], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5673 5674 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5676 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5676 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5674) (initSM 5675) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5676 5674 5675 740
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5674, 5675], outs := [5676] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5674 5675 5676)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5675 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5677 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5677 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5676) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5677 5676 741
    ({ rank := 0, op := "OpName.FW_view", ins := [5676], outs := [5677], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5676 5677)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5678 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5678 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5664) (denoteGraph_ringAttn sm_goal_3 initSM 5677) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5678 5664 5677 742
    ({ rank := 0, op := "OpName.FW_mul", ins := [5664, 5677], outs := [5678] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5664 5677 5678])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5679 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5679 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5659) (denoteGraph_ringAttn sm_goal_3 initSM 5678) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5679 5659 5678 743
    ({ rank := 0, op := "OpName.FW_add", ins := [5659, 5678], outs := [5679] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5659 5678 5679)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5680 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5680 =
      denoteGraph_ringAttn sm_goal_3 initSM 5679 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5680 5679 744
    ({ rank := 0, op := "OpName.FW_float", ins := [5679], outs := [5680] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5679 5680 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5681 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5681 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8385) (denoteGraph_ringAttn sm_goal_3 initSM 5680) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5681 8385 5680 745
    ({ rank := 0, op := "OpName.FW_add", ins := [8385, 5680], outs := [5681] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8385 5680 5681)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8385 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8385 =
      denoteGraph_ringAttn sm_goal_3 initSM 5648 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8385 5648 721
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5648], outs := [8381, 8385], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5648 8381 8385 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8396 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8396 =
      denoteGraph_ringAttn sm_goal_3 initSM 5650 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8396 5650 723
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5650 8392 8396 8400 8404 8408 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8400 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8400 =
      denoteGraph_ringAttn sm_goal_3 initSM 5650 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8400 5650 723
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5650 8392 8396 8400 8404 8408 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8404 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8404 =
      denoteGraph_ringAttn sm_goal_3 initSM 5650 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8404 5650 723
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5650 8392 8396 8400 8404 8408 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8408 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8408 =
      denoteGraph_ringAttn sm_goal_3 initSM 5650 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8408 5650 723
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5650 8392 8396 8400 8404 8408 (by decide) (by decide) (by decide) (by decide))
    rfl


-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5648 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10749,
         denoteGraph_ringAttn pm_goal_3 initPM 10750])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5659 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10773,
         denoteGraph_ringAttn pm_goal_3 initPM 10774] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5649 = initPM 5649 := hb initGoal_5649 (by decide) rfl
  have hw5603sh : (initPM 5652).shape = [64, 1024] := by
    have hgh := hII initGoal_5652 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5652] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5608 : initSM 5657 = allGatherPrimDimN 0 2 0 [initPM 10769, initPM 10770] := by
    have hg := hII initGoal_5657 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5657, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10769) (initPM 10770) []
        (by rw [h_ss_pm 10769 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5609 : initSM 5658 = allGatherPrimDimN 0 2 0 [initPM 10771, initPM 10772] := by
    have hg := hII initGoal_5658 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5658, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10771) (initPM 10772) []
        (by rw [h_ss_pm 10771 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L18_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hrouter := sm_pm_router_commute_L18 initSM initPM hInit hcarry5599 h10577 h10578
  -- PM rms output shapes [2048, 1024]
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10753).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L18, rms_sh]; exact h10577
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10754).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L18, rms_sh]; exact h10578
  -- PM nl output shapes [2048, 64]
  have h10589sh : (denoteGraph_ringAttn pm_goal_3 initPM 10761).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589_L18, denote_pm_goal_3_10583_L18, denote_pm_goal_3_10581_L18]
    exact nl_sh 2048 1024 64 _ (initPM 5652) (by rw [rms_sh]; exact h10577) hw5603sh
  have h10590sh : (denoteGraph_ringAttn pm_goal_3 initPM 10762).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590_L18, denote_pm_goal_3_10584_L18, denote_pm_goal_3_10582_L18]
    exact nl_sh 2048 1024 64 _ (initPM 5652) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5653).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10589sh
  -- MoE weight shapes
  have hw10597 : (initPM 10769).shape = [32,1024,1024] := h_ss_pm 10769 [32,1024,1024] (by decide)
  have hw10598 : (initPM 10770).shape = [32,1024,1024] := h_ss_pm 10770 [32,1024,1024] (by decide)
  have hw10599 : (initPM 10771).shape = [32,1024,512] := h_ss_pm 10771 [32,1024,512] (by decide)
  have hw10600 : (initPM 10772).shape = [32,1024,512] := h_ss_pm 10772 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10591canon : denoteGraph_ringAttn pm_goal_3 initPM 10763
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10761) 8 64).fst := by
    rw [br_pm_10763,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10761).shape.reverse.head?).getD 1 = 64 from by rw [h10589sh]; rfl]
  have h10592canon : denoteGraph_ringAttn pm_goal_3 initPM 10764
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10762) 8 64).fst := by
    rw [br_pm_10764,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10762).shape.reverse.head?).getD 1 = 64 from by rw [h10590sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10591sh : (denoteGraph_ringAttn pm_goal_3 initPM 10763).shape = [2048, 64] := by
    rw [h10591canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10589sh]; rfl)
  have h10592sh : (denoteGraph_ringAttn pm_goal_3 initPM 10764).shape = [2048, 64] := by
    rw [h10592canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10590sh]; rfl)
  have h10593canon : denoteGraph_ringAttn pm_goal_3 initPM 10765
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10761) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593_L18,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10761).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10589sh]; rfl]
  have h10594canon : denoteGraph_ringAttn pm_goal_3 initPM 10766
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10762) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594_L18,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10762).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10590sh]; rfl]
  have h10593sh : (denoteGraph_ringAttn pm_goal_3 initPM 10765).shape = [2048, 64] := by
    rw [h10593canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10589sh
  have h10594sh : (denoteGraph_ringAttn pm_goal_3 initPM 10766).shape = [2048, 64] := by
    rw [h10594canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10590sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 10753) (denoteGraph_ringAttn pm_goal_3 initPM 10754)
    (denoteGraph_ringAttn pm_goal_3 initPM 10763) (denoteGraph_ringAttn pm_goal_3 initPM 10764)
    (denoteGraph_ringAttn pm_goal_3 initPM 10765) (denoteGraph_ringAttn pm_goal_3 initPM 10766)
    (initPM 10769) (initPM 10770) (initPM 10771) (initPM 10772)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10581sh h10582sh h10591sh h10592sh h10593sh h10594sh hw10597 hw10598 hw10599 hw10600
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_10773, br_pm_10774, br_pm_16476, br_pm_16499,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5659, br_sm_8396, denote_sm_goal_3_5601_L18, br_sm_5654]
  rw [hrouter, h5608, h5609]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5653).shape.reverse.head?).getD 1 = 64 from by rw [hSM5604sh]; rfl]
  rw [hw5600, hcarry5599, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5649) 2048 1024 (by omega) (by omega) h10577 h10578]
  rw [← denote_pm_goal_3_10581_L18, ← denote_pm_goal_3_10582_L18]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10589sh h10590sh]
  rw [← h10591canon, ← h10592canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L18_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5648 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10749,
         denoteGraph_ringAttn pm_goal_3 initPM 10750])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5678
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10847,
           denoteGraph_ringAttn pm_goal_3 initPM 10848] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5649 = initPM 5649 := hb initGoal_5649 (by decide) rfl
  have hw5612 : initSM 5661 = initPM 5661 := hb initGoal_5661 (by decide) rfl
  have hw5617 : initSM 5666 = initPM 5666 := hb initGoal_5666 (by decide) rfl
  have hw5621 : initSM 5670 = initPM 5670 := hb initGoal_5670 (by decide) rfl
  have hw5626 : initSM 5675 = initPM 5675 := hb initGoal_5675 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5648) (initSM 5649)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10753,
           denoteGraph_ringAttn pm_goal_3 initPM 10754] := by
    rw [hcarry5599, hw5600,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5649) 2048 1024 (by omega) (by omega) h10577 h10578,
        ← denote_pm_goal_3_10581_L18, ← denote_pm_goal_3_10582_L18]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 10753 / 10754
  rw [br_pm_10847, br_pm_10848,
      br_pm_10787, br_pm_10785, br_pm_10779, br_pm_10775, br_pm_16480,
      br_pm_10843, br_pm_10833, br_pm_10827, br_pm_10825,
      br_pm_10803, br_pm_10793, br_pm_10789, br_pm_16484,
      br_pm_10821, br_pm_10811, br_pm_10807, br_pm_16488,
      br_pm_10788, br_pm_10786, br_pm_10780, br_pm_10776, br_pm_16503,
      br_pm_10844, br_pm_10834, br_pm_10828, br_pm_10826,
      br_pm_10804, br_pm_10794, br_pm_10790, br_pm_16507,
      br_pm_10822, br_pm_10812, br_pm_10808, br_pm_16511]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5650
  rw [br_sm_5678, br_sm_5664, br_sm_5663, br_sm_5662,
      br_sm_5660, br_sm_8400,
      br_sm_5677, br_sm_5676, br_sm_5674, br_sm_5673,
      br_sm_5668, br_sm_5667, br_sm_5665, br_sm_8404,
      br_sm_5672, br_sm_5671, br_sm_5669, br_sm_8408,
      denote_sm_goal_3_5601_L18]
  rw [hRMS, hw5612, hw5617, hw5621, hw5626]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 10753 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 10754 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581_L18, rms_sh]; exact h10577
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582_L18, rms_sh]; exact h10578
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5661).shape = [1, 1024] := h_ss_pm 5661 [1, 1024] (by decide)
  have hw29 : (initPM 5666).shape = [512, 1024] := h_ss_pm 5666 [512, 1024] (by decide)
  have hw33 : (initPM 5670).shape = [512, 1024] := h_ss_pm 5670 [512, 1024] (by decide)
  have hw38 : (initPM 5675).shape = [1024, 512] := h_ss_pm 5675 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5661) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5666) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5670) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5661)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5661)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5666)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5666)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5670)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5670)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5661), fw_linear (fw_view [2048, 1024] B) (initPM 5661)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5661)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5661))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5666), fw_linear (fw_view [2048, 1024] B) (initPM 5666)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5670), fw_linear (fw_view [2048, 1024] B) (initPM 5670)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5661)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5661)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5675) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670))))) (initPM 5675)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))))) (initPM 5675)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670))))) (initPM 5675), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))))) (initPM 5675)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670))))) (initPM 5675)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))))) (initPM 5675))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5661))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5661))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5670))))) (initPM 5675)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5666))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5670))))) (initPM 5675)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10861_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024] := by
  have h10517 := hbase345
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10745).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573_L18, denote_pm_goal_3_10569_L18]; rfl
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10749).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577_L18]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10517 h10573
  have h10581sh : (denoteGraph_ringAttn pm_goal_3 initPM 10753).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581_L18, rms_sh]; exact h10577
  have h10601sh : (denoteGraph_ringAttn pm_goal_3 initPM 10773).shape = [2048, 1024] := by
    rw [br_pm_10773, br_pm_16476]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10581sh]; rfl) (by rw [h10581sh]; rfl)
  have h10615sh : (denoteGraph_ringAttn pm_goal_3 initPM 10787).shape = [2048, 1] := by
    rw [br_pm_10787, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10785]
    exact fw_view_shape_eq _ _
  have h10671sh : (denoteGraph_ringAttn pm_goal_3 initPM 10843).shape = [2048, 1024] := by
    rw [br_pm_10843]; exact fw_view_shape_eq _ _
  have h10675sh : (denoteGraph_ringAttn pm_goal_3 initPM 10847).shape = [2048, 1024] := by
    rw [br_pm_10847, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10615sh h10671sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10773) (denoteGraph_ringAttn pm_goal_3 initPM 10847)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10601sh h10675sh
  have h16379sh : (denoteGraph_ringAttn pm_goal_3 initPM 16457).shape = [2048, 1024] := by
    rw [br_pm_16457]; exact h10577
  have h10685sh : (denoteGraph_ringAttn pm_goal_3 initPM 10857).shape = [2048, 1024] := by
    rw [br_pm_10857, br_pm_10851]; exact hinnerA
  rw [br_pm_10861]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16379sh h10685sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10862_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024] := by
  have h10518 := hbase346
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10746).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574_L18, denote_pm_goal_3_10570_L18]; rfl
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10750).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578_L18]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10518 h10574
  have h10582sh : (denoteGraph_ringAttn pm_goal_3 initPM 10754).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582_L18, rms_sh]; exact h10578
  have h10602sh : (denoteGraph_ringAttn pm_goal_3 initPM 10774).shape = [2048, 1024] := by
    rw [br_pm_10774, br_pm_16499]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10582sh]; rfl) (by rw [h10582sh]; rfl)
  have h10616sh : (denoteGraph_ringAttn pm_goal_3 initPM 10788).shape = [2048, 1] := by
    rw [br_pm_10788, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10786]
    exact fw_view_shape_eq _ _
  have h10672sh : (denoteGraph_ringAttn pm_goal_3 initPM 10844).shape = [2048, 1024] := by
    rw [br_pm_10844]; exact fw_view_shape_eq _ _
  have h10676sh : (denoteGraph_ringAttn pm_goal_3 initPM 10848).shape = [2048, 1024] := by
    rw [br_pm_10848, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10616sh h10672sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10774) (denoteGraph_ringAttn pm_goal_3 initPM 10848)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10602sh h10676sh
  have h16387sh : (denoteGraph_ringAttn pm_goal_3 initPM 16465).shape = [2048, 1024] := by
    rw [br_pm_16465]; exact h10578
  have h10686sh : (denoteGraph_ringAttn pm_goal_3 initPM 10858).shape = [2048, 1024] := by
    rw [br_pm_10858, br_pm_10852]; exact hinnerB
  rw [br_pm_10862]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16387sh h10686sh
end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute_L18
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L18
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L18_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L18_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L18_hbound_witness
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L18_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10861_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_10862_shape
