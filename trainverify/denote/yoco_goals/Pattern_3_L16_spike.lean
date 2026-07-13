/-
  Pattern_3_L16_spike.lean — L16 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L16-specific TIDs.  The L16 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L16's Q path
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

/-! ## L16 attention node declarations + buddy proofs.
SM attn node index 644; PM r0 = 1347; PM r1 = 1348. -/

def nSM_16 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5538, 5539, 5540, 5541, 5542], outs := [5543],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_16 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10351, 5539, 5540, 5541, 5542], outs := [10375],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_16 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10352, 5539, 5540, 5541, 5542], outs := [10376],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_16 : ringAttnBuddies sm_goal_3 nSM_16 = [nSM_16] := by
  show (List.filter (fun m => decide (m.op = nSM_16.op) && decide (m.params = nSM_16.params) &&
      decide (m.ins.getD 3 0 = nSM_16.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_16.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_16]
  rw [show (List.filter (fun m => decide (m.op = nSM_16.op) && decide (m.params = nSM_16.params) &&
      decide (m.ins.getD 3 0 = nSM_16.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_16.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_16] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_16 : ringAttnBuddies pm_goal_3 nR0_16 = [nR0_16, nR1_16] := by
  show (List.filter (fun m => decide (m.op = nR0_16.op) && decide (m.params = nR0_16.params) &&
      decide (m.ins.getD 3 0 = nR0_16.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_16.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_16, nR1_16]
  rw [show (List.filter (fun m => decide (m.op = nR0_16.op) && decide (m.params = nR0_16.params) &&
      decide (m.ins.getD 3 0 = nR0_16.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_16.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_16, nR1_16] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_16 : ringAttnBuddies pm_goal_3 nR1_16 = [nR0_16, nR1_16] := by
  show (List.filter (fun m => decide (m.op = nR1_16.op) && decide (m.params = nR1_16.params) &&
      decide (m.ins.getD 3 0 = nR1_16.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_16.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_16, nR1_16]
  rw [show (List.filter (fun m => decide (m.op = nR1_16.op) && decide (m.params = nR1_16.params) &&
      decide (m.ins.getD 3 0 = nR1_16.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_16.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_16, nR1_16] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L16 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L16_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5543
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_16 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5543
      = (sm_goal_3.nodes.take 645).foldl (applyNodeRingAttn sm_goal_3) initSM 5543 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5543 645 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 645 = sm_goal_3.nodes.take 644 ++ [nSM_16] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5538 5539 5540 5541 5542 5543 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L16_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10375
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_16 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10375
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10375 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10375 1348 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1348 = pm_goal_3.nodes.take 1347 ++ [nR0_16] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10351 5539 5540 5541 5542 10375 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L16_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10376
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_16 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10376
      = (pm_goal_3.nodes.take 1349).foldl (applyNodeRingAttn pm_goal_3) initPM 10376 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10376 1349 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1349 = pm_goal_3.nodes.take 1348 ++ [nR1_16] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10352 5539 5540 5541 5542 10376 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L16) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5585 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5536 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5534) (initSM 5535) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5536 8295 5535 642
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8295, 5535], outs := [5536] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8295 5535 5536)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8295 5534 641
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5534], outs := [8295, 8299], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5534 8295 [8295, 8299] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5535 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5587 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5538 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5536) (initSM 5537) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5538 5536 5537 643
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5536, 5537], outs := [5538] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5536 5537 5538 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5537 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5593 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5544 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5543) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5544 5543 645
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5543], outs := [5544], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5543 5544 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5594 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5545 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5544) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5545 5544 646
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5544], outs := [5545], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5544 5545 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5596 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5547 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5545) (initSM 5546) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5547 5545 5546 647
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5545, 5546], outs := [5547] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5545 5546 5547)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5546 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5597 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5548 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5547) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5548 5547 648
    ({ rank := 0, op := "OpName.FW_view", ins := [5547], outs := [5548], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5547 5548)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5598 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5549 =
      denoteGraph_ringAttn sm_goal_3 initSM 5548 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5549 5548 649
    ({ rank := 0, op := "OpName.FW_float", ins := [5548], outs := [5549] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5548 5549 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5599 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5550 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5534)
        (denoteGraph_ringAttn sm_goal_3 initSM 5549) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8299 = denoteGraph_ringAttn sm_goal_3 initSM 5534 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8299 5534 641
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5534], outs := [8295, 8299], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5534 8299 [8295, 8299] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5550 8299 5549 650
    ({ rank := 0, op := "OpName.FW_add", ins := [8299, 5549], outs := [5550] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8299 5549 5550)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5601 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5552 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5550) (initSM 5551) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5552 8303 5551 652
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8303, 5551], outs := [5552] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8303 5551 5552)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8303 5550 651
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5550], outs := [8303, 8307], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5550 8303 [8303, 8307] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5551 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5602 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5553 =
      denoteGraph_ringAttn sm_goal_3 initSM 5552 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5553 8314 654
    ({ rank := 0, op := "OpName.FW_float", ins := [8314], outs := [5553] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8314 5553 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8314 5552 653
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5552 8314 [8314, 8318, 8322, 8326, 8330] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5604 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5555 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5553) (initSM 5554) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5555 5553 5554 658
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5553, 5554], outs := [5555] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5553 5554 5555 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5554 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5606 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5557 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5555) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5555).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5557 5555 662
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5555], outs := [5556, 5557, 5558], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5555 5556 5557 5558 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5588 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5539 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5539 8049 484
    ({ rank := 0, op := "OpName.FW_to", ins := [8049], outs := [5539] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8049 5539 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8049 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8049 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5589 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5540 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5540 8107 496
    ({ rank := 0, op := "OpName.FW_to", ins := [8107], outs := [5540] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8107 5540 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8107 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8107 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L16) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10521 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10349 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10345) (initPM 5535) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10349 16281 5535 1343
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16281, 5535], outs := [10349] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16281 5535 10349)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16281 10345 1341
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281, 16285], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10345 16281 [16281, 16285] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5535 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10523 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10351 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10349) (initPM 5537) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10351 10349 5537 1345
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10349, 5537], outs := [10351] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 10349 5537 10351 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5537 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10549 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10377 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10375) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10377 10375 1349
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10375], outs := [10377], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10375 10377 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10555 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10383 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10377) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10383 10377 1351
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10377], outs := [10383], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10377 10383 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10559 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10387 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10383) (initPM 5546) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10387 10383 5546 1353
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10383, 5546], outs := [10387] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10383 5546 10387)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5546 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10569 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10397 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10387) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10397 10387 1355
    ({ rank := 0, op := "OpName.FW_view", ins := [10387], outs := [10397], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10387 10397)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10573 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10401 =
      denoteGraph_ringAttn pm_goal_3 initPM 10397 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10401 10397 1357
    ({ rank := 0, op := "OpName.FW_float", ins := [10397], outs := [10401] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10397 10401 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10577 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10405 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10345)
        (denoteGraph_ringAttn pm_goal_3 initPM 10401) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16285 = denoteGraph_ringAttn pm_goal_3 initPM 10345 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16285 10345 1341
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281, 16285], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10345 16285 [16281, 16285] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10405 16285 10401 1359
    ({ rank := 0, op := "OpName.FW_add", ins := [16285, 10401], outs := [10405] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16285 10401 10405)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10581 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10409 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10405) (initPM 5551) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10409 16297 5551 1363
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16297, 5551], outs := [10409] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16297 5551 10409)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16297 10405 1361
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10405], outs := [16297, 16301], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10405 16297 [16297, 16301] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5551 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10583 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10411 =
      denoteGraph_ringAttn pm_goal_3 initPM 10409 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10411 16316 1367
    ({ rank := 0, op := "OpName.FW_float", ins := [16316], outs := [10411] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16316 10411 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16316 10409 1365
      ({ rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10409 16316 [16316, 16320, 16324, 16328, 16332] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10417 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10411) (initPM 5554) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10417 10411 5554 1375
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [10411, 5554], outs := [10417] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 10411 5554 10417 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5554 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10593 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10421 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10417) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10417).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10421 10417 1383
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10417], outs := [10419, 10421, 10423], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 10417 10419 10421 10423 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10522 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10350 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10346) (initPM 5535) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10350 16289 5535 1344
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16289, 5535], outs := [10350] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16289 5535 10350)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16289 10346 1342
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289, 16293], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10346 16289 [16289, 16293] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5535 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10524 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10352 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 10350) (initPM 5537) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10352 10350 5537 1346
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10350, 5537], outs := [10352] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 10350 5537 10352 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5537 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10550 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10378 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10376) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10378 10376 1350
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10376], outs := [10378], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10376 10378 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10556 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10384 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10378) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10384 10378 1352
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10378], outs := [10384], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10378 10384 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10560 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10388 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10384) (initPM 5546) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10388 10384 5546 1354
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10384, 5546], outs := [10388] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10384 5546 10388)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5546 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10570 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10398 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10388) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10398 10388 1356
    ({ rank := 1, op := "OpName.FW_view", ins := [10388], outs := [10398], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10388 10398)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10574 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10402 =
      denoteGraph_ringAttn pm_goal_3 initPM 10398 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10402 10398 1358
    ({ rank := 1, op := "OpName.FW_float", ins := [10398], outs := [10402] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10398 10402 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10578 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10406 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10346)
        (denoteGraph_ringAttn pm_goal_3 initPM 10402) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16293 = denoteGraph_ringAttn pm_goal_3 initPM 10346 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16293 10346 1342
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289, 16293], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10346 16293 [16289, 16293] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10406 16293 10402 1360
    ({ rank := 1, op := "OpName.FW_add", ins := [16293, 10402], outs := [10406] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16293 10402 10406)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10582 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10410 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10406) (initPM 5551) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10410 16305 5551 1364
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16305, 5551], outs := [10410] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16305 5551 10410)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16305 10406 1362
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10406], outs := [16305, 16309], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10406 16305 [16305, 16309] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5551 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10584 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10412 =
      denoteGraph_ringAttn pm_goal_3 initPM 10410 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10412 16339 1371
    ({ rank := 1, op := "OpName.FW_float", ins := [16339], outs := [10412] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16339 10412 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16339 10410 1366
      ({ rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10410 16339 [16339, 16343, 16347, 16351, 16355] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10590 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10418 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 10412) (initPM 5554) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10418 10412 5554 1379
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [10412, 5554], outs := [10418] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 10412 5554 10418 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5554 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_10594 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10422 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10418) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 10418).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10422 10418 1387
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10418], outs := [10420, 10422, 10424], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 10418 10420 10422 10424 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5588 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5539 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5539 15831 1035
    ({ rank := 1, op := "OpName.FW_to", ins := [15831], outs := [5539] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15831 5539 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15831 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15831 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5589 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5540 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5540 15937 1059
    ({ rank := 1, op := "OpName.FW_to", ins := [15937], outs := [5540] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15937 5540 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15937 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15937 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L16 commute theorems -/

-- Q sharding commute: SM 5538 = allGather0[PM 10351, PM 10352].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024])
    (hw5586 : (initPM 5537).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5538 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10351,
         denoteGraph_ringAttn pm_goal_3 initPM 10352] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5584 : initSM 5535 = initPM 5535 := hb initGoal_5535 (by decide) rfl
  have hw5586e : initSM 5537 = initPM 5537 := hb initGoal_5537 (by decide) rfl
  rw [denote_sm_goal_3_5587, denote_sm_goal_3_5585,
      denote_pm_goal_3_10523, denote_pm_goal_3_10521,
      denote_pm_goal_3_10524, denote_pm_goal_3_10522]
  rw [hcarry5583, hw5584, hw5586e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10345) (initPM 5535)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10517
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10346) (initPM 5535)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10518
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5535) 2048 1024 (by omega) (by omega) h10517 h10518,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5537) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5586]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5588_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5539).shape = [4096, 4, 64] := by
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
    (denoteGraph_ringAttn pm_goal_3 initPM 5540).shape = [4096, 4, 64] := by
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

-- K/V replication (cross-graph, full tensor): SM 5539 = PM 5539, SM 5540 = PM 5540.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5539 =
      denoteGraph_ringAttn pm_goal_3 initPM 5539 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5588, denote_pm_goal_3_5588, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5540 =
      denoteGraph_ringAttn pm_goal_3 initPM 5540 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5589, denote_pm_goal_3_5589, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L16 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L16_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5543 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10375,
         denoteGraph_ringAttn pm_goal_3 initPM 10376] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5586 : (initPM 5537).shape = [16, 64, 1024] := hPM 5537 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L16_commute initSM initPM hInit hcarry5583 h10517 h10518 hw5586
  have hK := sm_pm_krepl_L16_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L16_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5588_shape initPM hPM
  have hVsh := pm_5589_shape initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10349).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10350).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523 : (denoteGraph_ringAttn pm_goal_3 initPM 10351).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524 : (denoteGraph_ringAttn pm_goal_3 initPM 10352).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5538).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5538).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5539).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5540).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 644)
  have bSM5587 : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5538 = denoteGraph_ringAttn sm_goal_3 initSM 5538 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5538 644 (by decide) (by decide)).symm
  have bSM5588 : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5539 = denoteGraph_ringAttn sm_goal_3 initSM 5539 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5539 644 (by decide) (by decide)).symm
  have bSM5589 : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5540 = denoteGraph_ringAttn sm_goal_3 initSM 5540 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5540 644 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1347)
  have bPM10523 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10351 = denoteGraph_ringAttn pm_goal_3 initPM 10351 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10351 1347 (by decide) (by decide)).symm
  have bPM10524 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10352 = denoteGraph_ringAttn pm_goal_3 initPM 10352 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10352 1347 (by decide) (by decide)).symm
  have bPM5588 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5539 = denoteGraph_ringAttn pm_goal_3 initPM 5539 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5539 1347 (by decide) (by decide)).symm
  have bPM5589 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5540 = denoteGraph_ringAttn pm_goal_3 initPM 5540 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5540 1347 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5590 : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5541 = initSM 5541 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 644) initSM 5541 (by decide) (by decide)
  have hS5591 : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5542 = initSM 5542 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 644) initSM 5542 (by decide) (by decide)
  have hP5590 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5541 = initPM 5541 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1347) initPM 5541 (by decide) (by decide)
  have hP5591 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5542 = initPM 5542 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1347) initPM 5542 (by decide) (by decide)
  have hw5590 : initSM 5541 = initPM 5541 := hb initGoal_5541 (by decide) rfl
  have hw5591 : initSM 5542 = initPM 5542 := hb initGoal_5542 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5538).shape.length
    rw [bSM5587]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5539).shape.length
    rw [bSM5588]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5540).shape.length
    rw [bSM5589]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
        (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5538 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10351,
        (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10352]
    rw [bSM5587, bPM10523, bPM10524]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5539 =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5539
    rw [bSM5588, bPM5588]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5540 =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5540
    rw [bSM5589, bPM5589]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5539).shape = [4096, 4, 64]
    rw [bPM5588]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5540).shape = [4096, 4, 64]
    rw [bPM5589]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5542)).getD (t+1) 0 ≤ 4096
    rw [hP5591]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5541 =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5541
    rw [hS5590, hP5590, hw5590]
  have hcuK : (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_16.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM 5542 =
      (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5542
    rw [hS5591, hP5591, hw5591]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
       (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10351,
       (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10352]).shape = [4096, 16, 64]
    rw [bPM10523, bPM10524]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
          (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 1 0),
          (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 2 0),
          (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 4 0))
        (nR0_16.params.getD 0 1) (nR0_16.params.getD 1 1) (nR0_16.params.getD 2 1) (nR0_16.params.getD 3 1)
        (decide (nR0_16.params.getD 4 0 ≠ 0)) (nR0_16.params.getD 5 0)).shape
        = [2 * 2048, nR0_16.params.getD 0 1, nR0_16.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1347 -> take 1348)
  have e10523 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10351
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10351 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10351 1347 1348 (by omega) (by decide) (by decide)).symm
  have e10524 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10352
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10352 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10352 1347 1348 (by omega) (by decide) (by decide)).symm
  have e5588 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5539
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 5539 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5539 1347 1348 (by omega) (by decide) (by decide)).symm
  have e5589 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5540
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 5540 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5540 1347 1348 (by omega) (by decide) (by decide)).symm
  have e5590 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5541
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 5541 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5541 1347 1348 (by omega) (by decide) (by decide)).symm
  have e5591 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 5542
      = (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 5542 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5542 1347 1348 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_16
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_16 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_16]; intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [buddy_r1_16]; intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [buddy_r1_16]; intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 644).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_16 nR0_16 nR1_16 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_16 buddy_r0_16 buddy_r1_16 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L16_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L16_r0_bridge, ← denote_pm_attn_L16_r1_bridge]


/-! ## L16 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5543 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10375,
         denoteGraph_ringAttn pm_goal_3 initPM 10376])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10375).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10376).shape = [2048, 16, 64])
    (hw5595 : (initPM 5546).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5549 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10401,
         denoteGraph_ringAttn pm_goal_3 initPM 10402] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5546 = initPM 5546 := hb initGoal_5546 (by decide) rfl
  rw [denote_sm_goal_3_5598, denote_sm_goal_3_5597, denote_sm_goal_3_5596,
      denote_sm_goal_3_5594, denote_sm_goal_3_5593,
      denote_pm_goal_3_10573, denote_pm_goal_3_10569, denote_pm_goal_3_10559,
      denote_pm_goal_3_10555, denote_pm_goal_3_10549,
      denote_pm_goal_3_10574, denote_pm_goal_3_10570, denote_pm_goal_3_10560,
      denote_pm_goal_3_10556, denote_pm_goal_3_10550]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h10547 h10548]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10375))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10376))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5546) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5595]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10375))) (initPM 5546)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5595]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10376))) (initPM 5546)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5595]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10375))) (initPM 5546),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10376))) (initPM 5546)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5599_commute (initSM initPM : Store)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5549 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10401,
         denoteGraph_ringAttn pm_goal_3 initPM 10402])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024])
    (h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10401).shape = [2048, 1024])
    (h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10402).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5550 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10405,
         denoteGraph_ringAttn pm_goal_3 initPM 10406] := by
  rw [denote_sm_goal_3_5599, denote_pm_goal_3_10577, denote_pm_goal_3_10578]
  rw [hcarry5583, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h10517 h10518 h10573 h10574]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5550 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10405,
         denoteGraph_ringAttn pm_goal_3 initPM 10406])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5555 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10417,
         denoteGraph_ringAttn pm_goal_3 initPM 10418] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5600 : initSM 5551 = initPM 5551 := hb initGoal_5551 (by decide) rfl
  have hw5603 : initSM 5554 = initPM 5554 := hb initGoal_5554 (by decide) rfl
  have hw5603sh : (initPM 5554).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5554 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5554] using hsh
  rw [denote_sm_goal_3_5604, denote_sm_goal_3_5602, denote_sm_goal_3_5601,
      denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581,
      denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
  rw [hw5600, hw5603, hcarry5599]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5551) 2048 1024 (by omega) (by omega) h10577 h10578]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10405) (initPM 5551)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10577
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 10406) (initPM 5551)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h10578
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5554) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5603sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L16 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5599 : denoteGraph_ringAttn sm_goal_3 initSM 5550 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10405,
         denoteGraph_ringAttn pm_goal_3 initPM 10406])
    (h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024])
    (h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5557 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10421,
         denoteGraph_ringAttn pm_goal_3 initPM 10422] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5603sh : (initPM 5554).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5554 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5554] using hsh
  have hnl := sm_pm_nl_L16_commute initSM initPM hInit hcarry5599 h10577 h10578
  have hs10589 : (denoteGraph_ringAttn pm_goal_3 initPM 10417).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581]
    exact nl_sh 2048 1024 64 _ (initPM 5554) (by rw [rms_sh]; exact h10577) hw5603sh
  have hs10590 : (denoteGraph_ringAttn pm_goal_3 initPM 10418).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
    exact nl_sh 2048 1024 64 _ (initPM 5554) (by rw [rms_sh]; exact h10578) hw5603sh
  have hSM5604sh : (denoteGraph_ringAttn sm_goal_3 initSM 5555).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs10589
  rw [denote_sm_goal_3_5606, denote_pm_goal_3_10593, denote_pm_goal_3_10594]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5555).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5604sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10417).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10589]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 10418).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs10590]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs10589 hs10590


/-! ## L16 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L16_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5543 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10375,
         denoteGraph_ringAttn pm_goal_3 initPM 10376])
    (h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10375).shape = [2048, 16, 64])
    (h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10376).shape = [2048, 16, 64])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024])
    (hw5595 : (initPM 5546).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5557 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10421,
         denoteGraph_ringAttn pm_goal_3 initPM 10422] := by
  have hreshape := sm_pm_reshape_float_L16_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10401).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573, denote_pm_goal_3_10569]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10402).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574, denote_pm_goal_3_10570]; rfl
  have hcarry5599 := sm_pm_carry_5599_commute initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10577 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10578 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  exact sm_pm_router_commute_L16 initSM initPM hInit hcarry5599 h10577 h10578

/-! ## L16 router — fully assembled

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
theorem sm_pm_router_commute_L16_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5557 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10421,
         denoteGraph_ringAttn pm_goal_3 initPM 10422] := by
  have hattn := sm_pm_attention_L16_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5537).shape = [16, 64, 1024] := hPM 5537 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5546).shape = [1024, 1024] := hPM 5546 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10349).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10350).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10351).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10352).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10351
      = denoteGraph_ringAttn pm_goal_3 initPM 10351 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10351 1347 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10352
      = denoteGraph_ringAttn pm_goal_3 initPM 10352 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10352 1347 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10351
      = denoteGraph_ringAttn pm_goal_3 initPM 10351 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10351 1348 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10352
      = denoteGraph_ringAttn pm_goal_3 initPM 10352 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10352 1348 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10375).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L16_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_16 nR0_16 nR1_16 0 buddy_r0_16 (by decide)]
    have e0 : nR0_16.ins.getD 0 0 = 10351 := by decide
    have e1 : nR1_16.ins.getD 0 0 = 10352 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
         (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10376).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L16_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_16 nR0_16 nR1_16 1 buddy_r1_16 (by decide)]
    have e0 : nR0_16.ins.getD 0 0 = 10351 := by decide
    have e1 : nR1_16.ins.getD 0 0 = 10352 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
         (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L16_from_attention initSM initPM hInit hcarry5583
    hattn h10547 h10548 h10517 h10518 hw5595

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L16_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _


-- ================= L16 MoE carry (sm_pm_carry_5583_commute) =================
theorem br_pm_16285 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16285 = denoteGraph_ringAttn pm_goal_3 initPM 10345 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16285 10345 1341
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281, 16285], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 10345 16285 [16281, 16285] 2 (by decide) (by decide))
    rfl

theorem br_pm_16293 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16293 = denoteGraph_ringAttn pm_goal_3 initPM 10346 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16293 10346 1342
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289, 16293], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 10346 16293 [16289, 16293] 2 (by decide) (by decide))
    rfl

-- ===== ported bridges =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10419 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10419 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10417) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10417).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10419 10417 1383
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [10417], outs := [10419, 10421, 10423], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 10417 10419 10421 10423 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10420 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10420 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10418) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 10418).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10420 10418 1387
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [10418], outs := [10420, 10422, 10424], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 10418 10420 10422 10424 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10429 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10429 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16320)
        (denoteGraph_ringAttn pm_goal_3 initPM 10419)
        (denoteGraph_ringAttn pm_goal_3 initPM 10421)
        [initPM 10425, initPM 10426] [initPM 10427, initPM 10428]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10429 16320 10419 10421 10425 10426 10427 10428 1391
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16320, 10419, 10421, 10425, 10426, 10427, 10428], outs := [10429], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16320 10419 10421 10425 10426 10427 10428 10429 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10425 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10426 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10427 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10428 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10430 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10430 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16343)
        (denoteGraph_ringAttn pm_goal_3 initPM 10420)
        (denoteGraph_ringAttn pm_goal_3 initPM 10422)
        [initPM 10425, initPM 10426] [initPM 10427, initPM 10428]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 10430 16343 10420 10422 10425 10426 10427 10428 1394
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16343, 10420, 10422, 10425, 10426, 10427, 10428], outs := [10430], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16343 10420 10422 10425 10426 10427 10428 10430 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10425 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10426 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10427 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 10428 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10431 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10431 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16324) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10431 16324 1368
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16324], outs := [10431], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16324 10431 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10432 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10432 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16347) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10432 16347 1372
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16347], outs := [10432], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16347 10432 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10435 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10435 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10431) (initPM 5563) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10435 10431 5563 1376
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10431, 5563], outs := [10435] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10431 5563 10435)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5563 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10436 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10436 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10432) (initPM 5563) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10436 10432 5563 1380
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10432, 5563], outs := [10436] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10432 5563 10436)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5563 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10441 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10441 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10435) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10441 10435 1384
    ({ rank := 0, op := "OpName.FW_view", ins := [10435], outs := [10441], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 10435 10441)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10442 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10442 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 10436) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10442 10436 1388
    ({ rank := 1, op := "OpName.FW_view", ins := [10436], outs := [10442], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 10436 10442)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10443 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10443 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10441) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10443 10441 1392
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [10441], outs := [10443] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 10441 10443])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10444 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10444 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 10442) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10444 10442 1395
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [10442], outs := [10444] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 10442 10444])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10445 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10445 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16328) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10445 16328 1369
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16328], outs := [10445], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16328 10445 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10446 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10446 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16351) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10446 16351 1373
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16351], outs := [10446], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16351 10446 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10449 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10449 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10445) (initPM 5568) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10449 10445 5568 1377
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10445, 5568], outs := [10449] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10445 5568 10449)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5568 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10450 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10450 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10446) (initPM 5568) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10450 10446 5568 1381
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10446, 5568], outs := [10450] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10446 5568 10450)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5568 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10459 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10459 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10449) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10459 10449 1385
    ({ rank := 0, op := "OpName.FW_view", ins := [10449], outs := [10459], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10449 10459)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10460 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10460 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10450) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10460 10450 1389
    ({ rank := 1, op := "OpName.FW_view", ins := [10450], outs := [10460], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10450 10460)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10463 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10463 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16332) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10463 16332 1370
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16332], outs := [10463], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16332 10463 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10464 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10464 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16355) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10464 16355 1374
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16355], outs := [10464], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16355 10464 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10467 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10467 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10463) (initPM 5572) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10467 10463 5572 1378
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10463, 5572], outs := [10467] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10463 5572 10467)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5572 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10468 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10468 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10464) (initPM 5572) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10468 10464 5572 1382
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10464, 5572], outs := [10468] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10464 5572 10468)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5572 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10477 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10477 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10467) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10477 10467 1386
    ({ rank := 0, op := "OpName.FW_view", ins := [10467], outs := [10477], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 10467 10477)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10478 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10478 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10468) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10478 10468 1390
    ({ rank := 1, op := "OpName.FW_view", ins := [10468], outs := [10478], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 10468 10478)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10481 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10481 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10459) (denoteGraph_ringAttn pm_goal_3 initPM 10477) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10481 10459 10477 1393
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [10459, 10477], outs := [10481] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 10459 10477 10481])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10482 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10482 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 10460) (denoteGraph_ringAttn pm_goal_3 initPM 10478) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10482 10460 10478 1396
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [10460, 10478], outs := [10482] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 10460 10478 10482])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10483 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10483 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10481) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10483 10481 1397
    ({ rank := 0, op := "OpName.FW_reshape", ins := [10481], outs := [10483], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 10481 10483 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10484 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10484 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 10482) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10484 10482 1398
    ({ rank := 1, op := "OpName.FW_reshape", ins := [10482], outs := [10484], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 10482 10484 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10489 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10489 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10483) (initPM 5577) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10489 10483 5577 1399
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10483, 5577], outs := [10489] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 10483 5577 10489)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5577 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10490 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10490 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 10484) (initPM 5577) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10490 10484 5577 1400
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10484, 5577], outs := [10490] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 10484 5577 10490)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5577 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10499 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10499 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10489) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10499 10489 1401
    ({ rank := 0, op := "OpName.FW_view", ins := [10489], outs := [10499], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 10489 10499)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10500 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10500 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 10490) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10500 10490 1402
    ({ rank := 1, op := "OpName.FW_view", ins := [10490], outs := [10500], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 10490 10500)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10503 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10503 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10443) (denoteGraph_ringAttn pm_goal_3 initPM 10499) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10503 10443 10499 1403
    ({ rank := 0, op := "OpName.FW_mul", ins := [10443, 10499], outs := [10503] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 10443 10499 10503])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10504 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10504 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 10444) (denoteGraph_ringAttn pm_goal_3 initPM 10500) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10504 10444 10500 1404
    ({ rank := 1, op := "OpName.FW_mul", ins := [10444, 10500], outs := [10504] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 10444 10500 10504])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10507 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10507 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10429) (denoteGraph_ringAttn pm_goal_3 initPM 10503) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10507 10429 10503 1405
    ({ rank := 0, op := "OpName.FW_add", ins := [10429, 10503], outs := [10507] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 10429 10503 10507)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10508 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10508 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10430) (denoteGraph_ringAttn pm_goal_3 initPM 10504) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10508 10430 10504 1406
    ({ rank := 1, op := "OpName.FW_add", ins := [10430, 10504], outs := [10508] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 10430 10504 10508)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10513 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10513 =
      denoteGraph_ringAttn pm_goal_3 initPM 10507 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10513 10507 1407
    ({ rank := 0, op := "OpName.FW_float", ins := [10507], outs := [10513] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 10507 10513 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10514 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10514 =
      denoteGraph_ringAttn pm_goal_3 initPM 10508 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 10514 10508 1408
    ({ rank := 1, op := "OpName.FW_float", ins := [10508], outs := [10514] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 10508 10514 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10517 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10517 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16301) (denoteGraph_ringAttn pm_goal_3 initPM 10513) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10517 16301 10513 1409
    ({ rank := 0, op := "OpName.FW_add", ins := [16301, 10513], outs := [10517] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16301 10513 10517)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_10518 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10518 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 16309) (denoteGraph_ringAttn pm_goal_3 initPM 10514) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 10518 16309 10514 1410
    ({ rank := 1, op := "OpName.FW_add", ins := [16309, 10514], outs := [10518] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16309 10514 10518)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16301 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16301 =
      denoteGraph_ringAttn pm_goal_3 initPM 10405 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16301 10405 1361
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10405], outs := [16297, 16301], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 10405 16297 16301 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16309 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16309 =
      denoteGraph_ringAttn pm_goal_3 initPM 10406 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16309 10406 1362
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10406], outs := [16305, 16309], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 10406 16305 16309 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16320 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16320 =
      denoteGraph_ringAttn pm_goal_3 initPM 10409 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16320 10409 1365
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 10409 16316 16320 16324 16328 16332 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16324 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16324 =
      denoteGraph_ringAttn pm_goal_3 initPM 10409 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16324 10409 1365
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 10409 16316 16320 16324 16328 16332 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16328 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16328 =
      denoteGraph_ringAttn pm_goal_3 initPM 10409 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16328 10409 1365
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 10409 16316 16320 16324 16328 16332 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16332 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16332 =
      denoteGraph_ringAttn pm_goal_3 initPM 10409 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16332 10409 1365
    ({ rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 10409 16316 16320 16324 16328 16332 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16343 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16343 =
      denoteGraph_ringAttn pm_goal_3 initPM 10410 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16343 10410 1366
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 10410 16339 16343 16347 16351 16355 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16347 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16347 =
      denoteGraph_ringAttn pm_goal_3 initPM 10410 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16347 10410 1366
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 10410 16339 16343 16347 16351 16355 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16351 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16351 =
      denoteGraph_ringAttn pm_goal_3 initPM 10410 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16351 10410 1366
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 10410 16339 16343 16347 16351 16355 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_pm_16355 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16355 =
      denoteGraph_ringAttn pm_goal_3 initPM 10410 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16355 10410 1366
    ({ rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 10410 16339 16343 16347 16351 16355 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5556 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5556 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5555) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5555).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5556 5555 662
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5555], outs := [5556, 5557, 5558], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5555 5556 5557 5558 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5561 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5561 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8318)
        (denoteGraph_ringAttn sm_goal_3 initSM 5556)
        (denoteGraph_ringAttn sm_goal_3 initSM 5557)
        (initSM 5559) (initSM 5560) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5561 8318 5556 5557 5559 5560 666
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8318, 5556, 5557, 5559, 5560], outs := [5561], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8318 5556 5557 5559 5560 5561 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5559 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5560 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5562 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5562 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8322) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5562 8322 655
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8322], outs := [5562], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8322 5562 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5564 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5564 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5562) (initSM 5563) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5564 5562 5563 659
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5562, 5563], outs := [5564] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5562 5563 5564)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5563 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5565 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5565 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5564) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5565 5564 663
    ({ rank := 0, op := "OpName.FW_view", ins := [5564], outs := [5565], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5564 5565)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5566 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5566 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5565) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5566 5565 667
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5565], outs := [5566] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5565 5566])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5567 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5567 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8326) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5567 8326 656
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8326], outs := [5567], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8326 5567 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5569 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5569 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5567) (initSM 5568) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5569 5567 5568 660
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5567, 5568], outs := [5569] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5567 5568 5569)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5568 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5570 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5570 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5569) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5570 5569 664
    ({ rank := 0, op := "OpName.FW_view", ins := [5569], outs := [5570], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5569 5570)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5571 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5571 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8330) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5571 8330 657
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8330], outs := [5571], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8330 5571 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5573 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5573 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5571) (initSM 5572) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5573 5571 5572 661
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5571, 5572], outs := [5573] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5571 5572 5573)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5572 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5574 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5574 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5573) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5574 5573 665
    ({ rank := 0, op := "OpName.FW_view", ins := [5573], outs := [5574], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5573 5574)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5575 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5575 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5570) (denoteGraph_ringAttn sm_goal_3 initSM 5574) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5575 5570 5574 668
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5570, 5574], outs := [5575] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5570 5574 5575])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5576 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5576 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5575) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5576 5575 669
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5575], outs := [5576], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5575 5576 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5578 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5578 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5576) (initSM 5577) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5578 5576 5577 670
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5576, 5577], outs := [5578] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5576 5577 5578)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5577 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5579 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5579 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5578) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5579 5578 671
    ({ rank := 0, op := "OpName.FW_view", ins := [5578], outs := [5579], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5578 5579)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5580 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5580 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5566) (denoteGraph_ringAttn sm_goal_3 initSM 5579) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5580 5566 5579 672
    ({ rank := 0, op := "OpName.FW_mul", ins := [5566, 5579], outs := [5580] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5566 5579 5580])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5581 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5581 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5561) (denoteGraph_ringAttn sm_goal_3 initSM 5580) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5581 5561 5580 673
    ({ rank := 0, op := "OpName.FW_add", ins := [5561, 5580], outs := [5581] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5561 5580 5581)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5582 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5582 =
      denoteGraph_ringAttn sm_goal_3 initSM 5581 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5582 5581 674
    ({ rank := 0, op := "OpName.FW_float", ins := [5581], outs := [5582] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5581 5582 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_5583 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8307) (denoteGraph_ringAttn sm_goal_3 initSM 5582) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5583 8307 5582 675
    ({ rank := 0, op := "OpName.FW_add", ins := [8307, 5582], outs := [5583] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8307 5582 5583)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8307 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8307 =
      denoteGraph_ringAttn sm_goal_3 initSM 5550 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8307 5550 651
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5550], outs := [8303, 8307], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5550 8303 8307 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8318 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8318 =
      denoteGraph_ringAttn sm_goal_3 initSM 5552 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8318 5552 653
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5552 8314 8318 8322 8326 8330 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8322 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8322 =
      denoteGraph_ringAttn sm_goal_3 initSM 5552 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8322 5552 653
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5552 8314 8318 8322 8326 8330 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8326 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8326 =
      denoteGraph_ringAttn sm_goal_3 initSM 5552 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8326 5552 653
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5552 8314 8318 8322 8326 8330 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem br_sm_8330 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8330 =
      denoteGraph_ringAttn sm_goal_3 initSM 5552 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8330 5552 653
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5552 8314 8318 8322 8326 8330 (by decide) (by decide) (by decide) (by decide))
    rfl







-- ===== moe_gmm =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5550 : denoteGraph_ringAttn sm_goal_3 initSM 5550 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10405,
         denoteGraph_ringAttn pm_goal_3 initPM 10406])
    (h10405 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024])
    (h10406 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5561 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10429,
         denoteGraph_ringAttn pm_goal_3 initPM 10430] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5551 : initSM 5551 = initPM 5551 := hb initGoal_5551 (by decide) rfl
  have hw5554sh : (initPM 5554).shape = [64, 1024] := by
    have hgh := hII initGoal_5554 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5554] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5559 : initSM 5559 = allGatherPrimDimN 0 2 0 [initPM 10425, initPM 10426] := by
    have hg := hII initGoal_5559 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5559, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10425) (initPM 10426) []
        (by rw [h_ss_pm 10425 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5560 : initSM 5560 = allGatherPrimDimN 0 2 0 [initPM 10427, initPM 10428] := by
    have hg := hII initGoal_5560 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5560, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 10427) (initPM 10428) []
        (by rw [h_ss_pm 10427 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L16_commute initSM initPM hInit hcarry5550 h10405 h10406
  have hrouter := sm_pm_router_commute_L16 initSM initPM hInit hcarry5550 h10405 h10406
  -- PM rms output shapes [2048, 1024]
  have h10409sh : (denoteGraph_ringAttn pm_goal_3 initPM 10409).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581, rms_sh]; exact h10405
  have h10410sh : (denoteGraph_ringAttn pm_goal_3 initPM 10410).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582, rms_sh]; exact h10406
  -- PM nl output shapes [2048, 64]
  have h10417sh : (denoteGraph_ringAttn pm_goal_3 initPM 10417).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10589, denote_pm_goal_3_10583, denote_pm_goal_3_10581]
    exact nl_sh 2048 1024 64 _ (initPM 5554) (by rw [rms_sh]; exact h10405) hw5554sh
  have h10418sh : (denoteGraph_ringAttn pm_goal_3 initPM 10418).shape = [2048, 64] := by
    rw [denote_pm_goal_3_10590, denote_pm_goal_3_10584, denote_pm_goal_3_10582]
    exact nl_sh 2048 1024 64 _ (initPM 5554) (by rw [rms_sh]; exact h10406) hw5554sh
  have hSM5555sh : (denoteGraph_ringAttn sm_goal_3 initSM 5555).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h10417sh
  -- MoE weight shapes
  have hw10425 : (initPM 10425).shape = [32,1024,1024] := h_ss_pm 10425 [32,1024,1024] (by decide)
  have hw10426 : (initPM 10426).shape = [32,1024,1024] := h_ss_pm 10426 [32,1024,1024] (by decide)
  have hw10427 : (initPM 10427).shape = [32,1024,512] := h_ss_pm 10427 [32,1024,512] (by decide)
  have hw10428 : (initPM 10428).shape = [32,1024,512] := h_ss_pm 10428 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h10419canon : denoteGraph_ringAttn pm_goal_3 initPM 10419
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10417) 8 64).fst := by
    rw [br_pm_10419,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10417).shape.reverse.head?).getD 1 = 64 from by rw [h10417sh]; rfl]
  have h10420canon : denoteGraph_ringAttn pm_goal_3 initPM 10420
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10418) 8 64).fst := by
    rw [br_pm_10420,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10418).shape.reverse.head?).getD 1 = 64 from by rw [h10418sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h10419sh : (denoteGraph_ringAttn pm_goal_3 initPM 10419).shape = [2048, 64] := by
    rw [h10419canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10417sh]; rfl)
  have h10420sh : (denoteGraph_ringAttn pm_goal_3 initPM 10420).shape = [2048, 64] := by
    rw [h10420canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h10418sh]; rfl)
  have h10421canon : denoteGraph_ringAttn pm_goal_3 initPM 10421
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10417) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10593,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10417).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10417sh]; rfl]
  have h10422canon : denoteGraph_ringAttn pm_goal_3 initPM 10422
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 10418) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_10594,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 10418).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h10418sh]; rfl]
  have h10421sh : (denoteGraph_ringAttn pm_goal_3 initPM 10421).shape = [2048, 64] := by
    rw [h10421canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10417sh
  have h10422sh : (denoteGraph_ringAttn pm_goal_3 initPM 10422).shape = [2048, 64] := by
    rw [h10422canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h10418sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 10409) (denoteGraph_ringAttn pm_goal_3 initPM 10410)
    (denoteGraph_ringAttn pm_goal_3 initPM 10419) (denoteGraph_ringAttn pm_goal_3 initPM 10420)
    (denoteGraph_ringAttn pm_goal_3 initPM 10421) (denoteGraph_ringAttn pm_goal_3 initPM 10422)
    (initPM 10425) (initPM 10426) (initPM 10427) (initPM 10428)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h10409sh h10410sh h10419sh h10420sh h10421sh h10422sh hw10425 hw10426 hw10427 hw10428
  -- Rewrite RHS via denote unfolds + key
  rw [br_pm_10429, br_pm_10430, br_pm_16320, br_pm_16343,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [br_sm_5561, br_sm_8318, denote_sm_goal_3_5601, br_sm_5556]
  rw [hrouter, h5559, h5560]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5555).shape.reverse.head?).getD 1 = 64 from by rw [hSM5555sh]; rfl]
  rw [hw5551, hcarry5550, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5551) 2048 1024 (by omega) (by omega) h10405 h10406]
  rw [← denote_pm_goal_3_10581, ← denote_pm_goal_3_10582]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h10417sh h10418sh]
  rw [← h10419canon, ← h10420canon]
  unfold fw_all2all_moe_gmm_full
  rfl



-- ===== gate_mul =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L16_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5550 : denoteGraph_ringAttn sm_goal_3 initSM 5550 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10405,
         denoteGraph_ringAttn pm_goal_3 initPM 10406])
    (h10405 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024])
    (h10406 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5580
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10503,
           denoteGraph_ringAttn pm_goal_3 initPM 10504] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5551 : initSM 5551 = initPM 5551 := hb initGoal_5551 (by decide) rfl
  have hw5563 : initSM 5563 = initPM 5563 := hb initGoal_5563 (by decide) rfl
  have hw5568 : initSM 5568 = initPM 5568 := hb initGoal_5568 (by decide) rfl
  have hw5572 : initSM 5572 = initPM 5572 := hb initGoal_5572 (by decide) rfl
  have hw5577 : initSM 5577 = initPM 5577 := hb initGoal_5577 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5550) (initSM 5551)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 10409,
           denoteGraph_ringAttn pm_goal_3 initPM 10410] := by
    rw [hcarry5550, hw5551,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5551) 2048 1024 (by omega) (by omega) h10405 h10406,
        ← denote_pm_goal_3_10581, ← denote_pm_goal_3_10582]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 10409 / 10410
  rw [br_pm_10503, br_pm_10504,
      br_pm_10443, br_pm_10441, br_pm_10435, br_pm_10431, br_pm_16324,
      br_pm_10499, br_pm_10489, br_pm_10483, br_pm_10481,
      br_pm_10459, br_pm_10449, br_pm_10445, br_pm_16328,
      br_pm_10477, br_pm_10467, br_pm_10463, br_pm_16332,
      br_pm_10444, br_pm_10442, br_pm_10436, br_pm_10432, br_pm_16347,
      br_pm_10500, br_pm_10490, br_pm_10484, br_pm_10482,
      br_pm_10460, br_pm_10450, br_pm_10446, br_pm_16351,
      br_pm_10478, br_pm_10468, br_pm_10464, br_pm_16355]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5552
  rw [br_sm_5580, br_sm_5566, br_sm_5565, br_sm_5564,
      br_sm_5562, br_sm_8322,
      br_sm_5579, br_sm_5578, br_sm_5576, br_sm_5575,
      br_sm_5570, br_sm_5569, br_sm_5567, br_sm_8326,
      br_sm_5574, br_sm_5573, br_sm_5571, br_sm_8330,
      denote_sm_goal_3_5601]
  rw [hRMS, hw5563, hw5568, hw5572, hw5577]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 10409 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 10410 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_10581, rms_sh]; exact h10405
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_10582, rms_sh]; exact h10406
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5563).shape = [1, 1024] := h_ss_pm 5563 [1, 1024] (by decide)
  have hw29 : (initPM 5568).shape = [512, 1024] := h_ss_pm 5568 [512, 1024] (by decide)
  have hw33 : (initPM 5572).shape = [512, 1024] := h_ss_pm 5572 [512, 1024] (by decide)
  have hw38 : (initPM 5577).shape = [1024, 512] := h_ss_pm 5577 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5563) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5568) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5572) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5563)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5563)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5568)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5568)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5572)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5572)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5563), fw_linear (fw_view [2048, 1024] B) (initPM 5563)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5563)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5563))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5568), fw_linear (fw_view [2048, 1024] B) (initPM 5568)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5572), fw_linear (fw_view [2048, 1024] B) (initPM 5572)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5563)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5563)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5577) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572))))) (initPM 5577)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))))) (initPM 5577)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572))))) (initPM 5577), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))))) (initPM 5577)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572))))) (initPM 5577)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))))) (initPM 5577))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5563))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5563))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5572))))) (initPM 5577)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5568))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5572))))) (initPM 5577)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]




-- ===== shape helpers =====
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10517_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024] := by
  have h10345 := hbase345
  have h10401 : (denoteGraph_ringAttn pm_goal_3 initPM 10401).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573, denote_pm_goal_3_10569]; rfl
  have h10405 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10345 h10401
  have h10409sh : (denoteGraph_ringAttn pm_goal_3 initPM 10409).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581, rms_sh]; exact h10405
  have h10429sh : (denoteGraph_ringAttn pm_goal_3 initPM 10429).shape = [2048, 1024] := by
    rw [br_pm_10429, br_pm_16320]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10409sh]; rfl) (by rw [h10409sh]; rfl)
  have h10443sh : (denoteGraph_ringAttn pm_goal_3 initPM 10443).shape = [2048, 1] := by
    rw [br_pm_10443, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10441]
    exact fw_view_shape_eq _ _
  have h10499sh : (denoteGraph_ringAttn pm_goal_3 initPM 10499).shape = [2048, 1024] := by
    rw [br_pm_10499]; exact fw_view_shape_eq _ _
  have h10503sh : (denoteGraph_ringAttn pm_goal_3 initPM 10503).shape = [2048, 1024] := by
    rw [br_pm_10503, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10443sh h10499sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10429) (denoteGraph_ringAttn pm_goal_3 initPM 10503)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10429sh h10503sh
  have h16301sh : (denoteGraph_ringAttn pm_goal_3 initPM 16301).shape = [2048, 1024] := by
    rw [br_pm_16301]; exact h10405
  have h10513sh : (denoteGraph_ringAttn pm_goal_3 initPM 10513).shape = [2048, 1024] := by
    rw [br_pm_10513, br_pm_10507]; exact hinnerA
  rw [br_pm_10517]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16301sh h10513sh


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem pm_goal_3_10518_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hbase346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024]) :
    (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024] := by
  have h10346 := hbase346
  have h10402 : (denoteGraph_ringAttn pm_goal_3 initPM 10402).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574, denote_pm_goal_3_10570]; rfl
  have h10406 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578]
    exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024]
      h10346 h10402
  have h10410sh : (denoteGraph_ringAttn pm_goal_3 initPM 10410).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582, rms_sh]; exact h10406
  have h10430sh : (denoteGraph_ringAttn pm_goal_3 initPM 10430).shape = [2048, 1024] := by
    rw [br_pm_10430, br_pm_16343]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10410sh]; rfl) (by rw [h10410sh]; rfl)
  have h10444sh : (denoteGraph_ringAttn pm_goal_3 initPM 10444).shape = [2048, 1] := by
    rw [br_pm_10444, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10442]
    exact fw_view_shape_eq _ _
  have h10500sh : (denoteGraph_ringAttn pm_goal_3 initPM 10500).shape = [2048, 1024] := by
    rw [br_pm_10500]; exact fw_view_shape_eq _ _
  have h10504sh : (denoteGraph_ringAttn pm_goal_3 initPM 10504).shape = [2048, 1024] := by
    rw [br_pm_10504, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10444sh h10500sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10430) (denoteGraph_ringAttn pm_goal_3 initPM 10504)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10430sh h10504sh
  have h16309sh : (denoteGraph_ringAttn pm_goal_3 initPM 16309).shape = [2048, 1024] := by
    rw [br_pm_16309]; exact h10406
  have h10514sh : (denoteGraph_ringAttn pm_goal_3 initPM 10514).shape = [2048, 1024] := by
    rw [br_pm_10514, br_pm_10508]; exact hinnerB
  rw [br_pm_10518]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h16309sh h10514sh

-- ===== carry_5583 =====
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_carry_5583_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096)
    (hcarry5583 : denoteGraph_ringAttn sm_goal_3 initSM 5534 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10345,
         denoteGraph_ringAttn pm_goal_3 initPM 10346])
    (h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024])
    (h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5583 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 10517,
         denoteGraph_ringAttn pm_goal_3 initPM 10518] := by
  have hattn := sm_pm_attention_L16_commute initSM initPM hSM hPM hInit hcarry5583 h10517 h10518 h_bound
  have hw5586 : (initPM 5537).shape = [16, 64, 1024] := hPM 5537 [16, 64, 1024] (by decide)
  have hw5595 : (initPM 5546).shape = [1024, 1024] := hPM 5546 [1024, 1024] (by decide)
  have h10521 : (denoteGraph_ringAttn pm_goal_3 initPM 10349).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10521, rms_sh]; exact h10517
  have h10522 : (denoteGraph_ringAttn pm_goal_3 initPM 10350).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10522, rms_sh]; exact h10518
  have h10523d : (denoteGraph_ringAttn pm_goal_3 initPM 10351).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10523]; exact ph_lin_shape_gen _ _ 2048 16 h10521 hw5586
  have h10524d : (denoteGraph_ringAttn pm_goal_3 initPM 10352).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_10524]; exact ph_lin_shape_gen _ _ 2048 16 h10522 hw5586
  -- folded-store bridges at the two attention Q tids
  have b1417_10523 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10351
      = denoteGraph_ringAttn pm_goal_3 initPM 10351 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10351 1347 (by decide) (by decide)).symm
  have b1417_10524 : (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM 10352
      = denoteGraph_ringAttn pm_goal_3 initPM 10352 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10352 1347 (by decide) (by decide)).symm
  have b1418_10523 : (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10351
      = denoteGraph_ringAttn pm_goal_3 initPM 10351 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10351 1348 (by decide) (by decide)).symm
  have b1418_10524 : (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM 10352
      = denoteGraph_ringAttn pm_goal_3 initPM 10352 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10352 1348 (by decide) (by decide)).symm
  have h10547 : (denoteGraph_ringAttn pm_goal_3 initPM 10375).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L16_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_16 nR0_16 nR1_16 0 buddy_r0_16 (by decide)]
    have e0 : nR0_16.ins.getD 0 0 = 10351 := by decide
    have e1 : nR1_16.ins.getD 0 0 = 10352 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
         (pm_goal_3.nodes.take 1347).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1417_10523, b1417_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h10548 : (denoteGraph_ringAttn pm_goal_3 initPM 10376).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L16_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_16 nR0_16 nR1_16 1 buddy_r1_16 (by decide)]
    have e0 : nR0_16.ins.getD 0 0 = 10351 := by decide
    have e1 : nR1_16.ins.getD 0 0 = 10352 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_16.ins.getD 0 0),
         (pm_goal_3.nodes.take 1348).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_16.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1418_10523, b1418_10524]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h10523d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl

  have hreshape := sm_pm_reshape_float_L16_commute initSM initPM hInit hattn h10547 h10548 hw5595
  have h10573 : (denoteGraph_ringAttn pm_goal_3 initPM 10401).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10573, denote_pm_goal_3_10569]; rfl
  have h10574 : (denoteGraph_ringAttn pm_goal_3 initPM 10402).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10574, denote_pm_goal_3_10570]; rfl
  have hcarry5550 := sm_pm_carry_5599_commute initSM initPM hcarry5583 hreshape h10517 h10518 h10573 h10574
  have h10405 : (denoteGraph_ringAttn pm_goal_3 initPM 10405).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10577]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10517 h10573
  have h10406 : (denoteGraph_ringAttn pm_goal_3 initPM 10406).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10578]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10518 h10574
  have hgmm := sm_pm_moe_gmm_L16_commute initSM initPM hInit hPM hcarry5550 h10405 h10406
  have hgate := sm_pm_gate_mul_L16_commute initSM initPM hInit hPM hcarry5550 h10405 h10406
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h10409sh : (denoteGraph_ringAttn pm_goal_3 initPM 10409).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10581, rms_sh]; exact h10405
  have h10410sh : (denoteGraph_ringAttn pm_goal_3 initPM 10410).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_10582, rms_sh]; exact h10406
  have h10429sh : (denoteGraph_ringAttn pm_goal_3 initPM 10429).shape = [2048, 1024] := by
    rw [br_pm_10429, br_pm_16320]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10409sh]; rfl) (by rw [h10409sh]; rfl)
  have h10430sh : (denoteGraph_ringAttn pm_goal_3 initPM 10430).shape = [2048, 1024] := by
    rw [br_pm_10430, br_pm_16343]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h10410sh]; rfl) (by rw [h10410sh]; rfl)
  have h10443sh : (denoteGraph_ringAttn pm_goal_3 initPM 10443).shape = [2048, 1] := by
    rw [br_pm_10443, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10441]
    exact fw_view_shape_eq _ _
  have h10499sh : (denoteGraph_ringAttn pm_goal_3 initPM 10499).shape = [2048, 1024] := by
    rw [br_pm_10499]; exact fw_view_shape_eq _ _
  have h10503sh : (denoteGraph_ringAttn pm_goal_3 initPM 10503).shape = [2048, 1024] := by
    rw [br_pm_10503, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10443sh h10499sh]; rfl
  have h10444sh : (denoteGraph_ringAttn pm_goal_3 initPM 10444).shape = [2048, 1] := by
    rw [br_pm_10444, TrainVerify.Denote.fw_sigmoid_shape, br_pm_10442]
    exact fw_view_shape_eq _ _
  have h10500sh : (denoteGraph_ringAttn pm_goal_3 initPM 10500).shape = [2048, 1024] := by
    rw [br_pm_10500]; exact fw_view_shape_eq _ _
  have h10504sh : (denoteGraph_ringAttn pm_goal_3 initPM 10504).shape = [2048, 1024] := by
    rw [br_pm_10504, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h10444sh h10500sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10429) (denoteGraph_ringAttn pm_goal_3 initPM 10503)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10429sh h10503sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10430) (denoteGraph_ringAttn pm_goal_3 initPM 10504)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h10430sh h10504sh
  -- === assemble ===
  rw [br_pm_10517, br_pm_16301, br_pm_10513, br_pm_10507,
      br_pm_10518, br_pm_16309, br_pm_10514, br_pm_10508]
  rw [br_sm_5583, br_sm_8307, br_sm_5582, br_sm_5581]
  rw [hcarry5550, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10429) (denoteGraph_ringAttn pm_goal_3 initPM 10430)
        (denoteGraph_ringAttn pm_goal_3 initPM 10503) (denoteGraph_ringAttn pm_goal_3 initPM 10504)
        h10429sh h10430sh h10503sh h10504sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 10405) (denoteGraph_ringAttn pm_goal_3 initPM 10406)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10429) (denoteGraph_ringAttn pm_goal_3 initPM 10503))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 10430) (denoteGraph_ringAttn pm_goal_3 initPM 10504))
        h10405 h10406 hinnerA hinnerB]



end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L16_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L16_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L16_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L16
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L16_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L16_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L16_hbound_witness
