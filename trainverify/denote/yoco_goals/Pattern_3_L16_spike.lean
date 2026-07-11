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

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L16_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L16_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5599_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L16_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L16
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L16_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L16_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L16_hbound_witness
