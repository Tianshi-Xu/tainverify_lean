/-
  Pattern_3_L23_spike.lean — L23 zigzag-band proof (parallel worker, based on
  the L12 pilot `Pattern_3_L12_spike.lean`).

  Structurally analogous to L12 but with L23-specific TIDs.  The L23 attention
  block is *simpler* than L12's: the context-parallel Q shuffle and the K/V
  projections happen once at L12 and are replicated to L12..L23, so L23's Q path
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

/-! ## L23 attention node declarations + buddy proofs.
SM attn node index 889; PM r0 = 1837; PM r1 = 1838. -/

def nSM_23 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5881, 5882, 5883, 5884, 5885], outs := [5886],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_23 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11555, 5882, 5883, 5884, 5885], outs := [11579],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_23 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11556, 5882, 5883, 5884, 5885], outs := [11580],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_23 : ringAttnBuddies sm_goal_3 nSM_23 = [nSM_23] := by
  show (List.filter (fun m => decide (m.op = nSM_23.op) && decide (m.params = nSM_23.params) &&
      decide (m.ins.getD 3 0 = nSM_23.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_23.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_23]
  rw [show (List.filter (fun m => decide (m.op = nSM_23.op) && decide (m.params = nSM_23.params) &&
      decide (m.ins.getD 3 0 = nSM_23.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_23.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_23] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_23 : ringAttnBuddies pm_goal_3 nR0_23 = [nR0_23, nR1_23] := by
  show (List.filter (fun m => decide (m.op = nR0_23.op) && decide (m.params = nR0_23.params) &&
      decide (m.ins.getD 3 0 = nR0_23.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_23.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_23, nR1_23]
  rw [show (List.filter (fun m => decide (m.op = nR0_23.op) && decide (m.params = nR0_23.params) &&
      decide (m.ins.getD 3 0 = nR0_23.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_23.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_23, nR1_23] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_23 : ringAttnBuddies pm_goal_3 nR1_23 = [nR0_23, nR1_23] := by
  show (List.filter (fun m => decide (m.op = nR1_23.op) && decide (m.params = nR1_23.params) &&
      decide (m.ins.getD 3 0 = nR1_23.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_23.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_23, nR1_23]
  rw [show (List.filter (fun m => decide (m.op = nR1_23.op) && decide (m.params = nR1_23.params) &&
      decide (m.ins.getD 3 0 = nR1_23.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_23.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_23, nR1_23] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L23 attention denote <-> applyNodeRingAttn_zigzag bridges -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L23_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5886
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_23 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5886
      = (sm_goal_3.nodes.take 890).foldl (applyNodeRingAttn sm_goal_3) initSM 5886 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5886 890 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 890 = sm_goal_3.nodes.take 889 ++ [nSM_23] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5881 5882 5883 5884 5885 5886 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L23_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11579
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_23 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11579
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 11579 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11579 1838 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1838 = pm_goal_3.nodes.take 1837 ++ [nR0_23] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 11555 5882 5883 5884 5885 11579 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L23_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11580
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_23 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 11580
      = (pm_goal_3.nodes.take 1839).foldl (applyNodeRingAttn pm_goal_3) initPM 11580 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11580 1839 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1839 = pm_goal_3.nodes.take 1838 ++ [nR1_23] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 11556 5882 5883 5884 5885 11580 [16, 4, 64, 64, 1, 0]


/-! ### SM-side denote-unfold chain (L23) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5879 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5879 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5877) (initSM 5878) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5879 8568 5878 887
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8568, 5878], outs := [5879] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8568 5878 5879)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8568 5877 886
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5877], outs := [8568, 8572], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5877 8568 [8568, 8572] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5878 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5881 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5881 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5879) (initSM 5880) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5881 5879 5880 888
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5879, 5880], outs := [5881] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5879 5880 5881 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5880 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5887 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5887 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5886) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5887 5886 890
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5886], outs := [5887], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5886 5887 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5888 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5888 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5887) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5888 5887 891
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5887], outs := [5888], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5887 5888 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5890 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5890 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5888) (initSM 5889) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5890 5888 5889 892
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5888, 5889], outs := [5890] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5888 5889 5890)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5889 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5891 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5891 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5890) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5891 5890 893
    ({ rank := 0, op := "OpName.FW_view", ins := [5890], outs := [5891], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5890 5891)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5892 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5892 =
      denoteGraph_ringAttn sm_goal_3 initSM 5891 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5892 5891 894
    ({ rank := 0, op := "OpName.FW_float", ins := [5891], outs := [5892] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5891 5892 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5893 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5893 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5877)
        (denoteGraph_ringAttn sm_goal_3 initSM 5892) := by
  have hmref : denoteGraph_ringAttn sm_goal_3 initSM 8572 = denoteGraph_ringAttn sm_goal_3 initSM 5877 :=
    DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8572 5877 886
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5877], outs := [8568, 8572], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5877 8572 [8568, 8572] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5893 8572 5892 895
    ({ rank := 0, op := "OpName.FW_add", ins := [8572, 5892], outs := [5893] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8572 5892 5893)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5895 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5895 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5893) (initSM 5894) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5895 8576 5894 897
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8576, 5894], outs := [5895] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8576 5894 5895)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8576 5893 896
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5893 8576 [8576, 8580] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5894 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5896 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5896 =
      denoteGraph_ringAttn sm_goal_3 initSM 5895 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5896 8587 899
    ({ rank := 0, op := "OpName.FW_float", ins := [8587], outs := [5896] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8587 5896 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8587 5895 898
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5895 8587 [8587, 8591, 8595, 8599, 8603] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5898 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5898 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5896) (initSM 5897) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5898 5896 5897 900
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5896, 5897], outs := [5898] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5896 5897 5898 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5897 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5900 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5900 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5898) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5898).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5900 5898 901
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5898 5899 5900 5901 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5882 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5882 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5882 8077 491
    ({ rank := 0, op := "OpName.FW_to", ins := [8077], outs := [5882] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8077 5882 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8077 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8077 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5883 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5883 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5883 8135 503
    ({ rank := 0, op := "OpName.FW_to", ins := [8135], outs := [5883] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8135 5883 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8135 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8135 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ### PM-side denote-unfold chain (L23) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11553 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11553 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11549) (initPM 5878) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11553 16827 5878 1833
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16827, 5878], outs := [11553] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16827 5878 11553)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16827 11549 1831
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11549], outs := [16827, 16831], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11549 16827 [16827, 16831] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5878 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11555 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11555 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11553) (initPM 5880) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11555 11553 5880 1835
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11553, 5880], outs := [11555] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 11553 5880 11555 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5880 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11581 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11581 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11579) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11581 11579 1839
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11579], outs := [11581], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11579 11581 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11587 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11587 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11581) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11587 11581 1841
    ({ rank := 0, op := "OpName.FW_reshape", ins := [11581], outs := [11587], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 11581 11587 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11591 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11591 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11587) (initPM 5889) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11591 11587 5889 1843
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11587, 5889], outs := [11591] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 11587 5889 11591)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5889 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11601 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11601 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11591) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11601 11591 1845
    ({ rank := 0, op := "OpName.FW_view", ins := [11591], outs := [11601], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 11591 11601)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11605 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11605 =
      denoteGraph_ringAttn pm_goal_3 initPM 11601 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11605 11601 1847
    ({ rank := 0, op := "OpName.FW_float", ins := [11601], outs := [11605] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 11601 11605 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11609 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11609 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11549)
        (denoteGraph_ringAttn pm_goal_3 initPM 11605) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16831 = denoteGraph_ringAttn pm_goal_3 initPM 11549 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16831 11549 1831
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11549], outs := [16827, 16831], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11549 16831 [16827, 16831] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11609 16831 11605 1849
    ({ rank := 0, op := "OpName.FW_add", ins := [16831, 11605], outs := [11609] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 16831 11605 11609)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11613 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11613 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11609) (initPM 5894) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11613 16843 5894 1853
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [16843, 5894], outs := [11613] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 16843 5894 11613)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16843 11609 1851
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11609 16843 [16843, 16847] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5894 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11615 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11615 =
      denoteGraph_ringAttn pm_goal_3 initPM 11613 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11615 16862 1857
    ({ rank := 0, op := "OpName.FW_float", ins := [16862], outs := [11615] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16862 11615 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16862 11613 1855
      ({ rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 11613 16862 [16862, 16866, 16870, 16874, 16878] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11621 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11621 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11615) (initPM 5897) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11621 11615 5897 1859
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [11615, 5897], outs := [11621] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 11615 5897 11621 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5897 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11625 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11625 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11621) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11621).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11625 11621 1861
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 11621 11623 11625 11627 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11554 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11554 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11550) (initPM 5878) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11554 16835 5878 1834
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16835, 5878], outs := [11554] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16835 5878 11554)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16835 11550 1832
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11550], outs := [16835, 16839], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11550 16835 [16835, 16839] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5878 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11556 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11556 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 11554) (initPM 5880) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11556 11554 5880 1836
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11554, 5880], outs := [11556] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 11554 5880 11556 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5880 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11582 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11582 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11580) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11582 11580 1840
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11580], outs := [11582], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11580 11582 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11588 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11588 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11582) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11588 11582 1842
    ({ rank := 1, op := "OpName.FW_reshape", ins := [11582], outs := [11588], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 11582 11588 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11592 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11592 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 11588) (initPM 5889) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11592 11588 5889 1844
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11588, 5889], outs := [11592] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 11588 5889 11592)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5889 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11602 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11602 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11592) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11602 11592 1846
    ({ rank := 1, op := "OpName.FW_view", ins := [11592], outs := [11602], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 11592 11602)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11606 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11606 =
      denoteGraph_ringAttn pm_goal_3 initPM 11602 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11606 11602 1848
    ({ rank := 1, op := "OpName.FW_float", ins := [11602], outs := [11606] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 11602 11606 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11610 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11610 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 11550)
        (denoteGraph_ringAttn pm_goal_3 initPM 11606) := by
  have hmref : denoteGraph_ringAttn pm_goal_3 initPM 16839 = denoteGraph_ringAttn pm_goal_3 initPM 11550 :=
    DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16839 11550 1832
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11550], outs := [16835, 16839], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11550 16839 [16835, 16839] 2 (by decide) (by decide))
      rfl
  rw [← hmref]
  exact DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11610 16839 11606 1850
    ({ rank := 1, op := "OpName.FW_add", ins := [16839, 11606], outs := [11610] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 16839 11606 11610)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11614 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11614 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11610) (initPM 5894) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11614 16851 5894 1854
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [16851, 5894], outs := [11614] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 16851 5894 11614)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16851 11610 1852
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11610 16851 [16851, 16855] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5894 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11616 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11616 =
      denoteGraph_ringAttn pm_goal_3 initPM 11614 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11616 16885 1858
    ({ rank := 1, op := "OpName.FW_float", ins := [16885], outs := [11616] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16885 11616 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16885 11614 1856
      ({ rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 11614 16885 [16885, 16889, 16893, 16897, 16901] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11622 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11622 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 11616) (initPM 5897) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11622 11616 5897 1860
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [11616, 5897], outs := [11622] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 11616 5897 11622 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5897 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11626 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11626 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 11622) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 11622).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 11626 11622 1862
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 11622 11624 11626 11628 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5882 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5882 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5882 15859 1042
    ({ rank := 1, op := "OpName.FW_to", ins := [15859], outs := [5882] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15859 5882 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15859 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15859 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5883 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5883 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5883 15965 1066
    ({ rank := 1, op := "OpName.FW_to", ins := [15965], outs := [5883] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15965 5883 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15965 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15965 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)


/-! ## L23 commute theorems -/

-- Q sharding commute: SM 5881 = allGather0[PM 11555, PM 11556].
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L23_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5877 : denoteGraph_ringAttn sm_goal_3 initSM 5877 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11549,
         denoteGraph_ringAttn pm_goal_3 initPM 11550])
    (h11549 : (denoteGraph_ringAttn pm_goal_3 initPM 11549).shape = [2048, 1024])
    (h11550 : (denoteGraph_ringAttn pm_goal_3 initPM 11550).shape = [2048, 1024])
    (hw5880 : (initPM 5880).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5881 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11555,
         denoteGraph_ringAttn pm_goal_3 initPM 11556] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5878 : initSM 5878 = initPM 5878 := hb initGoal_5878 (by decide) rfl
  have hw5880e : initSM 5880 = initPM 5880 := hb initGoal_5880 (by decide) rfl
  rw [denote_sm_goal_3_5881, denote_sm_goal_3_5879,
      denote_pm_goal_3_11555, denote_pm_goal_3_11553,
      denote_pm_goal_3_11556, denote_pm_goal_3_11554]
  rw [hcarry5877, hw5878, hw5880e]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11549) (initPM 5878)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h11549
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11550) (initPM 5878)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h11550
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5878) 2048 1024 (by omega) (by omega) h11549 h11550,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5880) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms1 hrms2 hw5880]

-- PM K/V full-tensor shapes [4096,4,64] from the L12 K/V projection (via hPM).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5882_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5882).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5882, denote_pm_goal_3_5334]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem pm_5883_shape (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 5883).shape = [4096, 4, 64] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  rw [denote_pm_goal_3_5883, denote_pm_goal_3_5336]
  exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))

-- K/V replication (cross-graph, full tensor): SM 5882 = PM 5882, SM 5883 = PM 5883.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L23_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5882 =
      denoteGraph_ringAttn pm_goal_3 initPM 5882 := by
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5882, denote_pm_goal_3_5882, ← denote_sm_goal_3_5343,
      ← denote_pm_goal_3_5343, hkrepl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L23_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5883 =
      denoteGraph_ringAttn pm_goal_3 initPM 5883 := by
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5883, denote_pm_goal_3_5883, ← denote_sm_goal_3_5344,
      ← denote_pm_goal_3_5344, hvrepl]


/-! ## L23 attention commute (context-parallel, replicated K/V) -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_attention_L23_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5877 : denoteGraph_ringAttn sm_goal_3 initSM 5877 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11549,
         denoteGraph_ringAttn pm_goal_3 initPM 11550])
    (h11549 : (denoteGraph_ringAttn pm_goal_3 initPM 11549).shape = [2048, 1024])
    (h11550 : (denoteGraph_ringAttn pm_goal_3 initPM 11550).shape = [2048, 1024])
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5885)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5886 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11579,
         denoteGraph_ringAttn pm_goal_3 initPM 11580] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hb := L12_weight_eq initSM initPM hInit
  have hw5880 : (initPM 5880).shape = [16, 64, 1024] := hPM 5880 [16, 64, 1024] (by decide)
  -- Q sharding + K/V replication (denote form)
  have hqf := sm_pm_qfull_L23_commute initSM initPM hInit hcarry5877 h11549 h11550 hw5880
  have hK := sm_pm_krepl_L23_commute initSM initPM hInit hcarry5330
  have hV := sm_pm_vrepl_L23_commute initSM initPM hInit hcarry5330
  have hKsh := pm_5882_shape initPM hPM
  have hVsh := pm_5883_shape initPM hPM
  -- PM Q shard shapes [2048,16,64]
  have h11553 : (denoteGraph_ringAttn pm_goal_3 initPM 11553).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11553, rms_sh]; exact h11549
  have h11554 : (denoteGraph_ringAttn pm_goal_3 initPM 11554).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11554, rms_sh]; exact h11550
  have h11555 : (denoteGraph_ringAttn pm_goal_3 initPM 11555).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_11555]; exact ph_lin_shape_gen _ _ 2048 16 h11553 hw5880
  have h11556 : (denoteGraph_ringAttn pm_goal_3 initPM 11556).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_11556]; exact ph_lin_shape_gen _ _ 2048 16 h11554 hw5880
  -- SM Q shape [4096,16,64]
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5881).shape = [4096, 16, 64] := by
    rw [hqf]; exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h11555)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5881).shape.length := by rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5882).shape.length := by rw [hK, hKsh]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5883).shape.length := by rw [hV, hVsh]; decide
  -- folded <-> denote bridges (SM, take 889)
  have bSM5881 : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5881 = denoteGraph_ringAttn sm_goal_3 initSM 5881 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5881 889 (by decide) (by decide)).symm
  have bSM5882 : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5882 = denoteGraph_ringAttn sm_goal_3 initSM 5882 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5882 889 (by decide) (by decide)).symm
  have bSM5883 : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5883 = denoteGraph_ringAttn sm_goal_3 initSM 5883 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5883 889 (by decide) (by decide)).symm
  -- folded <-> denote bridges (PM, take 1837)
  have bPM11555 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11555 = denoteGraph_ringAttn pm_goal_3 initPM 11555 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11555 1837 (by decide) (by decide)).symm
  have bPM11556 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11556 = denoteGraph_ringAttn pm_goal_3 initPM 11556 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11556 1837 (by decide) (by decide)).symm
  have bPM5882 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5882 = denoteGraph_ringAttn pm_goal_3 initPM 5882 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5882 1837 (by decide) (by decide)).symm
  have bPM5883 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5883 = denoteGraph_ringAttn pm_goal_3 initPM 5883 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5883 1837 (by decide) (by decide)).symm
  -- cu_seqlens: not written in prefixes
  have hS5884 : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5884 = initSM 5884 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 889) initSM 5884 (by decide) (by decide)
  have hS5885 : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5885 = initSM 5885 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 889) initSM 5885 (by decide) (by decide)
  have hP5884 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5884 = initPM 5884 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1837) initPM 5884 (by decide) (by decide)
  have hP5885 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5885 = initPM 5885 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1837) initPM 5885 (by decide) (by decide)
  have hw5884 : initSM 5884 = initPM 5884 := hb initGoal_5884 (by decide) rfl
  have hw5885 : initSM 5885 = initPM 5885 := hb initGoal_5885 (by decide) rfl
  -- reconstruction-input hypotheses (folded form)
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5881).shape.length
    rw [bSM5881]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5882).shape.length
    rw [bSM5882]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5883).shape.length
    rw [bSM5883]; exact hv_sm
  have hq_full : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 0 0) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 0 0),
        (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 0 0)] := by
    show (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5881 =
      allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11555,
        (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11556]
    rw [bSM5881, bPM11555, bPM11556]; exact hqf
  have hk_repl : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 1 0) =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 1 0) := by
    show (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5882 =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5882
    rw [bSM5882, bPM5882]; exact hK
  have hv_repl : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 2 0) =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 2 0) := by
    show (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5883 =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5883
    rw [bSM5883, bPM5883]; exact hV
  have hk_shape : ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 1 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5882).shape = [4096, 4, 64]
    rw [bPM5882]; exact hKsh
  have hv_shape : ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 2 0)).shape = [4096, 4, 64] := by
    show ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5883).shape = [4096, 4, 64]
    rw [bPM5883]; exact hVsh
  have h_bound' : ∀ t, (decodeCuSeqlens ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 4 0))).getD (t+1) 0 ≤ 4096 := by
    intro t
    show (decodeCuSeqlens ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5885)).getD (t+1) 0 ≤ 4096
    rw [hP5885]; exact h_bound t
  have hcuQ : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 3 0) =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 3 0) := by
    show (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5884 =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5884
    rw [hS5884, hP5884, hw5884]
  have hcuK : (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_23.ins.getD 4 0) =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 4 0) := by
    show (sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM 5885 =
      (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5885
    rw [hS5885, hP5885, hw5885]
  -- Q allGather shape for hfull_shape
  have hQAG : (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 0 0),
       (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 0 0)]).shape = [4096, 16, 64] := by
    show (allGatherPrimDimN 0 2 0
      [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11555,
       (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11556]).shape = [4096, 16, 64]
    rw [bPM11555, bPM11556]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h11555)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 0 0),
          (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 1 0),
          (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 2 0),
          (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 2 0)])
        ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 3 0))
        ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 4 0))
        (nR0_23.params.getD 0 1) (nR0_23.params.getD 1 1) (nR0_23.params.getD 2 1) (nR0_23.params.getD 3 1)
        (decide (nR0_23.params.getD 4 0 ≠ 0)) (nR0_23.params.getD 5 0)).shape
        = [2 * 2048, nR0_23.params.getD 0 1, nR0_23.params.getD 3 1] := by
    rw [fw_attn_varlen_shape_p3, hQAG]
    rfl
  -- rank-1 buddy store alignment (take 1837 -> take 1838)
  have e11555 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11555
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 11555 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11555 1837 1838 (by omega) (by decide) (by decide)).symm
  have e11556 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11556
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 11556 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11556 1837 1838 (by omega) (by decide) (by decide)).symm
  have e5882 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5882
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 5882 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5882 1837 1838 (by omega) (by decide) (by decide)).symm
  have e5883 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5883
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 5883 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5883 1837 1838 (by omega) (by decide) (by decide)).symm
  have e5884 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5884
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 5884 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5884 1837 1838 (by omega) (by decide) (by decide)).symm
  have e5885 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 5885
      = (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 5885 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5885 1837 1838 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_23
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_23 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_23]; intro m hm; fin_cases hm
      · exact e11555
      · exact e11556
    · rw [buddy_r1_23]; intro m hm; fin_cases hm
      · exact e5882
      · exact e5882
    · rw [buddy_r1_23]; intro m hm; fin_cases hm
      · exact e5883
      · exact e5883
    · exact e5884
    · exact e5885
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 889).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_23 nR0_23 nR1_23 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_23 buddy_r0_23 buddy_r1_23 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound'
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L23_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L23_r0_bridge, ← denote_pm_attn_L23_r1_bridge]


/-! ## L23 reshape/float, residual carry, and router head -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_L23_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5886 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11579,
         denoteGraph_ringAttn pm_goal_3 initPM 11580])
    (h11579 : (denoteGraph_ringAttn pm_goal_3 initPM 11579).shape = [2048, 16, 64])
    (h11580 : (denoteGraph_ringAttn pm_goal_3 initPM 11580).shape = [2048, 16, 64])
    (hw5889 : (initPM 5889).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5892 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11605,
         denoteGraph_ringAttn pm_goal_3 initPM 11606] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5889 = initPM 5889 := hb initGoal_5889 (by decide) rfl
  rw [denote_sm_goal_3_5892, denote_sm_goal_3_5891, denote_sm_goal_3_5890,
      denote_sm_goal_3_5888, denote_sm_goal_3_5887,
      denote_pm_goal_3_11605, denote_pm_goal_3_11601, denote_pm_goal_3_11591,
      denote_pm_goal_3_11587, denote_pm_goal_3_11581,
      denote_pm_goal_3_11606, denote_pm_goal_3_11602, denote_pm_goal_3_11592,
      denote_pm_goal_3_11588, denote_pm_goal_3_11582]
  rw [hattn, hw]
  rw [carry_view_commute _ _ h11579 h11580]
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11579))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11580))).shape = [2048, 1024] := rfl
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5889) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5889]
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11579))) (initPM 5889)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5889]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11580))) (initPM 5889)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5889]; rfl
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11579))) (initPM 5889),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 11580))) (initPM 5889)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5893_commute (initSM initPM : Store)
    (hcarry5877 : denoteGraph_ringAttn sm_goal_3 initSM 5877 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11549,
         denoteGraph_ringAttn pm_goal_3 initPM 11550])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5892 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11605,
         denoteGraph_ringAttn pm_goal_3 initPM 11606])
    (h11549 : (denoteGraph_ringAttn pm_goal_3 initPM 11549).shape = [2048, 1024])
    (h11550 : (denoteGraph_ringAttn pm_goal_3 initPM 11550).shape = [2048, 1024])
    (h11605 : (denoteGraph_ringAttn pm_goal_3 initPM 11605).shape = [2048, 1024])
    (h11606 : (denoteGraph_ringAttn pm_goal_3 initPM 11606).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5893 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11609,
         denoteGraph_ringAttn pm_goal_3 initPM 11610] := by
  rw [denote_sm_goal_3_5893, denote_pm_goal_3_11609, denote_pm_goal_3_11610]
  rw [hcarry5877, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h11549 h11550 h11605 h11606]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L23_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5893 : denoteGraph_ringAttn sm_goal_3 initSM 5893 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11609,
         denoteGraph_ringAttn pm_goal_3 initPM 11610])
    (h11609 : (denoteGraph_ringAttn pm_goal_3 initPM 11609).shape = [2048, 1024])
    (h11610 : (denoteGraph_ringAttn pm_goal_3 initPM 11610).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5898 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11621,
         denoteGraph_ringAttn pm_goal_3 initPM 11622] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5894 : initSM 5894 = initPM 5894 := hb initGoal_5894 (by decide) rfl
  have hw5897 : initSM 5897 = initPM 5897 := hb initGoal_5897 (by decide) rfl
  have hw5897sh : (initPM 5897).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5897 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5897] using hsh
  rw [denote_sm_goal_3_5898, denote_sm_goal_3_5896, denote_sm_goal_3_5895,
      denote_pm_goal_3_11621, denote_pm_goal_3_11615, denote_pm_goal_3_11613,
      denote_pm_goal_3_11622, denote_pm_goal_3_11616, denote_pm_goal_3_11614]
  rw [hw5894, hw5897, hcarry5893]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5894) 2048 1024 (by omega) (by omega) h11609 h11610]
  have hrms1 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11609) (initPM 5894)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h11609
  have hrms2 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11610) (initPM 5894)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h11610
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5897) 2048 1024 64 (by omega) (by omega) (by omega) hrms1 hrms2 hw5897sh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L23 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5893 : denoteGraph_ringAttn sm_goal_3 initSM 5893 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11609,
         denoteGraph_ringAttn pm_goal_3 initPM 11610])
    (h11609 : (denoteGraph_ringAttn pm_goal_3 initPM 11609).shape = [2048, 1024])
    (h11610 : (denoteGraph_ringAttn pm_goal_3 initPM 11610).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5900 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11625,
         denoteGraph_ringAttn pm_goal_3 initPM 11626] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5897sh : (initPM 5897).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5897 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5897] using hsh
  have hnl := sm_pm_nl_L23_commute initSM initPM hInit hcarry5893 h11609 h11610
  have hs11621 : (denoteGraph_ringAttn pm_goal_3 initPM 11621).shape = [2048, 64] := by
    rw [denote_pm_goal_3_11621, denote_pm_goal_3_11615, denote_pm_goal_3_11613]
    exact nl_sh 2048 1024 64 _ (initPM 5897) (by rw [rms_sh]; exact h11609) hw5897sh
  have hs11622 : (denoteGraph_ringAttn pm_goal_3 initPM 11622).shape = [2048, 64] := by
    rw [denote_pm_goal_3_11622, denote_pm_goal_3_11616, denote_pm_goal_3_11614]
    exact nl_sh 2048 1024 64 _ (initPM 5897) (by rw [rms_sh]; exact h11610) hw5897sh
  have hSM5898sh : (denoteGraph_ringAttn sm_goal_3 initSM 5898).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs11621
  rw [denote_sm_goal_3_5900, denote_pm_goal_3_11625, denote_pm_goal_3_11626]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5898).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5898sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11621).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs11621]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 11622).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs11622]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs11621 hs11622


/-! ## L23 router — assembled from the attention commute + prior-layer carry -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L23_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5877 : denoteGraph_ringAttn sm_goal_3 initSM 5877 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11549,
         denoteGraph_ringAttn pm_goal_3 initPM 11550])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5886 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11579,
         denoteGraph_ringAttn pm_goal_3 initPM 11580])
    (h11579 : (denoteGraph_ringAttn pm_goal_3 initPM 11579).shape = [2048, 16, 64])
    (h11580 : (denoteGraph_ringAttn pm_goal_3 initPM 11580).shape = [2048, 16, 64])
    (h11549 : (denoteGraph_ringAttn pm_goal_3 initPM 11549).shape = [2048, 1024])
    (h11550 : (denoteGraph_ringAttn pm_goal_3 initPM 11550).shape = [2048, 1024])
    (hw5889 : (initPM 5889).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5900 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11625,
         denoteGraph_ringAttn pm_goal_3 initPM 11626] := by
  have hreshape := sm_pm_reshape_float_L23_commute initSM initPM hInit hattn h11579 h11580 hw5889
  have h11605 : (denoteGraph_ringAttn pm_goal_3 initPM 11605).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11605, denote_pm_goal_3_11601]; rfl
  have h11606 : (denoteGraph_ringAttn pm_goal_3 initPM 11606).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11606, denote_pm_goal_3_11602]; rfl
  have hcarry5893 := sm_pm_carry_5893_commute initSM initPM hcarry5877 hreshape h11549 h11550 h11605 h11606
  have h11609 : (denoteGraph_ringAttn pm_goal_3 initPM 11609).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11609]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h11549 h11605
  have h11610 : (denoteGraph_ringAttn pm_goal_3 initPM 11610).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11610]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h11550 h11606
  exact sm_pm_router_commute_L23 initSM initPM hInit hcarry5893 h11609 h11610

/-! ## L23 router — fully assembled

The only genuinely-external hypotheses beyond the two `StoreShapesHold`
well-formedness facts and the cut init goals are:
  * `h_bound`   — the K cu_seqlens well-formed-input contract (like L12),
  * `hcarry5877`, `h11549`, `h11550` — the L16 residual carry-out commute and
    its two PM-shard shapes (the prior layer L13..L16 is not yet on `main`,
    so per AGENTS.md #29 these are kept as statement-level hypotheses; see the
    `_witness` theorems below for their satisfiability).
All K/V replication / attention / router-head reasoning is discharged
internally (K/V come from the L12 projection via `sm_pm_carry_5330_commute`). -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 80000000 in
theorem sm_pm_router_commute_L23_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5885)).getD (t+1) 0 ≤ 4096)
    (hcarry5877 : denoteGraph_ringAttn sm_goal_3 initSM 5877 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11549,
         denoteGraph_ringAttn pm_goal_3 initPM 11550])
    (h11549 : (denoteGraph_ringAttn pm_goal_3 initPM 11549).shape = [2048, 1024])
    (h11550 : (denoteGraph_ringAttn pm_goal_3 initPM 11550).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5900 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 11625,
         denoteGraph_ringAttn pm_goal_3 initPM 11626] := by
  have hattn := sm_pm_attention_L23_commute initSM initPM hSM hPM hInit hcarry5877 h11549 h11550 h_bound
  have hw5880 : (initPM 5880).shape = [16, 64, 1024] := hPM 5880 [16, 64, 1024] (by decide)
  have hw5889 : (initPM 5889).shape = [1024, 1024] := hPM 5889 [1024, 1024] (by decide)
  -- PM Q shard shapes (for the attention chunk shape)
  have h11553 : (denoteGraph_ringAttn pm_goal_3 initPM 11553).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11553, rms_sh]; exact h11549
  have h11554 : (denoteGraph_ringAttn pm_goal_3 initPM 11554).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_11554, rms_sh]; exact h11550
  have h11555d : (denoteGraph_ringAttn pm_goal_3 initPM 11555).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_11555]; exact ph_lin_shape_gen _ _ 2048 16 h11553 hw5880
  have h11556d : (denoteGraph_ringAttn pm_goal_3 initPM 11556).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_11556]; exact ph_lin_shape_gen _ _ 2048 16 h11554 hw5880
  -- folded-store bridges at the two attention Q tids
  have b1837_11555 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11555
      = denoteGraph_ringAttn pm_goal_3 initPM 11555 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11555 1837 (by decide) (by decide)).symm
  have b1837_11556 : (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM 11556
      = denoteGraph_ringAttn pm_goal_3 initPM 11556 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11556 1837 (by decide) (by decide)).symm
  have b1838_11555 : (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 11555
      = denoteGraph_ringAttn pm_goal_3 initPM 11555 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11555 1838 (by decide) (by decide)).symm
  have b1838_11556 : (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM 11556
      = denoteGraph_ringAttn pm_goal_3 initPM 11556 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 11556 1838 (by decide) (by decide)).symm
  have h11579 : (denoteGraph_ringAttn pm_goal_3 initPM 11579).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L23_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_23 nR0_23 nR1_23 0 buddy_r0_23 (by decide)]
    have e0 : nR0_23.ins.getD 0 0 = 11555 := by decide
    have e1 : nR1_23.ins.getD 0 0 = 11556 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 0 0),
         (pm_goal_3.nodes.take 1837).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1837_11555, b1837_11556]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h11555d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h11580 : (denoteGraph_ringAttn pm_goal_3 initPM 11580).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L23_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_23 nR0_23 nR1_23 1 buddy_r1_23 (by decide)]
    have e0 : nR0_23.ins.getD 0 0 = 11555 := by decide
    have e1 : nR1_23.ins.getD 0 0 = 11556 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_23.ins.getD 0 0),
         (pm_goal_3.nodes.take 1838).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_23.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1838_11555, b1838_11556]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h11555d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L23_from_attention initSM initPM hInit hcarry5877
    hattn h11579 h11580 h11549 h11550 hw5889

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29).
theorem sm_pm_router_L23_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5885)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L23_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_L23_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5893_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L23_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L23
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L23_from_attention
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L23_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L23_hbound_witness
