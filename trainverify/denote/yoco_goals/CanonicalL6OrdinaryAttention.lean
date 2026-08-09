import denote.yoco_goals.L6OrdinaryQKV
import denote.yoco_goals.CanonicalKVCacheOrdinaryOps
import denote.ChunkGatherDim0
import denote.DenoteMoE
import denote.MultirefGeneral
import denote.GraphGears
import denote.Gather2Rel
import denote.SlidingWindowReconstruction
import denote.yoco_goals.RingAttnGears
import denote.yoco_goals.ZigzagPointwiseRel

set_option linter.style.longLine false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l6a_node_core (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid) (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node) (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hshuffle : node.op ≠ "OpName.FW_maybe_shuffle")
    (hunshuffle : node.op ≠ "OpName.FW_maybe_unshuffle")
    (hattn : node.op ≠ "OpName.FW_attn_zigzag")
    (hnil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      applyNodeRingAttn g ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) node outTid := by
  rw [denoteGraphDistributedFaithful_eq_prefix g init outTid (k + 1) hnil hw]
  have hstep := congrFun (foldl_take_succ (applyNodeDistributedFaithful g) g.nodes init k hk) outTid
  rw [hstep, hnode]
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    g _ node hshuffle hunshuffle hattn]
  unfold applyNodeDistributed
  rw [if_neg hmoe]

private theorem l6a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l6a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (i o : Tid) (f : Tensor → Tensor)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hm : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hshuffle : node.op ≠ "OpName.FW_maybe_shuffle")
    (hunshuffle : node.op ≠ "OpName.FW_maybe_unshuffle")
    (hattn : node.op ≠ "OpName.FW_attn_zigzag")
    (ha : ∀ s, applyNodeRingAttn g s node o = f (s i))
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = f (denoteGraphDistributedFaithful g init i) := by
  rw [l6a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l6a_prefix_read g init k i hpn hpw]

private theorem l6a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (x y o : Tid) (f : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hm : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hshuffle : node.op ≠ "OpName.FW_maybe_shuffle")
    (hunshuffle : node.op ≠ "OpName.FW_maybe_unshuffle")
    (hattn : node.op ≠ "OpName.FW_attn_zigzag")
    (ha : ∀ s, applyNodeRingAttn g s node o = f (s x) (s y))
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = f (denoteGraphDistributedFaithful g init x)
      (denoteGraphDistributedFaithful g init y) := by
  rw [l6a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l6a_prefix_read g init k x hpn hpx, l6a_prefix_read g init k y hpn hpy]

private theorem l6a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
    (tid j k : Nat) (hjk : j ≤ k)
    (hnil : ((nodes.take k).drop j).all (fun n => !n.outs.isEmpty) = true)
    (hw : ((nodes.take k).drop j).all (fun n => !n.outs.contains tid) = true) :
    (nodes.take j).foldl (applyNodeDistributedFaithful g) s tid =
      (nodes.take k).foldl (applyNodeDistributedFaithful g) s tid := by
  have hnil' : ∀ n ∈ (nodes.take k).drop j, n.outs ≠ [] := by
    intro n hn; simpa using (List.all_eq_true.mp hnil n hn)
  have hw' : ∀ n ∈ (nodes.take k).drop j, tid ∉ n.outs := by
    intro n hn; simpa using (List.all_eq_true.mp hw n hn)
  have hs : nodes.take k = nodes.take j ++ (nodes.take k).drop j := by
    rw [show nodes.take j = (nodes.take k).take j by rw [List.take_take, min_eq_left hjk]]
    rw [List.take_append_drop]
  rw [hs, List.foldl_append]
  exact (foldl_applyNodeDistributedFaithful_at_not_written g _ _ tid hnil' hw').symm

private theorem l6a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l6a_ring_sliding_first_out (g : GraphDecl) (s : Store)
    (rank q k v cuQ cuK out aux : Nat) (params : List Nat) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_attn_sliding_window",
        ins := [q, k, v, cuQ, cuK], outs := [out, aux], params := params } out =
      applyNodeRingAttn_sliding_window g s
        { rank := rank, op := "OpName.FW_attn_sliding_window",
          ins := [q, k, v, cuQ, cuK], outs := [out, aux], params := params } := by
  unfold applyNodeRingAttn
  rw [if_neg (by simp), if_pos rfl]
  change storeSet s [(out, _)] out = _
  unfold storeSet
  simp [List.find?]

private theorem l6a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l6a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l6a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l6a_init_value (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid)
    (htp : gW.tps = [{ rank := 0, tid := W }]) (hgd : gW.gatherDim = 0)
    (hr : gW.replicated = false) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM W = denoteGraphDistributedFaithful pm_goal_1 initPM W := by
  have h := hInit gW hg
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hr, htp, hts, hgd] at hv
  simp only [List.map, reconstructWithDim] at hv
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, denoteGraphDistributedFaithful,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM W (by native_decide) hpm]
  exact hv

private theorem l6a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l6SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5275, 5276, 5273, 5277, 5278], outs := [5279, 5280],
    params := [16, 4, 64, 64, 1, 512] }
private def l6PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8778, 8780, 8766, 5277, 5278], outs := [8782, 5280],
    params := [16, 4, 64, 64, 1, 512] }
private def l6PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8779, 8781, 8767, 5277, 5278], outs := [8783, 5280],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l6_sm_sliding_node : sm_goal_1.nodes[243]'(by native_decide) = l6SmSliding := by native_decide
private theorem l6_pm_sliding_node0 : pm_goal_1.nodes[553]'(by native_decide) = l6PmSliding0 := by native_decide
private theorem l6_pm_sliding_node1 : pm_goal_1.nodes[554]'(by native_decide) = l6PmSliding1 := by native_decide
private theorem l6_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l6SmSliding = [l6SmSliding] := by native_decide
private theorem l6_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l6PmSliding0 = [l6PmSliding0, l6PmSliding1] := by native_decide
private theorem l6_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l6PmSliding1 = [l6PmSliding0, l6PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L6 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l6o_raw5279_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5275)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8778) (denoteGraphDistributedFaithful pm_goal_1 initPM 8779)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8780) (denoteGraphDistributedFaithful pm_goal_1 initPM 8781)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5273)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8766) (denoteGraphDistributedFaithful pm_goal_1 initPM 8767)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5277 = denoteGraphDistributedFaithful pm_goal_1 initPM 5277)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5278 = denoteGraphDistributedFaithful pm_goal_1 initPM 5278) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5279)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8782) (denoteGraphDistributedFaithful pm_goal_1 initPM 8783)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm_goal_1.nodes.take 243).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm_goal_1.nodes.take 553).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm_goal_1.nodes.take 554).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 243, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 243, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l6a_prefix_read sm_goal_1 initSM 243 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 553, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 553, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l6a_prefix_read pm_goal_1 initPM 553 t hn hw
  have e9434 : fp 8778 = fp' 8778 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 8778 553 554
    (by omega) (by native_decide) (by native_decide)
  have e9435 : fp 8779 = fp' 8779 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 8779 553 554
    (by omega) (by native_decide) (by native_decide)
  have e9436 : fp 8780 = fp' 8780 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 8780 553 554
    (by omega) (by native_decide) (by native_decide)
  have e9437 : fp 8781 = fp' 8781 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 8781 553 554
    (by omega) (by native_decide) (by native_decide)
  have e9422 : fp 8766 = fp' 8766 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 8766 553 554
    (by omega) (by native_decide) (by native_decide)
  have e9423 : fp 8767 = fp' 8767 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 8767 553 554
    (by omega) (by native_decide) (by native_decide)
  have e5497 : fp 5277 = fp' 5277 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 5277 553 554
    (by omega) (by native_decide) (by native_decide)
  have e5498 : fp 5278 = fp' 5278 := l6a_split pm_goal_1 pm_goal_1.nodes initPM 5278 553 554
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5275 = allGatherPrimDimN 0 2 0 [fp 8778, fp 8779] := by
    rw [bs 5275 (by native_decide) (by native_decide), bp 8778 (by native_decide) (by native_decide),
      bp 8779 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5276 = allGatherPrimDimN 0 2 0 [fp 8780, fp 8781] := by
    rw [bs 5276 (by native_decide) (by native_decide), bp 8780 (by native_decide) (by native_decide),
      bp 8781 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 5273 = allGatherPrimDimN 0 2 0 [fp 8766, fp 8767] := by
    rw [bs 5273 (by native_decide) (by native_decide), bp 8766 (by native_decide) (by native_decide),
      bp 8767 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5277 = fp 5277 := by
    rw [bs 5277 (by native_decide) (by native_decide), bp 5277 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5278 = fp 5278 := by
    rw [bs 5278 (by native_decide) (by native_decide), bp 5278 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l6PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l6PmSliding1 := by
    apply l6a_attn_congr
    · rw [l6_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9434
      · exact e9435
    · rw [l6_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9436
      · exact e9437
    · rw [l6_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9422
      · exact e9423
    · exact e5497
    · exact e5498
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5279 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l6SmSliding := by
    rw [l6a_node_core sm_goal_1 initSM 243 l6SmSliding 5279 (by native_decide)
      l6_sm_sliding_node (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l6a_ring_sliding_first_out sm_goal_1 _ 0 5275 5276 5273 5277 5278 5279 5280
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8782 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l6PmSliding0 := by
    rw [l6a_node_core pm_goal_1 initPM 553 l6PmSliding0 8782 (by native_decide)
      l6_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l6a_ring_sliding_first_out pm_goal_1 _ 0 8778 8780 8766 5277 5278 8782 5280
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8783 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l6PmSliding1 := by
    rw [l6a_node_core pm_goal_1 initPM 554 l6PmSliding1 8783 (by native_decide)
      l6_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l6a_ring_sliding_first_out pm_goal_1 _ 1 8779 8781 8767 5277 5278 8783 5280
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8778, fp 8779])
      (allGatherPrimDimN 0 2 0 [fp 8780, fp 8781])
      (allGatherPrimDimN 0 2 0 [fp 8766, fp 8767])
      (fp 5277) (fp 5278) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l6a_attn_shape, ← hqfull, bs 5275 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8778, fp' 8779])
      (allGatherPrimDimN 0 2 0 [fp' 8780, fp' 8781])
      (allGatherPrimDimN 0 2 0 [fp' 8766, fp' 8767])
      (fp' 5277) (fp' 5278) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9434, ← e9435,
      ← e9436, ← e9437,
      ← e9422, ← e9423,
      ← e5497, ← e5498]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l6SmSliding l6PmSliding0 l6PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l6_sm_sliding_buddy l6_pm_sliding_buddy0
    l6_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5275).shape.length; rw [bs 5275 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5276).shape.length; rw [bs 5276 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 5273).shape.length; rw [bs 5273 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 5279 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8782, denoteGraphDistributedFaithful pm_goal_1 initPM 8783] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8782).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l6PmSliding0
      l6PmSliding0 l6PmSliding1 0 l6_pm_sliding_buddy0 (by native_decide)]
    simp only [l6PmSliding0, l6PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8778, fp 8779])
      (allGatherPrimDimN 0 2 0 [fp 8780, fp 8781])
      (allGatherPrimDimN 0 2 0 [fp 8766, fp 8767])
      (fp 5277) (fp 5278) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8783).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l6PmSliding1
      l6PmSliding0 l6PmSliding1 1 l6_pm_sliding_buddy1 (by native_decide)]
    simp only [l6PmSliding0, l6PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8778, fp' 8779])
      (allGatherPrimDimN 0 2 0 [fp' 8780, fp' 8781])
      (allGatherPrimDimN 0 2 0 [fp' 8766, fp' 8767])
      (fp' 5277) (fp' 5278) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l6a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l6a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l6a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l6a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l6a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l6a_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l6a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l6a_reduce1 g init k _ i o id hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l6a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l6a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L6 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l6o_residual5287_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5279)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8782) (denoteGraphDistributedFaithful pm_goal_1 initPM 8783)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15634) (denoteGraphDistributedFaithful pm_goal_1 initPM 15642)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8812) (denoteGraphDistributedFaithful pm_goal_1 initPM 8813)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l6a_reshape sm_goal_1 initSM 244 0 5279 5281 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6a_reshape pm_goal_1 initPM 555 0 8782 8784 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l6a_reshape pm_goal_1 initPM 556 1 8783 8785 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5281) (denoteGraphDistributedFaithful pm_goal_1 initPM 8784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8785) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r0]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r0, r10]
  have rs1 := l6a_reshape sm_goal_1 initSM 245 0 5281 5282 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6a_reshape pm_goal_1 initPM 557 0 8784 8790 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l6a_reshape pm_goal_1 initPM 558 1 8785 8791 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5282) (denoteGraphDistributedFaithful pm_goal_1 initPM 8790)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8791) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5282 = denoteGraphDistributedFaithful sm_goal_1 initSM 5281 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8790 = denoteGraphDistributedFaithful pm_goal_1 initPM 8784 := by rw [r1, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8791 = denoteGraphDistributedFaithful pm_goal_1 initPM 8785 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l6a_init_value initSM initPM hInit initGoal_5283
    (by native_decide) 5283 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l6a_init_shape initSM initPM hInit initGoal_5283
    (by native_decide) 5283 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5283).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l6a_linear sm_goal_1 initSM 246 0 5282 5283 5284 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l6a_linear pm_goal_1 initPM 559 0 8790 5283 8794 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l6a_linear pm_goal_1 initPM 560 1 8791 5283 8795 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5284) (denoteGraphDistributedFaithful pm_goal_1 initPM 8794)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8795) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l6a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l6a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l6a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l6a_view sm_goal_1 initSM 247 0 5284 5285 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l6a_view pm_goal_1 initPM 561 0 8794 8804 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l6a_view pm_goal_1 initPM 562 1 8795 8805 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5285) (denoteGraphDistributedFaithful pm_goal_1 initPM 8804)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8805) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5285 = denoteGraphDistributedFaithful sm_goal_1 initSM 5284 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8804 = denoteGraphDistributedFaithful pm_goal_1 initPM 8794 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8805 = denoteGraphDistributedFaithful pm_goal_1 initPM 8795 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l6a_float sm_goal_1 initSM 248 0 5285 5286 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l6a_float pm_goal_1 initPM 563 0 8804 8808 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l6a_float pm_goal_1 initPM 564 1 8805 8809 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5286) (denoteGraphDistributedFaithful pm_goal_1 initPM 8808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8809) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l6a_add sm_goal_1 initSM 249 0 8060 5286 5287 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l6a_add pm_goal_1 initPM 565 0 15634 8808 8812 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l6a_add pm_goal_1 initPM 566 1 15642 8809 8813 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L6 ordinary attention-to-residual boundary. -/
theorem l6o_residual5287_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5275) (denoteGraphDistributedFaithful pm_goal_1 initPM 8778)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8779) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5276) (denoteGraphDistributedFaithful pm_goal_1 initPM 8780)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8781) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5273) (denoteGraphDistributedFaithful pm_goal_1 initPM 8766)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8767) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5277 = denoteGraphDistributedFaithful pm_goal_1 initPM 5277)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5278 = denoteGraphDistributedFaithful pm_goal_1 initPM 5278)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8060) (denoteGraphDistributedFaithful pm_goal_1 initPM 15634)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15642) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5287) (denoteGraphDistributedFaithful pm_goal_1 initPM 8812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8813) [4096,1024] [2048,1024] :=
  l6o_residual5287_rel_of_raw initSM initPM hInit
    (l6o_raw5279_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L6 continuation from the exact incoming residual boundary
`5265 ↔ (8738,8739)`.  Q/K/V remain the explicit internal boundary until the
L6 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l6o_residual5287_rel_from_boundary5265_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5265)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8738) (denoteGraphDistributedFaithful pm_goal_1 initPM 8739)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5275)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8778) (denoteGraphDistributedFaithful pm_goal_1 initPM 8779)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8780) (denoteGraphDistributedFaithful pm_goal_1 initPM 8781)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5273)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8766) (denoteGraphDistributedFaithful pm_goal_1 initPM 8767)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8812) (denoteGraphDistributedFaithful pm_goal_1 initPM 8813)
      [4096,1024] [2048,1024] := by
  have ms := l6a_reduce1 sm_goal_1 initSM 236
    { rank := 0, op := "OpName.FW_multiref", ins := [5265], outs := [8056, 8060], params := [2] }
    5265 8060 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l6a_multiref_at sm_goal_1 st 0 5265 [8056, 8060] 2 rfl 8060 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l6a_reduce1 pm_goal_1 initPM 536
    { rank := 0, op := "OpName.FW_multiref", ins := [8738], outs := [15630, 15634], params := [2] }
    8738 15634 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l6a_multiref_at pm_goal_1 st 0 8738 [15630, 15634] 2 rfl 15634 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l6a_reduce1 pm_goal_1 initPM 537
    { rank := 1, op := "OpName.FW_multiref", ins := [8739], outs := [15638, 15642], params := [2] }
    8739 15642 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l6a_multiref_at pm_goal_1 st 1 8739 [15638, 15642] 2 rfl 15642 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15634) (denoteGraphDistributedFaithful pm_goal_1 initPM 15642)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l6a_init_value initSM initPM hInit initGoal_5277
    (by native_decide) 5277 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l6a_init_value initSM initPM hInit initGoal_5278
    (by native_decide) 5278 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l6o_residual5287_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

/-- Unconditional L6 ordinary attention residual reconstruction from the exact
incoming residual boundary: Q, K, and V are derived from their concrete graph
nodes before the sliding-window attention and projection continuation. -/
theorem l6o_residual5287_rel_from_boundary5265
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5265)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8738) (denoteGraphDistributedFaithful pm_goal_1 initPM 8739)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8812) (denoteGraphDistributedFaithful pm_goal_1 initPM 8813)
      [4096,1024] [2048,1024] := by
  obtain ⟨hq, hk⟩ := l6o_q5275_k5276_rels_from_boundary initSM initPM hInit hboundary
  have hv := l6o_v5273_rel_from_boundary initSM initPM hInit hboundary
  exact l6o_residual5287_rel_from_boundary5265_of_qkv
    initSM initPM hInit hboundary hq hk hv

end TrainVerify.Denote.GeneratedPatterns
