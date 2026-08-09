import denote.yoco_goals.Goal_1
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

private theorem l10a_node_core (g : GraphDecl) (init : Store) (k : Nat)
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

private theorem l10a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l10a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l10a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l10a_prefix_read g init k i hpn hpw]

private theorem l10a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l10a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l10a_prefix_read g init k x hpn hpx, l10a_prefix_read g init k y hpn hpy]

private theorem l10a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
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

private theorem l10a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l10a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l10a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l10a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l10a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l10a_init_value (initSM initPM : Store)
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

private theorem l10a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l10SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5495, 5496, 5493, 5497, 5498], outs := [5499, 5500],
    params := [16, 4, 64, 64, 1, 512] }
private def l10PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [9434, 9436, 9422, 5497, 5498], outs := [9438, 5500],
    params := [16, 4, 64, 64, 1, 512] }
private def l10PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [9435, 9437, 9423, 5497, 5498], outs := [9439, 5500],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l10_sm_sliding_node : sm_goal_1.nodes[399]'(by native_decide) = l10SmSliding := by native_decide
private theorem l10_pm_sliding_node0 : pm_goal_1.nodes[889]'(by native_decide) = l10PmSliding0 := by native_decide
private theorem l10_pm_sliding_node1 : pm_goal_1.nodes[890]'(by native_decide) = l10PmSliding1 := by native_decide
private theorem l10_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l10SmSliding = [l10SmSliding] := by native_decide
private theorem l10_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l10PmSliding0 = [l10PmSliding0, l10PmSliding1] := by native_decide
private theorem l10_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l10PmSliding1 = [l10PmSliding0, l10PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L10 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l10o_raw5499_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5495)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9434) (denoteGraphDistributedFaithful pm_goal_1 initPM 9435)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5496)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9436) (denoteGraphDistributedFaithful pm_goal_1 initPM 9437)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5493)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9422) (denoteGraphDistributedFaithful pm_goal_1 initPM 9423)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5497 = denoteGraphDistributedFaithful pm_goal_1 initPM 5497)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5498 = denoteGraphDistributedFaithful pm_goal_1 initPM 5498) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5499)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9438) (denoteGraphDistributedFaithful pm_goal_1 initPM 9439)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm.nodes.take 399).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm.nodes.take 889).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm.nodes.take 890).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 399, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 399, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l10a_prefix_read sm_goal_1 initSM 399 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 889, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 889, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l10a_prefix_read pm_goal_1 initPM 889 t hn hw
  have e9434 : fp 9434 = fp' 9434 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 9434 889 890
    (by omega) (by native_decide) (by native_decide)
  have e9435 : fp 9435 = fp' 9435 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 9435 889 890
    (by omega) (by native_decide) (by native_decide)
  have e9436 : fp 9436 = fp' 9436 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 9436 889 890
    (by omega) (by native_decide) (by native_decide)
  have e9437 : fp 9437 = fp' 9437 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 9437 889 890
    (by omega) (by native_decide) (by native_decide)
  have e9422 : fp 9422 = fp' 9422 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 9422 889 890
    (by omega) (by native_decide) (by native_decide)
  have e9423 : fp 9423 = fp' 9423 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 9423 889 890
    (by omega) (by native_decide) (by native_decide)
  have e5497 : fp 5497 = fp' 5497 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 5497 889 890
    (by omega) (by native_decide) (by native_decide)
  have e5498 : fp 5498 = fp' 5498 := l10a_split pm_goal_1 pm_goal_1.nodes initPM 5498 889 890
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5495 = allGatherPrimDimN 0 2 0 [fp 9434, fp 9435] := by
    rw [bs 5495 (by native_decide) (by native_decide), bp 9434 (by native_decide) (by native_decide),
      bp 9435 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5496 = allGatherPrimDimN 0 2 0 [fp 9436, fp 9437] := by
    rw [bs 5496 (by native_decide) (by native_decide), bp 9436 (by native_decide) (by native_decide),
      bp 9437 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 5493 = allGatherPrimDimN 0 2 0 [fp 9422, fp 9423] := by
    rw [bs 5493 (by native_decide) (by native_decide), bp 9422 (by native_decide) (by native_decide),
      bp 9423 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5497 = fp 5497 := by
    rw [bs 5497 (by native_decide) (by native_decide), bp 5497 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5498 = fp 5498 := by
    rw [bs 5498 (by native_decide) (by native_decide), bp 5498 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l10PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l10PmSliding1 := by
    apply l10a_attn_congr
    · rw [l10_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9434
      · exact e9435
    · rw [l10_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9436
      · exact e9437
    · rw [l10_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9422
      · exact e9423
    · exact e5497
    · exact e5498
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5499 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l10SmSliding := by
    rw [l10a_node_core sm_goal_1 initSM 399 l10SmSliding 5499 (by native_decide)
      l10_sm_sliding_node (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l10a_ring_sliding_first_out sm_goal_1 _ 0 5495 5496 5493 5497 5498 5499 5500
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9438 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l10PmSliding0 := by
    rw [l10a_node_core pm_goal_1 initPM 889 l10PmSliding0 9438 (by native_decide)
      l10_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l10a_ring_sliding_first_out pm_goal_1 _ 0 9434 9436 9422 5497 5498 9438 5500
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9439 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l10PmSliding1 := by
    rw [l10a_node_core pm_goal_1 initPM 890 l10PmSliding1 9439 (by native_decide)
      l10_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l10a_ring_sliding_first_out pm_goal_1 _ 1 9435 9437 9423 5497 5498 9439 5500
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9434, fp 9435])
      (allGatherPrimDimN 0 2 0 [fp 9436, fp 9437])
      (allGatherPrimDimN 0 2 0 [fp 9422, fp 9423])
      (fp 5497) (fp 5498) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l10a_attn_shape, ← hqfull, bs 5495 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9434, fp' 9435])
      (allGatherPrimDimN 0 2 0 [fp' 9436, fp' 9437])
      (allGatherPrimDimN 0 2 0 [fp' 9422, fp' 9423])
      (fp' 5497) (fp' 5498) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9434, ← e9435,
      ← e9436, ← e9437,
      ← e9422, ← e9423,
      ← e5497, ← e5498]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l10SmSliding l10PmSliding0 l10PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l10_sm_sliding_buddy l10_pm_sliding_buddy0
    l10_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5495).shape.length; rw [bs 5495 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5496).shape.length; rw [bs 5496 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 5493).shape.length; rw [bs 5493 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 5499 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 9438, denoteGraphDistributedFaithful pm_goal_1 initPM 9439] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9438).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l10PmSliding0
      l10PmSliding0 l10PmSliding1 0 l10_pm_sliding_buddy0 (by native_decide)]
    simp only [l10PmSliding0, l10PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9434, fp 9435])
      (allGatherPrimDimN 0 2 0 [fp 9436, fp 9437])
      (allGatherPrimDimN 0 2 0 [fp 9422, fp 9423])
      (fp 5497) (fp 5498) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9439).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l10PmSliding1
      l10PmSliding0 l10PmSliding1 1 l10_pm_sliding_buddy1 (by native_decide)]
    simp only [l10PmSliding0, l10PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9434, fp' 9435])
      (allGatherPrimDimN 0 2 0 [fp' 9436, fp' 9437])
      (allGatherPrimDimN 0 2 0 [fp' 9422, fp' 9423])
      (fp' 5497) (fp' 5498) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l10a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l10a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l10a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l10a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l10a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l10a_reduce2 g init k _ x w o fw_linear hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l10a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l10a_reduce1 g init k _ i o id hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l10a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l10a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L10 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l10o_residual5507_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5499)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9438) (denoteGraphDistributedFaithful pm_goal_1 initPM 9439)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8268)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15762) (denoteGraphDistributedFaithful pm_goal_1 initPM 15770)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5507)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9468) (denoteGraphDistributedFaithful pm_goal_1 initPM 9469)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l10a_reshape sm_goal_1 initSM 400 0 5499 5501 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r00 := l10a_reshape pm_goal_1 initPM 891 0 9438 9440 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l10a_reshape pm_goal_1 initPM 892 1 9439 9441 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5501) (denoteGraphDistributedFaithful pm_goal_1 initPM 9440)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9441) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r00]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r00, r10]
  have rs1 := l10a_reshape sm_goal_1 initSM 401 0 5501 5502 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r01 := l10a_reshape pm_goal_1 initPM 893 0 9440 9446 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l10a_reshape pm_goal_1 initPM 894 1 9441 9447 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5502) (denoteGraphDistributedFaithful pm_goal_1 initPM 9446)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9447) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5502 = denoteGraphDistributedFaithful sm_goal_1 initSM 5501 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9446 = denoteGraphDistributedFaithful pm_goal_1 initPM 9440 := by rw [r01, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9447 = denoteGraphDistributedFaithful pm_goal_1 initPM 9441 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l10a_init_value initSM initPM hInit initGoal_5503
    (by native_decide) 5503 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l10a_init_shape initSM initPM hInit initGoal_5503
    (by native_decide) 5503 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5503).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l10a_linear sm_goal_1 initSM 402 0 5502 5503 5504 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l10a_linear pm_goal_1 initPM 895 0 9446 5503 9450 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l10a_linear pm_goal_1 initPM 896 1 9447 5503 9451 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5504) (denoteGraphDistributedFaithful pm_goal_1 initPM 9450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9451) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l10a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l10a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l10a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l10a_view sm_goal_1 initSM 403 0 5504 5505 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l10a_view pm_goal_1 initPM 897 0 9450 9460 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l10a_view pm_goal_1 initPM 898 1 9451 9461 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5505) (denoteGraphDistributedFaithful pm_goal_1 initPM 9460)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9461) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5505 = denoteGraphDistributedFaithful sm_goal_1 initSM 5504 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9460 = denoteGraphDistributedFaithful pm_goal_1 initPM 9450 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9461 = denoteGraphDistributedFaithful pm_goal_1 initPM 9451 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l10a_float sm_goal_1 initSM 404 0 5505 5506 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l10a_float pm_goal_1 initPM 899 0 9460 9464 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l10a_float pm_goal_1 initPM 900 1 9461 9465 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5506) (denoteGraphDistributedFaithful pm_goal_1 initPM 9464)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9465) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l10a_add sm_goal_1 initSM 405 0 8268 5506 5507 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l10a_add pm_goal_1 initPM 901 0 15762 9464 9468 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l10a_add pm_goal_1 initPM 902 1 15770 9465 9469 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L10 ordinary attention-to-residual boundary. -/
theorem l10o_residual5507_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5495) (denoteGraphDistributedFaithful pm_goal_1 initPM 9434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9435) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5496) (denoteGraphDistributedFaithful pm_goal_1 initPM 9436)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9437) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5493) (denoteGraphDistributedFaithful pm_goal_1 initPM 9422)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9423) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5497 = denoteGraphDistributedFaithful pm_goal_1 initPM 5497)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5498 = denoteGraphDistributedFaithful pm_goal_1 initPM 5498)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8268) (denoteGraphDistributedFaithful pm_goal_1 initPM 15762)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15770) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5507) (denoteGraphDistributedFaithful pm_goal_1 initPM 9468)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9469) [4096,1024] [2048,1024] :=
  l10o_residual5507_rel_of_raw initSM initPM hInit
    (l10o_raw5499_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L10 continuation from the exact incoming residual boundary
`5485 ↔ (9394,9395)`.  Q/K/V remain the explicit internal boundary until the
L10 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l10o_residual5507_rel_from_boundary5485_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5485)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9394) (denoteGraphDistributedFaithful pm_goal_1 initPM 9395)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5495)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9434) (denoteGraphDistributedFaithful pm_goal_1 initPM 9435)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5496)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9436) (denoteGraphDistributedFaithful pm_goal_1 initPM 9437)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5493)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9422) (denoteGraphDistributedFaithful pm_goal_1 initPM 9423)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5507)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9468) (denoteGraphDistributedFaithful pm_goal_1 initPM 9469)
      [4096,1024] [2048,1024] := by
  have ms := l10a_reduce1 sm_goal_1 initSM 392
    { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8264, 8268], params := [2] }
    5485 8268 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l10a_multiref_at sm_goal_1 st 0 5485 [8264, 8268] 2 rfl 8268 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10a_reduce1 pm_goal_1 initPM 872
    { rank := 0, op := "OpName.FW_multiref", ins := [9394], outs := [15758, 15762], params := [2] }
    9394 15762 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l10a_multiref_at pm_goal_1 st 0 9394 [15758, 15762] 2 rfl 15762 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10a_reduce1 pm_goal_1 initPM 873
    { rank := 1, op := "OpName.FW_multiref", ins := [9395], outs := [15766, 15770], params := [2] }
    9395 15770 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l10a_multiref_at pm_goal_1 st 1 9395 [15766, 15770] 2 rfl 15770 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8268)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15762) (denoteGraphDistributedFaithful pm_goal_1 initPM 15770)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l10a_init_value initSM initPM hInit initGoal_5497
    (by native_decide) 5497 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l10a_init_value initSM initPM hInit initGoal_5498
    (by native_decide) 5498 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l10o_residual5507_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

end TrainVerify.Denote.GeneratedPatterns
