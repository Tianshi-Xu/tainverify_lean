import denote.yoco_goals.L8OrdinaryQKV
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

private theorem l8a_node_core (g : GraphDecl) (init : Store) (k : Nat)
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

private theorem l8a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l8a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l8a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l8a_prefix_read g init k i hpn hpw]

private theorem l8a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l8a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l8a_prefix_read g init k x hpn hpx, l8a_prefix_read g init k y hpn hpy]

private theorem l8a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
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

private theorem l8a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l8a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l8a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l8a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l8a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l8a_init_value (initSM initPM : Store)
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

private theorem l8a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l8SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5385, 5386, 5383, 5387, 5388], outs := [5389, 5390],
    params := [16, 4, 64, 64, 1, 512] }
private def l8PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [9106, 9108, 9094, 5387, 5388], outs := [9110, 5390],
    params := [16, 4, 64, 64, 1, 512] }
private def l8PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [9107, 9109, 9095, 5387, 5388], outs := [9111, 5390],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l8_sm_sliding_node : sm_goal_1.nodes[321]'(by native_decide) = l8SmSliding := by native_decide
private theorem l8_pm_sliding_node0 : pm_goal_1.nodes[721]'(by native_decide) = l8PmSliding0 := by native_decide
private theorem l8_pm_sliding_node1 : pm_goal_1.nodes[722]'(by native_decide) = l8PmSliding1 := by native_decide
private theorem l8_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l8SmSliding = [l8SmSliding] := by native_decide
private theorem l8_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l8PmSliding0 = [l8PmSliding0, l8PmSliding1] := by native_decide
private theorem l8_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l8PmSliding1 = [l8PmSliding0, l8PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L8 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l8o_raw5389_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5385)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9106) (denoteGraphDistributedFaithful pm_goal_1 initPM 9107)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5386)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9108) (denoteGraphDistributedFaithful pm_goal_1 initPM 9109)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5383)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9094) (denoteGraphDistributedFaithful pm_goal_1 initPM 9095)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5387 = denoteGraphDistributedFaithful pm_goal_1 initPM 5387)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5388 = denoteGraphDistributedFaithful pm_goal_1 initPM 5388) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5389)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9110) (denoteGraphDistributedFaithful pm_goal_1 initPM 9111)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm_goal_1.nodes.take 321).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm_goal_1.nodes.take 721).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm_goal_1.nodes.take 722).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 321, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 321, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l8a_prefix_read sm_goal_1 initSM 321 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 721, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 721, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l8a_prefix_read pm_goal_1 initPM 721 t hn hw
  have e9434 : fp 9106 = fp' 9106 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 9106 721 722
    (by omega) (by native_decide) (by native_decide)
  have e9435 : fp 9107 = fp' 9107 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 9107 721 722
    (by omega) (by native_decide) (by native_decide)
  have e9436 : fp 9108 = fp' 9108 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 9108 721 722
    (by omega) (by native_decide) (by native_decide)
  have e9437 : fp 9109 = fp' 9109 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 9109 721 722
    (by omega) (by native_decide) (by native_decide)
  have e9422 : fp 9094 = fp' 9094 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 9094 721 722
    (by omega) (by native_decide) (by native_decide)
  have e9423 : fp 9095 = fp' 9095 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 9095 721 722
    (by omega) (by native_decide) (by native_decide)
  have e5497 : fp 5387 = fp' 5387 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 5387 721 722
    (by omega) (by native_decide) (by native_decide)
  have e5498 : fp 5388 = fp' 5388 := l8a_split pm_goal_1 pm_goal_1.nodes initPM 5388 721 722
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5385 = allGatherPrimDimN 0 2 0 [fp 9106, fp 9107] := by
    rw [bs 5385 (by native_decide) (by native_decide), bp 9106 (by native_decide) (by native_decide),
      bp 9107 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5386 = allGatherPrimDimN 0 2 0 [fp 9108, fp 9109] := by
    rw [bs 5386 (by native_decide) (by native_decide), bp 9108 (by native_decide) (by native_decide),
      bp 9109 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 5383 = allGatherPrimDimN 0 2 0 [fp 9094, fp 9095] := by
    rw [bs 5383 (by native_decide) (by native_decide), bp 9094 (by native_decide) (by native_decide),
      bp 9095 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5387 = fp 5387 := by
    rw [bs 5387 (by native_decide) (by native_decide), bp 5387 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5388 = fp 5388 := by
    rw [bs 5388 (by native_decide) (by native_decide), bp 5388 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l8PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l8PmSliding1 := by
    apply l8a_attn_congr
    · rw [l8_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9434
      · exact e9435
    · rw [l8_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9436
      · exact e9437
    · rw [l8_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9422
      · exact e9423
    · exact e5497
    · exact e5498
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5389 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l8SmSliding := by
    rw [l8a_node_core sm_goal_1 initSM 321 l8SmSliding 5389 (by native_decide)
      l8_sm_sliding_node (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l8a_ring_sliding_first_out sm_goal_1 _ 0 5385 5386 5383 5387 5388 5389 5390
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9110 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l8PmSliding0 := by
    rw [l8a_node_core pm_goal_1 initPM 721 l8PmSliding0 9110 (by native_decide)
      l8_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l8a_ring_sliding_first_out pm_goal_1 _ 0 9106 9108 9094 5387 5388 9110 5390
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9111 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l8PmSliding1 := by
    rw [l8a_node_core pm_goal_1 initPM 722 l8PmSliding1 9111 (by native_decide)
      l8_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l8a_ring_sliding_first_out pm_goal_1 _ 1 9107 9109 9095 5387 5388 9111 5390
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9106, fp 9107])
      (allGatherPrimDimN 0 2 0 [fp 9108, fp 9109])
      (allGatherPrimDimN 0 2 0 [fp 9094, fp 9095])
      (fp 5387) (fp 5388) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l8a_attn_shape, ← hqfull, bs 5385 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9106, fp' 9107])
      (allGatherPrimDimN 0 2 0 [fp' 9108, fp' 9109])
      (allGatherPrimDimN 0 2 0 [fp' 9094, fp' 9095])
      (fp' 5387) (fp' 5388) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9434, ← e9435,
      ← e9436, ← e9437,
      ← e9422, ← e9423,
      ← e5497, ← e5498]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l8SmSliding l8PmSliding0 l8PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l8_sm_sliding_buddy l8_pm_sliding_buddy0
    l8_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5385).shape.length; rw [bs 5385 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5386).shape.length; rw [bs 5386 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 5383).shape.length; rw [bs 5383 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 5389 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 9110, denoteGraphDistributedFaithful pm_goal_1 initPM 9111] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9110).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l8PmSliding0
      l8PmSliding0 l8PmSliding1 0 l8_pm_sliding_buddy0 (by native_decide)]
    simp only [l8PmSliding0, l8PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9106, fp 9107])
      (allGatherPrimDimN 0 2 0 [fp 9108, fp 9109])
      (allGatherPrimDimN 0 2 0 [fp 9094, fp 9095])
      (fp 5387) (fp 5388) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9111).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l8PmSliding1
      l8PmSliding0 l8PmSliding1 1 l8_pm_sliding_buddy1 (by native_decide)]
    simp only [l8PmSliding0, l8PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9106, fp' 9107])
      (allGatherPrimDimN 0 2 0 [fp' 9108, fp' 9109])
      (allGatherPrimDimN 0 2 0 [fp' 9094, fp' 9095])
      (fp' 5387) (fp' 5388) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l8a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l8a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l8a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l8a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l8a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l8a_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l8a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l8a_reduce1 g init k _ i o id hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l8a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l8a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L8 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l8o_residual5397_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5389)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9110) (denoteGraphDistributedFaithful pm_goal_1 initPM 9111)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15698) (denoteGraphDistributedFaithful pm_goal_1 initPM 15706)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140) (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l8a_reshape sm_goal_1 initSM 322 0 5389 5391 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8a_reshape pm_goal_1 initPM 723 0 9110 9112 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l8a_reshape pm_goal_1 initPM 724 1 9111 9113 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5391) (denoteGraphDistributedFaithful pm_goal_1 initPM 9112)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9113) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r0]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r0, r10]
  have rs1 := l8a_reshape sm_goal_1 initSM 323 0 5391 5392 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8a_reshape pm_goal_1 initPM 725 0 9112 9118 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l8a_reshape pm_goal_1 initPM 726 1 9113 9119 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5392) (denoteGraphDistributedFaithful pm_goal_1 initPM 9118)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9119) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5392 = denoteGraphDistributedFaithful sm_goal_1 initSM 5391 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9118 = denoteGraphDistributedFaithful pm_goal_1 initPM 9112 := by rw [r1, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9119 = denoteGraphDistributedFaithful pm_goal_1 initPM 9113 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l8a_init_value initSM initPM hInit initGoal_5393
    (by native_decide) 5393 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l8a_init_shape initSM initPM hInit initGoal_5393
    (by native_decide) 5393 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5393).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l8a_linear sm_goal_1 initSM 324 0 5392 5393 5394 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l8a_linear pm_goal_1 initPM 727 0 9118 5393 9122 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l8a_linear pm_goal_1 initPM 728 1 9119 5393 9123 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5394) (denoteGraphDistributedFaithful pm_goal_1 initPM 9122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9123) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l8a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l8a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l8a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l8a_view sm_goal_1 initSM 325 0 5394 5395 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l8a_view pm_goal_1 initPM 729 0 9122 9132 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l8a_view pm_goal_1 initPM 730 1 9123 9133 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5395) (denoteGraphDistributedFaithful pm_goal_1 initPM 9132)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9133) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5395 = denoteGraphDistributedFaithful sm_goal_1 initSM 5394 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9132 = denoteGraphDistributedFaithful pm_goal_1 initPM 9122 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9133 = denoteGraphDistributedFaithful pm_goal_1 initPM 9123 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l8a_float sm_goal_1 initSM 326 0 5395 5396 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l8a_float pm_goal_1 initPM 731 0 9132 9136 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l8a_float pm_goal_1 initPM 732 1 9133 9137 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5396) (denoteGraphDistributedFaithful pm_goal_1 initPM 9136)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9137) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l8a_add sm_goal_1 initSM 327 0 8164 5396 5397 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l8a_add pm_goal_1 initPM 733 0 15698 9136 9140 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l8a_add pm_goal_1 initPM 734 1 15706 9137 9141 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L8 ordinary attention-to-residual boundary. -/
theorem l8o_residual5397_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5385) (denoteGraphDistributedFaithful pm_goal_1 initPM 9106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9107) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5386) (denoteGraphDistributedFaithful pm_goal_1 initPM 9108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9109) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5383) (denoteGraphDistributedFaithful pm_goal_1 initPM 9094)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9095) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5387 = denoteGraphDistributedFaithful pm_goal_1 initPM 5387)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5388 = denoteGraphDistributedFaithful pm_goal_1 initPM 5388)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8164) (denoteGraphDistributedFaithful pm_goal_1 initPM 15698)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15706) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5397) (denoteGraphDistributedFaithful pm_goal_1 initPM 9140)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9141) [4096,1024] [2048,1024] :=
  l8o_residual5397_rel_of_raw initSM initPM hInit
    (l8o_raw5389_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L8 continuation from the exact incoming residual boundary
`5375 ↔ (9066,9067)`.  Q/K/V remain the explicit internal boundary until the
L8 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l8o_residual5397_rel_from_boundary5375_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5375)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9066) (denoteGraphDistributedFaithful pm_goal_1 initPM 9067)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5385)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9106) (denoteGraphDistributedFaithful pm_goal_1 initPM 9107)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5386)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9108) (denoteGraphDistributedFaithful pm_goal_1 initPM 9109)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5383)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9094) (denoteGraphDistributedFaithful pm_goal_1 initPM 9095)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140) (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096,1024] [2048,1024] := by
  have ms := l8a_reduce1 sm_goal_1 initSM 314
    { rank := 0, op := "OpName.FW_multiref", ins := [5375], outs := [8160, 8164], params := [2] }
    5375 8164 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l8a_multiref_at sm_goal_1 st 0 5375 [8160, 8164] 2 rfl 8164 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l8a_reduce1 pm_goal_1 initPM 704
    { rank := 0, op := "OpName.FW_multiref", ins := [9066], outs := [15694, 15698], params := [2] }
    9066 15698 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l8a_multiref_at pm_goal_1 st 0 9066 [15694, 15698] 2 rfl 15698 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l8a_reduce1 pm_goal_1 initPM 705
    { rank := 1, op := "OpName.FW_multiref", ins := [9067], outs := [15702, 15706], params := [2] }
    9067 15706 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l8a_multiref_at pm_goal_1 st 1 9067 [15702, 15706] 2 rfl 15706 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15698) (denoteGraphDistributedFaithful pm_goal_1 initPM 15706)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l8a_init_value initSM initPM hInit initGoal_5387
    (by native_decide) 5387 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l8a_init_value initSM initPM hInit initGoal_5388
    (by native_decide) 5388 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l8o_residual5397_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

/-- Unconditional L8 ordinary attention residual reconstruction from the exact
incoming residual boundary: Q, K, and V are derived from their concrete graph
nodes before the sliding-window attention and projection continuation. -/
theorem l8o_residual5397_rel_from_boundary5375
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5375)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9066) (denoteGraphDistributedFaithful pm_goal_1 initPM 9067)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140) (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096,1024] [2048,1024] := by
  obtain ⟨hq, hk⟩ := l8o_q5385_k5386_rels_from_boundary initSM initPM hInit hboundary
  have hv := l8o_v5383_rel_from_boundary initSM initPM hInit hboundary
  exact l8o_residual5397_rel_from_boundary5375_of_qkv
    initSM initPM hInit hboundary hq hk hv

end TrainVerify.Denote.GeneratedPatterns
