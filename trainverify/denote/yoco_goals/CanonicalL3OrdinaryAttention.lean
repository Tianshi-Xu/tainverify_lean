import denote.yoco_goals.L3OrdinaryQKV
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

private theorem l3a_node_core (g : GraphDecl) (init : Store) (k : Nat)
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

private theorem l3a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l3a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l3a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l3a_prefix_read g init k i hpn hpw]

private theorem l3a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l3a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l3a_prefix_read g init k x hpn hpx, l3a_prefix_read g init k y hpn hpy]

private theorem l3a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
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

private theorem l3a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l3a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l3a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l3a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l3a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l3a_init_value (initSM initPM : Store)
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

private theorem l3a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l3SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5110, 5111, 5108, 5112, 5113], outs := [5114, 5115],
    params := [16, 4, 64, 64, 1, 512] }
private def l3PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8286, 8288, 8274, 5112, 5113], outs := [8290, 5115],
    params := [16, 4, 64, 64, 1, 512] }
private def l3PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8287, 8289, 8275, 5112, 5113], outs := [8291, 5115],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l3_sm_sliding_node : sm_goal_1.nodes[126]'(by native_decide) = l3SmSliding := by native_decide
private theorem l3_pm_sliding_node0 : pm_goal_1.nodes[301]'(by native_decide) = l3PmSliding0 := by native_decide
private theorem l3_pm_sliding_node1 : pm_goal_1.nodes[302]'(by native_decide) = l3PmSliding1 := by native_decide
private theorem l3_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l3SmSliding = [l3SmSliding] := by native_decide
private theorem l3_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l3PmSliding0 = [l3PmSliding0, l3PmSliding1] := by native_decide
private theorem l3_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l3PmSliding1 = [l3PmSliding0, l3PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L3 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l3o_raw5114_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5110)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8286) (denoteGraphDistributedFaithful pm_goal_1 initPM 8287)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5111)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8288) (denoteGraphDistributedFaithful pm_goal_1 initPM 8289)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8274) (denoteGraphDistributedFaithful pm_goal_1 initPM 8275)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5112 = denoteGraphDistributedFaithful pm_goal_1 initPM 5112)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5113 = denoteGraphDistributedFaithful pm_goal_1 initPM 5113) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8290) (denoteGraphDistributedFaithful pm_goal_1 initPM 8291)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm_goal_1.nodes.take 126).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm_goal_1.nodes.take 301).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm_goal_1.nodes.take 302).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 126, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 126, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l3a_prefix_read sm_goal_1 initSM 126 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 301, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 301, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l3a_prefix_read pm_goal_1 initPM 301 t hn hw
  have e9434 : fp 8286 = fp' 8286 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 8286 301 302
    (by omega) (by native_decide) (by native_decide)
  have e9435 : fp 8287 = fp' 8287 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 8287 301 302
    (by omega) (by native_decide) (by native_decide)
  have e9436 : fp 8288 = fp' 8288 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 8288 301 302
    (by omega) (by native_decide) (by native_decide)
  have e9437 : fp 8289 = fp' 8289 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 8289 301 302
    (by omega) (by native_decide) (by native_decide)
  have e9422 : fp 8274 = fp' 8274 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 8274 301 302
    (by omega) (by native_decide) (by native_decide)
  have e9423 : fp 8275 = fp' 8275 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 8275 301 302
    (by omega) (by native_decide) (by native_decide)
  have e5497 : fp 5112 = fp' 5112 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 5112 301 302
    (by omega) (by native_decide) (by native_decide)
  have e5498 : fp 5113 = fp' 5113 := l3a_split pm_goal_1 pm_goal_1.nodes initPM 5113 301 302
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5110 = allGatherPrimDimN 0 2 0 [fp 8286, fp 8287] := by
    rw [bs 5110 (by native_decide) (by native_decide), bp 8286 (by native_decide) (by native_decide),
      bp 8287 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5111 = allGatherPrimDimN 0 2 0 [fp 8288, fp 8289] := by
    rw [bs 5111 (by native_decide) (by native_decide), bp 8288 (by native_decide) (by native_decide),
      bp 8289 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 5108 = allGatherPrimDimN 0 2 0 [fp 8274, fp 8275] := by
    rw [bs 5108 (by native_decide) (by native_decide), bp 8274 (by native_decide) (by native_decide),
      bp 8275 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5112 = fp 5112 := by
    rw [bs 5112 (by native_decide) (by native_decide), bp 5112 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5113 = fp 5113 := by
    rw [bs 5113 (by native_decide) (by native_decide), bp 5113 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l3PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l3PmSliding1 := by
    apply l3a_attn_congr
    · rw [l3_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9434
      · exact e9435
    · rw [l3_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9436
      · exact e9437
    · rw [l3_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9422
      · exact e9423
    · exact e5497
    · exact e5498
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5114 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l3SmSliding := by
    rw [l3a_node_core sm_goal_1 initSM 126 l3SmSliding 5114 (by native_decide)
      l3_sm_sliding_node (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l3a_ring_sliding_first_out sm_goal_1 _ 0 5110 5111 5108 5112 5113 5114 5115
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8290 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l3PmSliding0 := by
    rw [l3a_node_core pm_goal_1 initPM 301 l3PmSliding0 8290 (by native_decide)
      l3_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l3a_ring_sliding_first_out pm_goal_1 _ 0 8286 8288 8274 5112 5113 8290 5115
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8291 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l3PmSliding1 := by
    rw [l3a_node_core pm_goal_1 initPM 302 l3PmSliding1 8291 (by native_decide)
      l3_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l3a_ring_sliding_first_out pm_goal_1 _ 1 8287 8289 8275 5112 5113 8291 5115
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8286, fp 8287])
      (allGatherPrimDimN 0 2 0 [fp 8288, fp 8289])
      (allGatherPrimDimN 0 2 0 [fp 8274, fp 8275])
      (fp 5112) (fp 5113) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l3a_attn_shape, ← hqfull, bs 5110 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8286, fp' 8287])
      (allGatherPrimDimN 0 2 0 [fp' 8288, fp' 8289])
      (allGatherPrimDimN 0 2 0 [fp' 8274, fp' 8275])
      (fp' 5112) (fp' 5113) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9434, ← e9435,
      ← e9436, ← e9437,
      ← e9422, ← e9423,
      ← e5497, ← e5498]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l3SmSliding l3PmSliding0 l3PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l3_sm_sliding_buddy l3_pm_sliding_buddy0
    l3_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5110).shape.length; rw [bs 5110 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5111).shape.length; rw [bs 5111 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 5108).shape.length; rw [bs 5108 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 5114 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8290, denoteGraphDistributedFaithful pm_goal_1 initPM 8291] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8290).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l3PmSliding0
      l3PmSliding0 l3PmSliding1 0 l3_pm_sliding_buddy0 (by native_decide)]
    simp only [l3PmSliding0, l3PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8286, fp 8287])
      (allGatherPrimDimN 0 2 0 [fp 8288, fp 8289])
      (allGatherPrimDimN 0 2 0 [fp 8274, fp 8275])
      (fp 5112) (fp 5113) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8291).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l3PmSliding1
      l3PmSliding0 l3PmSliding1 1 l3_pm_sliding_buddy1 (by native_decide)]
    simp only [l3PmSliding0, l3PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8286, fp' 8287])
      (allGatherPrimDimN 0 2 0 [fp' 8288, fp' 8289])
      (allGatherPrimDimN 0 2 0 [fp' 8274, fp' 8275])
      (fp' 5112) (fp' 5113) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l3a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l3a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l3a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l3a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l3a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l3a_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l3a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l3a_reduce1 g init k _ i o id hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l3a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l3a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L3 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l3o_residual5122_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8290) (denoteGraphDistributedFaithful pm_goal_1 initPM 8291)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15538) (denoteGraphDistributedFaithful pm_goal_1 initPM 15546)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8320) (denoteGraphDistributedFaithful pm_goal_1 initPM 8321)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l3a_reshape sm_goal_1 initSM 127 0 5114 5116 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l3a_reshape pm_goal_1 initPM 303 0 8290 8292 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l3a_reshape pm_goal_1 initPM 304 1 8291 8293 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5116) (denoteGraphDistributedFaithful pm_goal_1 initPM 8292)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8293) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r0]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r0, r10]
  have rs1 := l3a_reshape sm_goal_1 initSM 128 0 5116 5117 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l3a_reshape pm_goal_1 initPM 305 0 8292 8298 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l3a_reshape pm_goal_1 initPM 306 1 8293 8299 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5117) (denoteGraphDistributedFaithful pm_goal_1 initPM 8298)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8299) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5117 = denoteGraphDistributedFaithful sm_goal_1 initSM 5116 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8298 = denoteGraphDistributedFaithful pm_goal_1 initPM 8292 := by rw [r1, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8299 = denoteGraphDistributedFaithful pm_goal_1 initPM 8293 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l3a_init_value initSM initPM hInit initGoal_5118
    (by native_decide) 5118 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l3a_init_shape initSM initPM hInit initGoal_5118
    (by native_decide) 5118 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5118).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l3a_linear sm_goal_1 initSM 129 0 5117 5118 5119 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l3a_linear pm_goal_1 initPM 307 0 8298 5118 8302 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l3a_linear pm_goal_1 initPM 308 1 8299 5118 8303 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5119) (denoteGraphDistributedFaithful pm_goal_1 initPM 8302)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8303) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l3a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l3a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l3a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l3a_view sm_goal_1 initSM 130 0 5119 5120 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l3a_view pm_goal_1 initPM 309 0 8302 8312 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l3a_view pm_goal_1 initPM 310 1 8303 8313 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5120) (denoteGraphDistributedFaithful pm_goal_1 initPM 8312)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8313) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5120 = denoteGraphDistributedFaithful sm_goal_1 initSM 5119 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8312 = denoteGraphDistributedFaithful pm_goal_1 initPM 8302 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8313 = denoteGraphDistributedFaithful pm_goal_1 initPM 8303 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l3a_float sm_goal_1 initSM 131 0 5120 5121 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l3a_float pm_goal_1 initPM 311 0 8312 8316 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l3a_float pm_goal_1 initPM 312 1 8313 8317 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5121) (denoteGraphDistributedFaithful pm_goal_1 initPM 8316)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8317) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l3a_add sm_goal_1 initSM 132 0 7904 5121 5122 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l3a_add pm_goal_1 initPM 313 0 15538 8316 8320 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l3a_add pm_goal_1 initPM 314 1 15546 8317 8321 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L3 ordinary attention-to-residual boundary. -/
theorem l3o_residual5122_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5110) (denoteGraphDistributedFaithful pm_goal_1 initPM 8286)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8287) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5111) (denoteGraphDistributedFaithful pm_goal_1 initPM 8288)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8289) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5108) (denoteGraphDistributedFaithful pm_goal_1 initPM 8274)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8275) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5112 = denoteGraphDistributedFaithful pm_goal_1 initPM 5112)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5113 = denoteGraphDistributedFaithful pm_goal_1 initPM 5113)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7904) (denoteGraphDistributedFaithful pm_goal_1 initPM 15538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15546) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5122) (denoteGraphDistributedFaithful pm_goal_1 initPM 8320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8321) [4096,1024] [2048,1024] :=
  l3o_residual5122_rel_of_raw initSM initPM hInit
    (l3o_raw5114_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L3 continuation from the exact incoming residual boundary
`5100 ↔ (8246,8247)`.  Q/K/V remain the explicit internal boundary until the
L3 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l3o_residual5122_rel_from_boundary5100_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8246) (denoteGraphDistributedFaithful pm_goal_1 initPM 8247)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5110)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8286) (denoteGraphDistributedFaithful pm_goal_1 initPM 8287)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5111)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8288) (denoteGraphDistributedFaithful pm_goal_1 initPM 8289)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8274) (denoteGraphDistributedFaithful pm_goal_1 initPM 8275)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8320) (denoteGraphDistributedFaithful pm_goal_1 initPM 8321)
      [4096,1024] [2048,1024] := by
  have ms := l3a_reduce1 sm_goal_1 initSM 119
    { rank := 0, op := "OpName.FW_multiref", ins := [5100], outs := [7900, 7904], params := [2] }
    5100 7904 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l3a_multiref_at sm_goal_1 st 0 5100 [7900, 7904] 2 rfl 7904 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l3a_reduce1 pm_goal_1 initPM 284
    { rank := 0, op := "OpName.FW_multiref", ins := [8246], outs := [15534, 15538], params := [2] }
    8246 15538 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l3a_multiref_at pm_goal_1 st 0 8246 [15534, 15538] 2 rfl 15538 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l3a_reduce1 pm_goal_1 initPM 285
    { rank := 1, op := "OpName.FW_multiref", ins := [8247], outs := [15542, 15546], params := [2] }
    8247 15546 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l3a_multiref_at pm_goal_1 st 1 8247 [15542, 15546] 2 rfl 15546 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15538) (denoteGraphDistributedFaithful pm_goal_1 initPM 15546)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l3a_init_value initSM initPM hInit initGoal_5112
    (by native_decide) 5112 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l3a_init_value initSM initPM hInit initGoal_5113
    (by native_decide) 5113 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l3o_residual5122_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

/-- Unconditional L3 ordinary attention residual reconstruction from the exact
incoming residual boundary: Q, K, and V are derived from their concrete graph
nodes before the sliding-window attention and projection continuation. -/
theorem l3o_residual5122_rel_from_boundary5100
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8246) (denoteGraphDistributedFaithful pm_goal_1 initPM 8247)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8320) (denoteGraphDistributedFaithful pm_goal_1 initPM 8321)
      [4096,1024] [2048,1024] := by
  obtain ⟨hq, hk⟩ := l3o_q5110_k5111_rels_from_boundary initSM initPM hInit hboundary
  have hv := l3o_v5108_rel_from_boundary initSM initPM hInit hboundary
  exact l3o_residual5122_rel_from_boundary5100_of_qkv
    initSM initPM hInit hboundary hq hk hv

end TrainVerify.Denote.GeneratedPatterns
