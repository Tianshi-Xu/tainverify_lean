import denote.yoco_goals.L5OrdinaryQKV
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

private theorem l5a_node_core (g : GraphDecl) (init : Store) (k : Nat)
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

private theorem l5a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l5a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l5a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l5a_prefix_read g init k i hpn hpw]

private theorem l5a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l5a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l5a_prefix_read g init k x hpn hpx, l5a_prefix_read g init k y hpn hpy]

private theorem l5a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
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

private theorem l5a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l5a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l5a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l5a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l5a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l5a_init_value (initSM initPM : Store)
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

private theorem l5a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l5SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5220, 5221, 5218, 5222, 5223], outs := [5224, 5225],
    params := [16, 4, 64, 64, 1, 512] }
private def l5PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8614, 8616, 8602, 5222, 5223], outs := [8618, 5225],
    params := [16, 4, 64, 64, 1, 512] }
private def l5PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8615, 8617, 8603, 5222, 5223], outs := [8619, 5225],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l5_sm_sliding_node : sm_goal_1.nodes[204]'(by native_decide) = l5SmSliding := by native_decide
private theorem l5_pm_sliding_node0 : pm_goal_1.nodes[469]'(by native_decide) = l5PmSliding0 := by native_decide
private theorem l5_pm_sliding_node1 : pm_goal_1.nodes[470]'(by native_decide) = l5PmSliding1 := by native_decide
private theorem l5_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l5SmSliding = [l5SmSliding] := by native_decide
private theorem l5_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l5PmSliding0 = [l5PmSliding0, l5PmSliding1] := by native_decide
private theorem l5_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l5PmSliding1 = [l5PmSliding0, l5PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L5 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l5o_raw5224_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8614) (denoteGraphDistributedFaithful pm_goal_1 initPM 8615)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5221)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8616) (denoteGraphDistributedFaithful pm_goal_1 initPM 8617)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8602) (denoteGraphDistributedFaithful pm_goal_1 initPM 8603)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5222 = denoteGraphDistributedFaithful pm_goal_1 initPM 5222)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5223 = denoteGraphDistributedFaithful pm_goal_1 initPM 5223) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5224)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8618) (denoteGraphDistributedFaithful pm_goal_1 initPM 8619)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm_goal_1.nodes.take 204).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm_goal_1.nodes.take 469).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm_goal_1.nodes.take 470).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 204, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 204, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l5a_prefix_read sm_goal_1 initSM 204 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 469, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 469, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l5a_prefix_read pm_goal_1 initPM 469 t hn hw
  have e9434 : fp 8614 = fp' 8614 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 8614 469 470
    (by omega) (by native_decide) (by native_decide)
  have e9435 : fp 8615 = fp' 8615 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 8615 469 470
    (by omega) (by native_decide) (by native_decide)
  have e9436 : fp 8616 = fp' 8616 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 8616 469 470
    (by omega) (by native_decide) (by native_decide)
  have e9437 : fp 8617 = fp' 8617 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 8617 469 470
    (by omega) (by native_decide) (by native_decide)
  have e9422 : fp 8602 = fp' 8602 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 8602 469 470
    (by omega) (by native_decide) (by native_decide)
  have e9423 : fp 8603 = fp' 8603 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 8603 469 470
    (by omega) (by native_decide) (by native_decide)
  have e5497 : fp 5222 = fp' 5222 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 5222 469 470
    (by omega) (by native_decide) (by native_decide)
  have e5498 : fp 5223 = fp' 5223 := l5a_split pm_goal_1 pm_goal_1.nodes initPM 5223 469 470
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5220 = allGatherPrimDimN 0 2 0 [fp 8614, fp 8615] := by
    rw [bs 5220 (by native_decide) (by native_decide), bp 8614 (by native_decide) (by native_decide),
      bp 8615 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5221 = allGatherPrimDimN 0 2 0 [fp 8616, fp 8617] := by
    rw [bs 5221 (by native_decide) (by native_decide), bp 8616 (by native_decide) (by native_decide),
      bp 8617 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 5218 = allGatherPrimDimN 0 2 0 [fp 8602, fp 8603] := by
    rw [bs 5218 (by native_decide) (by native_decide), bp 8602 (by native_decide) (by native_decide),
      bp 8603 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5222 = fp 5222 := by
    rw [bs 5222 (by native_decide) (by native_decide), bp 5222 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5223 = fp 5223 := by
    rw [bs 5223 (by native_decide) (by native_decide), bp 5223 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l5PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l5PmSliding1 := by
    apply l5a_attn_congr
    · rw [l5_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9434
      · exact e9435
    · rw [l5_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9436
      · exact e9437
    · rw [l5_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9422
      · exact e9423
    · exact e5497
    · exact e5498
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5224 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l5SmSliding := by
    rw [l5a_node_core sm_goal_1 initSM 204 l5SmSliding 5224 (by native_decide)
      l5_sm_sliding_node (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l5a_ring_sliding_first_out sm_goal_1 _ 0 5220 5221 5218 5222 5223 5224 5225
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8618 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l5PmSliding0 := by
    rw [l5a_node_core pm_goal_1 initPM 469 l5PmSliding0 8618 (by native_decide)
      l5_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l5a_ring_sliding_first_out pm_goal_1 _ 0 8614 8616 8602 5222 5223 8618 5225
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8619 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l5PmSliding1 := by
    rw [l5a_node_core pm_goal_1 initPM 470 l5PmSliding1 8619 (by native_decide)
      l5_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide) (by native_decide) (by native_decide)]
    exact l5a_ring_sliding_first_out pm_goal_1 _ 1 8615 8617 8603 5222 5223 8619 5225
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8614, fp 8615])
      (allGatherPrimDimN 0 2 0 [fp 8616, fp 8617])
      (allGatherPrimDimN 0 2 0 [fp 8602, fp 8603])
      (fp 5222) (fp 5223) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l5a_attn_shape, ← hqfull, bs 5220 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8614, fp' 8615])
      (allGatherPrimDimN 0 2 0 [fp' 8616, fp' 8617])
      (allGatherPrimDimN 0 2 0 [fp' 8602, fp' 8603])
      (fp' 5222) (fp' 5223) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9434, ← e9435,
      ← e9436, ← e9437,
      ← e9422, ← e9423,
      ← e5497, ← e5498]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l5SmSliding l5PmSliding0 l5PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l5_sm_sliding_buddy l5_pm_sliding_buddy0
    l5_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5220).shape.length; rw [bs 5220 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5221).shape.length; rw [bs 5221 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 5218).shape.length; rw [bs 5218 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 5224 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8618, denoteGraphDistributedFaithful pm_goal_1 initPM 8619] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8618).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l5PmSliding0
      l5PmSliding0 l5PmSliding1 0 l5_pm_sliding_buddy0 (by native_decide)]
    simp only [l5PmSliding0, l5PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8614, fp 8615])
      (allGatherPrimDimN 0 2 0 [fp 8616, fp 8617])
      (allGatherPrimDimN 0 2 0 [fp 8602, fp 8603])
      (fp 5222) (fp 5223) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8619).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l5PmSliding1
      l5PmSliding0 l5PmSliding1 1 l5_pm_sliding_buddy1 (by native_decide)]
    simp only [l5PmSliding0, l5PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8614, fp' 8615])
      (allGatherPrimDimN 0 2 0 [fp' 8616, fp' 8617])
      (allGatherPrimDimN 0 2 0 [fp' 8602, fp' 8603])
      (fp' 5222) (fp' 5223) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l5a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l5a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l5a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l5a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l5a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l5a_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l5a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l5a_reduce1 g init k _ i o id hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l5a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l5a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L5 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l5o_residual5232_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5224)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8618) (denoteGraphDistributedFaithful pm_goal_1 initPM 8619)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8008)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15602) (denoteGraphDistributedFaithful pm_goal_1 initPM 15610)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648) (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l5a_reshape sm_goal_1 initSM 205 0 5224 5226 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l5a_reshape pm_goal_1 initPM 471 0 8618 8620 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l5a_reshape pm_goal_1 initPM 472 1 8619 8621 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5226) (denoteGraphDistributedFaithful pm_goal_1 initPM 8620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8621) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r0]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r0, r10]
  have rs1 := l5a_reshape sm_goal_1 initSM 206 0 5226 5227 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l5a_reshape pm_goal_1 initPM 473 0 8620 8626 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l5a_reshape pm_goal_1 initPM 474 1 8621 8627 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5227) (denoteGraphDistributedFaithful pm_goal_1 initPM 8626)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8627) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5227 = denoteGraphDistributedFaithful sm_goal_1 initSM 5226 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8626 = denoteGraphDistributedFaithful pm_goal_1 initPM 8620 := by rw [r1, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8627 = denoteGraphDistributedFaithful pm_goal_1 initPM 8621 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l5a_init_value initSM initPM hInit initGoal_5228
    (by native_decide) 5228 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l5a_init_shape initSM initPM hInit initGoal_5228
    (by native_decide) 5228 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5228).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l5a_linear sm_goal_1 initSM 207 0 5227 5228 5229 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l5a_linear pm_goal_1 initPM 475 0 8626 5228 8630 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l5a_linear pm_goal_1 initPM 476 1 8627 5228 8631 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5229) (denoteGraphDistributedFaithful pm_goal_1 initPM 8630)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8631) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l5a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l5a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l5a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l5a_view sm_goal_1 initSM 208 0 5229 5230 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l5a_view pm_goal_1 initPM 477 0 8630 8640 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l5a_view pm_goal_1 initPM 478 1 8631 8641 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5230) (denoteGraphDistributedFaithful pm_goal_1 initPM 8640)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8641) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5230 = denoteGraphDistributedFaithful sm_goal_1 initSM 5229 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 8640 = denoteGraphDistributedFaithful pm_goal_1 initPM 8630 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 8641 = denoteGraphDistributedFaithful pm_goal_1 initPM 8631 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l5a_float sm_goal_1 initSM 209 0 5230 5231 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l5a_float pm_goal_1 initPM 479 0 8640 8644 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l5a_float pm_goal_1 initPM 480 1 8641 8645 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5231) (denoteGraphDistributedFaithful pm_goal_1 initPM 8644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8645) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l5a_add sm_goal_1 initSM 210 0 8008 5231 5232 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l5a_add pm_goal_1 initPM 481 0 15602 8644 8648 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l5a_add pm_goal_1 initPM 482 1 15610 8645 8649 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L5 ordinary attention-to-residual boundary. -/
theorem l5o_residual5232_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5220) (denoteGraphDistributedFaithful pm_goal_1 initPM 8614)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8615) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5221) (denoteGraphDistributedFaithful pm_goal_1 initPM 8616)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8617) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5218) (denoteGraphDistributedFaithful pm_goal_1 initPM 8602)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8603) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5222 = denoteGraphDistributedFaithful pm_goal_1 initPM 5222)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5223 = denoteGraphDistributedFaithful pm_goal_1 initPM 5223)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8008) (denoteGraphDistributedFaithful pm_goal_1 initPM 15602)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15610) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5232) (denoteGraphDistributedFaithful pm_goal_1 initPM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8649) [4096,1024] [2048,1024] :=
  l5o_residual5232_rel_of_raw initSM initPM hInit
    (l5o_raw5224_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L5 continuation from the exact incoming residual boundary
`5210 ↔ (8574,8575)`.  Q/K/V remain the explicit internal boundary until the
L5 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l5o_residual5232_rel_from_boundary5210_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574) (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8614) (denoteGraphDistributedFaithful pm_goal_1 initPM 8615)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5221)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8616) (denoteGraphDistributedFaithful pm_goal_1 initPM 8617)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8602) (denoteGraphDistributedFaithful pm_goal_1 initPM 8603)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648) (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096,1024] [2048,1024] := by
  have ms := l5a_reduce1 sm_goal_1 initSM 197
    { rank := 0, op := "OpName.FW_multiref", ins := [5210], outs := [8004, 8008], params := [2] }
    5210 8008 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l5a_multiref_at sm_goal_1 st 0 5210 [8004, 8008] 2 rfl 8008 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l5a_reduce1 pm_goal_1 initPM 452
    { rank := 0, op := "OpName.FW_multiref", ins := [8574], outs := [15598, 15602], params := [2] }
    8574 15602 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l5a_multiref_at pm_goal_1 st 0 8574 [15598, 15602] 2 rfl 15602 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l5a_reduce1 pm_goal_1 initPM 453
    { rank := 1, op := "OpName.FW_multiref", ins := [8575], outs := [15606, 15610], params := [2] }
    8575 15610 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l5a_multiref_at pm_goal_1 st 1 8575 [15606, 15610] 2 rfl 15610 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8008)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15602) (denoteGraphDistributedFaithful pm_goal_1 initPM 15610)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l5a_init_value initSM initPM hInit initGoal_5222
    (by native_decide) 5222 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l5a_init_value initSM initPM hInit initGoal_5223
    (by native_decide) 5223 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l5o_residual5232_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

/-- Unconditional L5 ordinary attention residual reconstruction from the exact
incoming residual boundary: Q, K, and V are derived from their concrete graph
nodes before the sliding-window attention and projection continuation. -/
theorem l5o_residual5232_rel_from_boundary5210
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574) (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648) (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096,1024] [2048,1024] := by
  obtain ⟨hq, hk⟩ := l5o_q5220_k5221_rels_from_boundary initSM initPM hInit hboundary
  have hv := l5o_v5218_rel_from_boundary initSM initPM hInit hboundary
  exact l5o_residual5232_rel_from_boundary5210_of_qkv
    initSM initPM hInit hboundary hq hk hv

end TrainVerify.Denote.GeneratedPatterns
