import denote.yoco_goals.Goal_1
import denote.yoco_goals.CanonicalGoal1EmbeddingEntry
import denote.yoco_goals.L0OrdinaryQKV
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

private theorem l0a_node_core (g : GraphDecl) (init : Store) (k : Nat)
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

private theorem l0a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l0a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l0a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l0a_prefix_read g init k i hpn hpw]

private theorem l0a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l0a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l0a_prefix_read g init k x hpn hpx, l0a_prefix_read g init k y hpn hpy]

private theorem l0a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
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

private theorem l0a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l0a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l0a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l0a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l0a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l0a_init_value (initSM initPM : Store)
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

private theorem l0a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l0SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [4945, 4946, 4942, 4947, 4948], outs := [4949, 4950],
    params := [16, 4, 64, 64, 1, 512] }
private def l0PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [7794, 7796, 7782, 4947, 4948], outs := [7798, 4950],
    params := [16, 4, 64, 64, 1, 512] }
private def l0PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [7795, 7797, 7783, 4947, 4948], outs := [7799, 4950],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l0_sm_sliding_node : sm_goal_1.nodes[9]'(by native_decide) = l0SmSliding := by native_decide
private theorem l0_pm_sliding_node0 : pm_goal_1.nodes[49]'(by native_decide) = l0PmSliding0 := by native_decide
private theorem l0_pm_sliding_node1 : pm_goal_1.nodes[50]'(by native_decide) = l0PmSliding1 := by native_decide
private theorem l0_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l0SmSliding = [l0SmSliding] := by native_decide
private theorem l0_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l0PmSliding0 = [l0PmSliding0, l0PmSliding1] := by native_decide
private theorem l0_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l0PmSliding1 = [l0PmSliding0, l0PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L0 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l0o_raw4949_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4945)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7794) (denoteGraphDistributedFaithful pm_goal_1 initPM 7795)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7796) (denoteGraphDistributedFaithful pm_goal_1 initPM 7797)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4942)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7782) (denoteGraphDistributedFaithful pm_goal_1 initPM 7783)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 4947 = denoteGraphDistributedFaithful pm_goal_1 initPM 4947)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 4948 = denoteGraphDistributedFaithful pm_goal_1 initPM 4948) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4949)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7798) (denoteGraphDistributedFaithful pm_goal_1 initPM 7799)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm_goal_1.nodes.take 9).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm_goal_1.nodes.take 49).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm_goal_1.nodes.take 50).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 9, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 9, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l0a_prefix_read sm_goal_1 initSM 9 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 49, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 49, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l0a_prefix_read pm_goal_1 initPM 49 t hn hw
  have e7794 : fp 7794 = fp' 7794 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 7794 49 50
    (by omega) (by native_decide) (by native_decide)
  have e7795 : fp 7795 = fp' 7795 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 7795 49 50
    (by omega) (by native_decide) (by native_decide)
  have e7796 : fp 7796 = fp' 7796 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 7796 49 50
    (by omega) (by native_decide) (by native_decide)
  have e7797 : fp 7797 = fp' 7797 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 7797 49 50
    (by omega) (by native_decide) (by native_decide)
  have e7782 : fp 7782 = fp' 7782 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 7782 49 50
    (by omega) (by native_decide) (by native_decide)
  have e7783 : fp 7783 = fp' 7783 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 7783 49 50
    (by omega) (by native_decide) (by native_decide)
  have e4947 : fp 4947 = fp' 4947 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 4947 49 50
    (by omega) (by native_decide) (by native_decide)
  have e4948 : fp 4948 = fp' 4948 := l0a_split pm_goal_1 pm_goal_1.nodes initPM 4948 49 50
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 4945 = allGatherPrimDimN 0 2 0 [fp 7794, fp 7795] := by
    rw [bs 4945 (by native_decide) (by native_decide), bp 7794 (by native_decide) (by native_decide),
      bp 7795 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 4946 = allGatherPrimDimN 0 2 0 [fp 7796, fp 7797] := by
    rw [bs 4946 (by native_decide) (by native_decide), bp 7796 (by native_decide) (by native_decide),
      bp 7797 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 4942 = allGatherPrimDimN 0 2 0 [fp 7782, fp 7783] := by
    rw [bs 4942 (by native_decide) (by native_decide), bp 7782 (by native_decide) (by native_decide),
      bp 7783 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 4947 = fp 4947 := by
    rw [bs 4947 (by native_decide) (by native_decide), bp 4947 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 4948 = fp 4948 := by
    rw [bs 4948 (by native_decide) (by native_decide), bp 4948 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l0PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l0PmSliding1 := by
    apply l0a_attn_congr
    · rw [l0_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e7794
      · exact e7795
    · rw [l0_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e7796
      · exact e7797
    · rw [l0_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e7782
      · exact e7783
    · exact e4947
    · exact e4948
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 4949 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l0SmSliding := by
    rw [l0a_node_core sm_goal_1 initSM 9 l0SmSliding 4949 (by native_decide)
      l0_sm_sliding_node (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l0a_ring_sliding_first_out sm_goal_1 _ 0 4945 4946 4942 4947 4948 4949 4950
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 7798 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l0PmSliding0 := by
    rw [l0a_node_core pm_goal_1 initPM 49 l0PmSliding0 7798 (by native_decide)
      l0_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l0a_ring_sliding_first_out pm_goal_1 _ 0 7794 7796 7782 4947 4948 7798 4950
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 7799 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l0PmSliding1 := by
    rw [l0a_node_core pm_goal_1 initPM 50 l0PmSliding1 7799 (by native_decide)
      l0_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l0a_ring_sliding_first_out pm_goal_1 _ 1 7795 7797 7783 4947 4948 7799 4950
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7794, fp 7795])
      (allGatherPrimDimN 0 2 0 [fp 7796, fp 7797])
      (allGatherPrimDimN 0 2 0 [fp 7782, fp 7783])
      (fp 4947) (fp 4948) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l0a_attn_shape, ← hqfull, bs 4945 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7794, fp' 7795])
      (allGatherPrimDimN 0 2 0 [fp' 7796, fp' 7797])
      (allGatherPrimDimN 0 2 0 [fp' 7782, fp' 7783])
      (fp' 4947) (fp' 4948) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e7794, ← e7795,
      ← e7796, ← e7797,
      ← e7782, ← e7783,
      ← e4947, ← e4948]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l0SmSliding l0PmSliding0 l0PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l0_sm_sliding_buddy l0_pm_sliding_buddy0
    l0_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 4945).shape.length; rw [bs 4945 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 4946).shape.length; rw [bs 4946 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 4942).shape.length; rw [bs 4942 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 4949 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 7798, denoteGraphDistributedFaithful pm_goal_1 initPM 7799] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7798).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l0PmSliding0
      l0PmSliding0 l0PmSliding1 0 l0_pm_sliding_buddy0 (by native_decide)]
    simp only [l0PmSliding0, l0PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7794, fp 7795])
      (allGatherPrimDimN 0 2 0 [fp 7796, fp 7797])
      (allGatherPrimDimN 0 2 0 [fp 7782, fp 7783])
      (fp 4947) (fp 4948) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7799).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l0PmSliding1
      l0PmSliding0 l0PmSliding1 1 l0_pm_sliding_buddy1 (by native_decide)]
    simp only [l0PmSliding0, l0PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7794, fp' 7795])
      (allGatherPrimDimN 0 2 0 [fp' 7796, fp' 7797])
      (allGatherPrimDimN 0 2 0 [fp' 7782, fp' 7783])
      (fp' 4947) (fp' 4948) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l0a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l0a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l0a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l0a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l0a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l0a_reduce2 g init k _ x w o fw_linear hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l0a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l0a_reduce1 g init k _ i o id hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l0a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l0a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L0 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l0o_residual4957_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4949)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7798) (denoteGraphDistributedFaithful pm_goal_1 initPM 7799)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7748)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15442) (denoteGraphDistributedFaithful pm_goal_1 initPM 15450)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828) (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l0a_reshape sm_goal_1 initSM 10 0 4949 4951 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l0a_reshape pm_goal_1 initPM 51 0 7798 7800 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l0a_reshape pm_goal_1 initPM 52 1 7799 7801 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4951) (denoteGraphDistributedFaithful pm_goal_1 initPM 7800)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7801) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r0]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r0, r10]
  have rs1 := l0a_reshape sm_goal_1 initSM 11 0 4951 4952 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l0a_reshape pm_goal_1 initPM 53 0 7800 7806 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l0a_reshape pm_goal_1 initPM 54 1 7801 7807 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4952) (denoteGraphDistributedFaithful pm_goal_1 initPM 7806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7807) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 4952 = denoteGraphDistributedFaithful sm_goal_1 initSM 4951 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 7806 = denoteGraphDistributedFaithful pm_goal_1 initPM 7800 := by rw [r1, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 7807 = denoteGraphDistributedFaithful pm_goal_1 initPM 7801 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l0a_init_value initSM initPM hInit initGoal_4953
    (by native_decide) 4953 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l0a_init_shape initSM initPM hInit initGoal_4953
    (by native_decide) 4953 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 4953).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l0a_linear sm_goal_1 initSM 12 0 4952 4953 4954 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l0a_linear pm_goal_1 initPM 55 0 7806 4953 7810 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l0a_linear pm_goal_1 initPM 56 1 7807 4953 7811 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4954) (denoteGraphDistributedFaithful pm_goal_1 initPM 7810)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7811) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l0a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l0a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l0a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l0a_view sm_goal_1 initSM 13 0 4954 4955 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l0a_view pm_goal_1 initPM 57 0 7810 7820 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l0a_view pm_goal_1 initPM 58 1 7811 7821 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4955) (denoteGraphDistributedFaithful pm_goal_1 initPM 7820)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7821) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 4955 = denoteGraphDistributedFaithful sm_goal_1 initSM 4954 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 7820 = denoteGraphDistributedFaithful pm_goal_1 initPM 7810 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 7821 = denoteGraphDistributedFaithful pm_goal_1 initPM 7811 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l0a_float sm_goal_1 initSM 14 0 4955 4956 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l0a_float pm_goal_1 initPM 59 0 7820 7824 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l0a_float pm_goal_1 initPM 60 1 7821 7825 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4956) (denoteGraphDistributedFaithful pm_goal_1 initPM 7824)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7825) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l0a_add sm_goal_1 initSM 15 0 7748 4956 4957 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l0a_add pm_goal_1 initPM 61 0 15442 7824 7828 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l0a_add pm_goal_1 initPM 62 1 15450 7825 7829 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L0 ordinary attention-to-residual boundary. -/
theorem l0o_residual4957_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4945) (denoteGraphDistributedFaithful pm_goal_1 initPM 7794)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7795) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4946) (denoteGraphDistributedFaithful pm_goal_1 initPM 7796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7797) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4942) (denoteGraphDistributedFaithful pm_goal_1 initPM 7782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7783) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 4947 = denoteGraphDistributedFaithful pm_goal_1 initPM 4947)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 4948 = denoteGraphDistributedFaithful pm_goal_1 initPM 4948)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7748) (denoteGraphDistributedFaithful pm_goal_1 initPM 15442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15450) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4957) (denoteGraphDistributedFaithful pm_goal_1 initPM 7828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7829) [4096,1024] [2048,1024] :=
  l0o_residual4957_rel_of_raw initSM initPM hInit
    (l0o_raw4949_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L0 continuation from the exact incoming residual boundary
`4934 ↔ (7754,7755)`.  Q/K/V remain the explicit internal boundary until the
L0 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l0o_residual4957_rel_from_boundary4934_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7754) (denoteGraphDistributedFaithful pm_goal_1 initPM 7755)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4945)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7794) (denoteGraphDistributedFaithful pm_goal_1 initPM 7795)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7796) (denoteGraphDistributedFaithful pm_goal_1 initPM 7797)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4942)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7782) (denoteGraphDistributedFaithful pm_goal_1 initPM 7783)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828) (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096,1024] [2048,1024] := by
  have ms := l0a_reduce1 sm_goal_1 initSM 2
    { rank := 0, op := "OpName.FW_multiref", ins := [4934], outs := [7744, 7748], params := [2] }
    4934 7748 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l0a_multiref_at sm_goal_1 st 0 4934 [7744, 7748] 2 rfl 7748 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l0a_reduce1 pm_goal_1 initPM 32
    { rank := 0, op := "OpName.FW_multiref", ins := [7754], outs := [15438, 15442], params := [2] }
    7754 15442 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l0a_multiref_at pm_goal_1 st 0 7754 [15438, 15442] 2 rfl 15442 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l0a_reduce1 pm_goal_1 initPM 33
    { rank := 1, op := "OpName.FW_multiref", ins := [7755], outs := [15446, 15450], params := [2] }
    7755 15450 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l0a_multiref_at pm_goal_1 st 1 7755 [15446, 15450] 2 rfl 15450 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7748)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15442) (denoteGraphDistributedFaithful pm_goal_1 initPM 15450)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l0a_init_value initSM initPM hInit initGoal_4947
    (by native_decide) 4947 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l0a_init_value initSM initPM hInit initGoal_4948
    (by native_decide) 4948 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l0o_residual4957_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

/-- Direct faithful L0 QKV, sliding-window attention, projection, and residual
composition from the exact incoming boundary `4934 ↔ (7754,7755)`. -/
theorem l0o_residual4957_rel_from_boundary4934
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7755)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096,1024] [2048,1024] := by
  have hv := l0o_v4942_rel_from_boundary initSM initPM hInit hboundary
  have hqk := l0o_q4945_k4946_rels_from_boundary initSM initPM hInit hboundary
  exact l0o_residual4957_rel_from_boundary4934_of_qkv initSM initPM hInit hboundary
    hqk.1 hqk.2 hv

/-- Exact Goal-1 external-to-L0 faithful composition.  The embedding/AllToAll
entry relation and every Q/K/V, sliding-attention, projection, and residual
relation are computed internally; callers provide only the generated store and
init contracts. -/
theorem canonical_l0_residual4957_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096,1024] [2048,1024] :=
  l0o_residual4957_rel_from_boundary4934 initSM initPM hInit
    (canonical_goal_1_embedding_entry initSM initPM hSM hPM hInit)

#print axioms canonical_l0_residual4957_rel

end TrainVerify.Denote.GeneratedPatterns
