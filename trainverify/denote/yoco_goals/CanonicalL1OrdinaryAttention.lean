import denote.yoco_goals.Goal_1
import denote.yoco_goals.L1OrdinaryQKV
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

private theorem l1a_node_core (g : GraphDecl) (init : Store) (k : Nat)
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

private theorem l1a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hw).symm

private theorem l1a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l1a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l1a_prefix_read g init k i hpn hpw]

private theorem l1a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l1a_node_core g init k node o hk hn hm hshuffle hunshuffle hattn hdn hdw, ha,
    l1a_prefix_read g init k x hpn hpx, l1a_prefix_read g init k y hpn hpy]

private theorem l1a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
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

private theorem l1a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l1a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l1a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l1a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l1a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l1a_init_value (initSM initPM : Store)
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

private theorem l1a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributedFaithful, foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l1SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5000, 5001, 4998, 5002, 5003], outs := [5004, 5005],
    params := [16, 4, 64, 64, 1, 512] }
private def l1PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [7958, 7960, 7946, 5002, 5003], outs := [7962, 5005],
    params := [16, 4, 64, 64, 1, 512] }
private def l1PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [7959, 7961, 7947, 5002, 5003], outs := [7963, 5005],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l1_sm_sliding_node : sm_goal_1.nodes[48]'(by native_decide) = l1SmSliding := by native_decide
private theorem l1_pm_sliding_node0 : pm_goal_1.nodes[133]'(by native_decide) = l1PmSliding0 := by native_decide
private theorem l1_pm_sliding_node1 : pm_goal_1.nodes[134]'(by native_decide) = l1PmSliding1 := by native_decide
private theorem l1_sm_sliding_buddy : ringAttnBuddies sm_goal_1 l1SmSliding = [l1SmSliding] := by native_decide
private theorem l1_pm_sliding_buddy0 : ringAttnBuddies pm_goal_1 l1PmSliding0 = [l1PmSliding0, l1PmSliding1] := by native_decide
private theorem l1_pm_sliding_buddy1 : ringAttnBuddies pm_goal_1 l1PmSliding1 = [l1PmSliding0, l1PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L1 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l1o_raw5004_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7958) (denoteGraphDistributedFaithful pm_goal_1 initPM 7959)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5001)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7960) (denoteGraphDistributedFaithful pm_goal_1 initPM 7961)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7946) (denoteGraphDistributedFaithful pm_goal_1 initPM 7947)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5002 = denoteGraphDistributedFaithful pm_goal_1 initPM 5002)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5003 = denoteGraphDistributedFaithful pm_goal_1 initPM 5003) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5004)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7962) (denoteGraphDistributedFaithful pm_goal_1 initPM 7963)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm.nodes.take 48).foldl (applyNodeDistributedFaithful sm_goal_1) initSM
  let fp := (pm.nodes.take 133).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  let fp' := (pm.nodes.take 134).foldl (applyNodeDistributedFaithful pm_goal_1) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm_goal_1.nodes.drop 48, n.outs ≠ [])
      (hw : ∀ n ∈ sm_goal_1.nodes.drop 48, t ∉ n.outs) : fs t = denoteGraphDistributedFaithful sm_goal_1 initSM t :=
    l1a_prefix_read sm_goal_1 initSM 48 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm_goal_1.nodes.drop 133, n.outs ≠ [])
      (hw : ∀ n ∈ pm_goal_1.nodes.drop 133, t ∉ n.outs) : fp t = denoteGraphDistributedFaithful pm_goal_1 initPM t :=
    l1a_prefix_read pm_goal_1 initPM 133 t hn hw
  have e7958 : fp 7958 = fp' 7958 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 7958 133 134
    (by omega) (by native_decide) (by native_decide)
  have e7959 : fp 7959 = fp' 7959 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 7959 133 134
    (by omega) (by native_decide) (by native_decide)
  have e7960 : fp 7960 = fp' 7960 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 7960 133 134
    (by omega) (by native_decide) (by native_decide)
  have e7961 : fp 7961 = fp' 7961 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 7961 133 134
    (by omega) (by native_decide) (by native_decide)
  have e7946 : fp 7946 = fp' 7946 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 7946 133 134
    (by omega) (by native_decide) (by native_decide)
  have e7947 : fp 7947 = fp' 7947 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 7947 133 134
    (by omega) (by native_decide) (by native_decide)
  have e5002 : fp 5002 = fp' 5002 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 5002 133 134
    (by omega) (by native_decide) (by native_decide)
  have e5003 : fp 5003 = fp' 5003 := l1a_split pm_goal_1 pm_goal_1.nodes initPM 5003 133 134
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5000 = allGatherPrimDimN 0 2 0 [fp 7958, fp 7959] := by
    rw [bs 5000 (by native_decide) (by native_decide), bp 7958 (by native_decide) (by native_decide),
      bp 7959 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5001 = allGatherPrimDimN 0 2 0 [fp 7960, fp 7961] := by
    rw [bs 5001 (by native_decide) (by native_decide), bp 7960 (by native_decide) (by native_decide),
      bp 7961 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 4998 = allGatherPrimDimN 0 2 0 [fp 7946, fp 7947] := by
    rw [bs 4998 (by native_decide) (by native_decide), bp 7946 (by native_decide) (by native_decide),
      bp 7947 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5002 = fp 5002 := by
    rw [bs 5002 (by native_decide) (by native_decide), bp 5002 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5003 = fp 5003 := by
    rw [bs 5003 (by native_decide) (by native_decide), bp 5003 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm_goal_1 fp l1PmSliding1 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l1PmSliding1 := by
    apply l1a_attn_congr
    · rw [l1_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e7958
      · exact e7959
    · rw [l1_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e7960
      · exact e7961
    · rw [l1_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e7946
      · exact e7947
    · exact e5002
    · exact e5003
  have rSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5004 =
      applyNodeRingAttn_sliding_window sm_goal_1 fs l1SmSliding := by
    rw [l1a_node_core sm_goal_1 initSM 48 l1SmSliding 5004 (by native_decide)
      l1_sm_sliding_node (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l1a_ring_sliding_first_out sm_goal_1 _ 0 5000 5001 4998 5002 5003 5004 5005
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributedFaithful pm_goal_1 initPM 7962 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp l1PmSliding0 := by
    rw [l1a_node_core pm_goal_1 initPM 133 l1PmSliding0 7962 (by native_decide)
      l1_pm_sliding_node0 (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l1a_ring_sliding_first_out pm_goal_1 _ 0 7958 7960 7946 5002 5003 7962 5005
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributedFaithful pm_goal_1 initPM 7963 =
      applyNodeRingAttn_sliding_window pm_goal_1 fp' l1PmSliding1 := by
    rw [l1a_node_core pm_goal_1 initPM 134 l1PmSliding1 7963 (by native_decide)
      l1_pm_sliding_node1 (by decide) (by decide) (by decide) (by decide)
      (by native_decide) (by native_decide)]
    exact l1a_ring_sliding_first_out pm_goal_1 _ 1 7959 7961 7947 5002 5003 7963 5005
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7958, fp 7959])
      (allGatherPrimDimN 0 2 0 [fp 7960, fp 7961])
      (allGatherPrimDimN 0 2 0 [fp 7946, fp 7947])
      (fp 5002) (fp 5003) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l1a_attn_shape, ← hqfull, bs 5000 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7958, fp' 7959])
      (allGatherPrimDimN 0 2 0 [fp' 7960, fp' 7961])
      (allGatherPrimDimN 0 2 0 [fp' 7946, fp' 7947])
      (fp' 5002) (fp' 5003) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e7958, ← e7959,
      ← e7960, ← e7961,
      ← e7946, ← e7947,
      ← e5002, ← e5003]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_1 pm_goal_1 fs fp l1SmSliding l1PmSliding0 l1PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l1_sm_sliding_buddy l1_pm_sliding_buddy0
    l1_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5000).shape.length; rw [bs 5000 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5001).shape.length; rw [bs 5001 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 4998).shape.length; rw [bs 4998 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 5004 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 7962, denoteGraphDistributedFaithful pm_goal_1 initPM 7963] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7962).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp l1PmSliding0
      l1PmSliding0 l1PmSliding1 0 l1_pm_sliding_buddy0 (by native_decide)]
    simp only [l1PmSliding0, l1PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7958, fp 7959])
      (allGatherPrimDimN 0 2 0 [fp 7960, fp 7961])
      (allGatherPrimDimN 0 2 0 [fp 7946, fp 7947])
      (fp 5002) (fp 5003) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7963).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm_goal_1 fp' l1PmSliding1
      l1PmSliding0 l1PmSliding1 1 l1_pm_sliding_buddy1 (by native_decide)]
    simp only [l1PmSliding0, l1PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7958, fp' 7959])
      (allGatherPrimDimN 0 2 0 [fp' 7960, fp' 7961])
      (allGatherPrimDimN 0 2 0 [fp' 7946, fp' 7947])
      (fp' 5002) (fp' 5003) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l1a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l1a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l1a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_view (hd :: tl) (denoteGraphDistributedFaithful g init i) :=
  l1a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l1a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = fw_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l1a_reduce2 g init k _ x w o fw_linear hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l1a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = denoteGraphDistributedFaithful g init i := by
  have h := l1a_reduce1 g init k _ i o id hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l1a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = elemwiseAdd (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init y) :=
  l1a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp) (by simp) (by simp) (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L1 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l1o_residual5012_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5004)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7962) (denoteGraphDistributedFaithful pm_goal_1 initPM 7963)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7800)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15474) (denoteGraphDistributedFaithful pm_goal_1 initPM 15482)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992) (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l1a_reshape sm_goal_1 initSM 49 0 5004 5006 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l1a_reshape pm_goal_1 initPM 135 0 7962 7964 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l1a_reshape pm_goal_1 initPM 136 1 7963 7965 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5006) (denoteGraphDistributedFaithful pm_goal_1 initPM 7964)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7965) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r0]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r0, r10]
  have rs1 := l1a_reshape sm_goal_1 initSM 50 0 5006 5007 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l1a_reshape pm_goal_1 initPM 137 0 7964 7970 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l1a_reshape pm_goal_1 initPM 138 1 7965 7971 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5007) (denoteGraphDistributedFaithful pm_goal_1 initPM 7970)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7971) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5007 = denoteGraphDistributedFaithful sm_goal_1 initSM 5006 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 7970 = denoteGraphDistributedFaithful pm_goal_1 initPM 7964 := by rw [r1, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 7971 = denoteGraphDistributedFaithful pm_goal_1 initPM 7965 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l1a_init_value initSM initPM hInit initGoal_5008
    (by native_decide) 5008 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l1a_init_shape initSM initPM hInit initGoal_5008
    (by native_decide) 5008 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5008).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l1a_linear sm_goal_1 initSM 51 0 5007 5008 5009 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l1a_linear pm_goal_1 initPM 139 0 7970 5008 7974 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l1a_linear pm_goal_1 initPM 140 1 7971 5008 7975 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5009) (denoteGraphDistributedFaithful pm_goal_1 initPM 7974)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7975) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l1a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l1a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l1a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l1a_view sm_goal_1 initSM 52 0 5009 5010 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l1a_view pm_goal_1 initPM 141 0 7974 7984 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l1a_view pm_goal_1 initPM 142 1 7975 7985 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5010) (denoteGraphDistributedFaithful pm_goal_1 initPM 7984)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7985) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributedFaithful sm_goal_1 initSM 5010 = denoteGraphDistributedFaithful sm_goal_1 initSM 5009 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributedFaithful pm_goal_1 initPM 7984 = denoteGraphDistributedFaithful pm_goal_1 initPM 7974 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributedFaithful pm_goal_1 initPM 7985 = denoteGraphDistributedFaithful pm_goal_1 initPM 7975 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l1a_float sm_goal_1 initSM 53 0 5010 5011 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l1a_float pm_goal_1 initPM 143 0 7984 7988 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l1a_float pm_goal_1 initPM 144 1 7985 7989 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5011) (denoteGraphDistributedFaithful pm_goal_1 initPM 7988)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7989) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l1a_add sm_goal_1 initSM 54 0 7800 5011 5012 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l1a_add pm_goal_1 initPM 145 0 15474 7988 7992 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l1a_add pm_goal_1 initPM 146 1 15482 7989 7993 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L1 ordinary attention-to-residual boundary. -/
theorem l1o_residual5012_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5000) (denoteGraphDistributedFaithful pm_goal_1 initPM 7958)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7959) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5001) (denoteGraphDistributedFaithful pm_goal_1 initPM 7960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7961) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4998) (denoteGraphDistributedFaithful pm_goal_1 initPM 7946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7947) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributedFaithful sm_goal_1 initSM 5002 = denoteGraphDistributedFaithful pm_goal_1 initPM 5002)
    (hcuK : denoteGraphDistributedFaithful sm_goal_1 initSM 5003 = denoteGraphDistributedFaithful pm_goal_1 initPM 5003)
    (hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7800) (denoteGraphDistributedFaithful pm_goal_1 initPM 15474)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15482) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5012) (denoteGraphDistributedFaithful pm_goal_1 initPM 7992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7993) [4096,1024] [2048,1024] :=
  l1o_residual5012_rel_of_raw initSM initPM hInit
    (l1o_raw5004_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Conditional L1 continuation from the exact incoming residual boundary
`4990 ↔ (7918,7919)`.  Q/K/V remain the explicit internal boundary until the
L1 ordinary-QKV sibling is proved; the bypass and packed-cu aliases are
reconstructed from graph nodes and init goals. -/
theorem l1o_residual5012_rel_from_boundary4990_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7918) (denoteGraphDistributedFaithful pm_goal_1 initPM 7919)
      [4096,1024] [2048,1024])
    (hq : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7958) (denoteGraphDistributedFaithful pm_goal_1 initPM 7959)
      [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5001)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7960) (denoteGraphDistributedFaithful pm_goal_1 initPM 7961)
      [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7946) (denoteGraphDistributedFaithful pm_goal_1 initPM 7947)
      [4096,4,64] [2048,4,64]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992) (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096,1024] [2048,1024] := by
  have ms := l1a_reduce1 sm_goal_1 initSM 41
    { rank := 0, op := "OpName.FW_multiref", ins := [4990], outs := [7796, 7800], params := [2] }
    4990 7800 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l1a_multiref_at sm_goal_1 st 0 4990 [7796, 7800] 2 rfl 7800 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l1a_reduce1 pm_goal_1 initPM 116
    { rank := 0, op := "OpName.FW_multiref", ins := [7918], outs := [15470, 15474], params := [2] }
    7918 15474 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l1a_multiref_at pm_goal_1 st 0 7918 [15470, 15474] 2 rfl 15474 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l1a_reduce1 pm_goal_1 initPM 117
    { rank := 1, op := "OpName.FW_multiref", ins := [7919], outs := [15478, 15482], params := [2] }
    7919 15482 id (by native_decide) (by native_decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st => l1a_multiref_at pm_goal_1 st 1 7919 [15478, 15482] 2 rfl 15482 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 7800)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15474) (denoteGraphDistributedFaithful pm_goal_1 initPM 15482)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, hboundary.value, ← m0, ← m1], by rw [ms]; exact hboundary.full_shape,
      by rw [m0]; exact hboundary.shard0_shape, by rw [m1]; exact hboundary.shard1_shape,
      by decide⟩
  have hcuQ := l1a_init_value initSM initPM hInit initGoal_5002
    (by native_decide) 5002 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l1a_init_value initSM initPM hInit initGoal_5003
    (by native_decide) 5003 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l1o_residual5012_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

/-- Direct faithful L1 QKV, sliding-window attention, projection, and residual
composition from the exact incoming boundary `4990 ↔ (7918,7919)`. -/
theorem l1o_residual5012_rel_from_boundary4990
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hboundary : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7919)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096,1024] [2048,1024] := by
  have hv := l1o_v4998_rel_from_boundary initSM initPM hInit hboundary
  have hqk := l1o_q5000_k5001_rels_from_boundary initSM initPM hInit hboundary
  exact l1o_residual5012_rel_from_boundary4990_of_qkv initSM initPM hInit hboundary
    hqk.1 hqk.2 hv

end TrainVerify.Denote.GeneratedPatterns
