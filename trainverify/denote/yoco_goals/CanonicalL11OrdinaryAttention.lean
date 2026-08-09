import denote.yoco_goals.L11OrdinaryQKV
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

private theorem l11a_node_core (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid) (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node) (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hnil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      applyNodeRingAttn g ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid := by
  rw [denoteGraphDistributed_eq_prefix g init outTid (k + 1) hnil hw]
  have hstep := congrFun (foldl_take_succ (applyNodeDistributed g) g.nodes init k hk) outTid
  rw [hstep, hnode]
  unfold applyNodeDistributed
  rw [if_neg hmoe]

private theorem l11a_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hw : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributed g) init) tid =
      denoteGraphDistributed g init tid :=
  (denoteGraphDistributed_eq_prefix g init tid k hnil hw).symm

private theorem l11a_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (i o : Tid) (f : Tensor → Tensor)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hm : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (ha : ∀ s, applyNodeRingAttn g s node o = f (s i))
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = f (denoteGraphDistributed g init i) := by
  rw [l11a_node_core g init k node o hk hn hm hdn hdw, ha,
    l11a_prefix_read g init k i hpn hpw]

private theorem l11a_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (x y o : Tid) (f : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hm : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (ha : ∀ s, applyNodeRingAttn g s node o = f (s x) (s y))
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o = f (denoteGraphDistributed g init x)
      (denoteGraphDistributed g init y) := by
  rw [l11a_node_core g init k node o hk hn hm hdn hdw, ha,
    l11a_prefix_read g init k x hpn hpx, l11a_prefix_read g init k y hpn hpy]

private theorem l11a_split (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
    (tid j k : Nat) (hjk : j ≤ k)
    (hnil : ((nodes.take k).drop j).all (fun n => !n.outs.isEmpty) = true)
    (hw : ((nodes.take k).drop j).all (fun n => !n.outs.contains tid) = true) :
    (nodes.take j).foldl (applyNodeDistributed g) s tid =
      (nodes.take k).foldl (applyNodeDistributed g) s tid := by
  have hnil' : ∀ n ∈ (nodes.take k).drop j, n.outs ≠ [] := by
    intro n hn; simpa using (List.all_eq_true.mp hnil n hn)
  have hw' : ∀ n ∈ (nodes.take k).drop j, tid ∉ n.outs := by
    intro n hn; simpa using (List.all_eq_true.mp hw n hn)
  have hs : nodes.take k = nodes.take j ++ (nodes.take k).drop j := by
    rw [show nodes.take j = (nodes.take k).take j by rw [List.take_take, min_eq_left hjk]]
    rw [List.take_append_drop]
  rw [hs, List.foldl_append]
  exact (foldl_applyNodeDistributed_at_not_written g _ _ tid hnil' hw').symm

private theorem l11a_attn_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hq : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hk : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hq, hk]

private theorem l11a_ring_sliding_first_out (g : GraphDecl) (s : Store)
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

private theorem l11a_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l11a_attn_shape (q k v cq ck : Tensor) (qh kh d vd w : Nat) (c : Bool) :
    (fw_attn_varlen q k v cq ck qh kh d vd c w).shape = [q.shape.head?.getD 0, qh, vd] := by
  unfold fw_attn_varlen
  rfl

private theorem l11a_linear_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [TrainVerify.Denote.fw_linear_is_matmul b i o x w hx hw]
  rfl

private theorem l11a_init_value (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ initGoals) (W : Tid)
    (htp : gW.tps = [{ rank := 0, tid := W }]) (hgd : gW.gatherDim = 0)
    (hr : gW.replicated = false) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm.nodes, W ∉ n.outs) (hpm : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributed sm initSM W = denoteGraphDistributed pm initPM W := by
  have h := hInit gW hg
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated gW pm.numRanks _ hr, htp, hts, hgd] at hv
  simp only [List.map, reconstructWithDim] at hv
  rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM W
    (by native_decide) hsm, denoteGraphDistributed,
    foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM W (by native_decide) hpm]
  exact hv

private theorem l11a_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ initGoals) (W : Tid) (sh : Shape)
    (hsh : gW.tsShape = sh) (hts : gW.ts = W) (hsm : ∀ n ∈ sm.nodes, W ∉ n.outs) :
    (denoteGraphDistributed sm initSM W).shape = sh := by
  have h := hInit gW hg
  rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM W
    (by native_decide) hsm, ← hts, ← hsh]
  exact h.1

private def l11SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5550, 5551, 5548, 5552, 5553], outs := [5554, 5555],
    params := [16, 4, 64, 64, 1, 512] }
private def l11PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [9598, 9600, 9586, 5552, 5553], outs := [9602, 5555],
    params := [16, 4, 64, 64, 1, 512] }
private def l11PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [9599, 9601, 9587, 5552, 5553], outs := [9603, 5555],
    params := [16, 4, 64, 64, 1, 512] }

private theorem l11_sm_sliding_node : sm.nodes[438]'(by native_decide) = l11SmSliding := by native_decide
private theorem l11_pm_sliding_node0 : pm.nodes[973]'(by native_decide) = l11PmSliding0 := by native_decide
private theorem l11_pm_sliding_node1 : pm.nodes[974]'(by native_decide) = l11PmSliding1 := by native_decide
private theorem l11_sm_sliding_buddy : ringAttnBuddies sm l11SmSliding = [l11SmSliding] := by native_decide
private theorem l11_pm_sliding_buddy0 : ringAttnBuddies pm l11PmSliding0 = [l11PmSliding0, l11PmSliding1] := by native_decide
private theorem l11_pm_sliding_buddy1 : ringAttnBuddies pm l11PmSliding1 = [l11PmSliding0, l11PmSliding1] := by native_decide

/-- Conditional faithful ordinary-CP2 reconstruction of the L11 sliding-window
attention output.  The premises are precisely the Q/K/V gather relations and
replicated cu-seqlens aliases at the attention boundary. -/
theorem l11o_raw5554_rel_of_qkv
    (initSM initPM : Store)
    (hq : Gather2Rel (denoteGraphDistributed sm initSM 5550)
      (denoteGraphDistributed pm initPM 9598) (denoteGraphDistributed pm initPM 9599)
      [4096, 16, 64] [2048, 16, 64])
    (hk : Gather2Rel (denoteGraphDistributed sm initSM 5551)
      (denoteGraphDistributed pm initPM 9600) (denoteGraphDistributed pm initPM 9601)
      [4096, 4, 64] [2048, 4, 64])
    (hv : Gather2Rel (denoteGraphDistributed sm initSM 5548)
      (denoteGraphDistributed pm initPM 9586) (denoteGraphDistributed pm initPM 9587)
      [4096, 4, 64] [2048, 4, 64])
    (hcuQ : denoteGraphDistributed sm initSM 5552 = denoteGraphDistributed pm initPM 5552)
    (hcuK : denoteGraphDistributed sm initSM 5553 = denoteGraphDistributed pm initPM 5553) :
    Gather2Rel (denoteGraphDistributed sm initSM 5554)
      (denoteGraphDistributed pm initPM 9602) (denoteGraphDistributed pm initPM 9603)
      [4096, 16, 64] [2048, 16, 64] := by
  let fs := (sm.nodes.take 438).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 973).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 974).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 438, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 438, t ∉ n.outs) : fs t = denoteGraphDistributed sm initSM t :=
    l11a_prefix_read sm initSM 438 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 973, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 973, t ∉ n.outs) : fp t = denoteGraphDistributed pm initPM t :=
    l11a_prefix_read pm initPM 973 t hn hw
  have e9598 : fp 9598 = fp' 9598 := l11a_split pm pm.nodes initPM 9598 973 974
    (by omega) (by native_decide) (by native_decide)
  have e9599 : fp 9599 = fp' 9599 := l11a_split pm pm.nodes initPM 9599 973 974
    (by omega) (by native_decide) (by native_decide)
  have e9600 : fp 9600 = fp' 9600 := l11a_split pm pm.nodes initPM 9600 973 974
    (by omega) (by native_decide) (by native_decide)
  have e9601 : fp 9601 = fp' 9601 := l11a_split pm pm.nodes initPM 9601 973 974
    (by omega) (by native_decide) (by native_decide)
  have e9586 : fp 9586 = fp' 9586 := l11a_split pm pm.nodes initPM 9586 973 974
    (by omega) (by native_decide) (by native_decide)
  have e9587 : fp 9587 = fp' 9587 := l11a_split pm pm.nodes initPM 9587 973 974
    (by omega) (by native_decide) (by native_decide)
  have e5552 : fp 5552 = fp' 5552 := l11a_split pm pm.nodes initPM 5552 973 974
    (by omega) (by native_decide) (by native_decide)
  have e5553 : fp 5553 = fp' 5553 := l11a_split pm pm.nodes initPM 5553 973 974
    (by omega) (by native_decide) (by native_decide)
  have hqfull : fs 5550 = allGatherPrimDimN 0 2 0 [fp 9598, fp 9599] := by
    rw [bs 5550 (by native_decide) (by native_decide), bp 9598 (by native_decide) (by native_decide),
      bp 9599 (by native_decide) (by native_decide)]; exact hq.value
  have hkfull : fs 5551 = allGatherPrimDimN 0 2 0 [fp 9600, fp 9601] := by
    rw [bs 5551 (by native_decide) (by native_decide), bp 9600 (by native_decide) (by native_decide),
      bp 9601 (by native_decide) (by native_decide)]; exact hk.value
  have hvfull : fs 5548 = allGatherPrimDimN 0 2 0 [fp 9586, fp 9587] := by
    rw [bs 5548 (by native_decide) (by native_decide), bp 9586 (by native_decide) (by native_decide),
      bp 9587 (by native_decide) (by native_decide)]; exact hv.value
  have hcuQ' : fs 5552 = fp 5552 := by
    rw [bs 5552 (by native_decide) (by native_decide), bp 5552 (by native_decide) (by native_decide), hcuQ]
  have hcuK' : fs 5553 = fp 5553 := by
    rw [bs 5553 (by native_decide) (by native_decide), bp 5553 (by native_decide) (by native_decide), hcuK]
  have bridge : applyNodeRingAttn_sliding_window pm fp l11PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' l11PmSliding1 := by
    apply l11a_attn_congr
    · rw [l11_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9598
      · exact e9599
    · rw [l11_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9600
      · exact e9601
    · rw [l11_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9586
      · exact e9587
    · exact e5552
    · exact e5553
  have rSM : denoteGraphDistributed sm initSM 5554 =
      applyNodeRingAttn_sliding_window sm fs l11SmSliding := by
    rw [l11a_node_core sm initSM 438 l11SmSliding 5554 (by native_decide)
      l11_sm_sliding_node (by decide) (by native_decide) (by native_decide)]
    exact l11a_ring_sliding_first_out sm _ 0 5550 5551 5548 5552 5553 5554 5555
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 9602 =
      applyNodeRingAttn_sliding_window pm fp l11PmSliding0 := by
    rw [l11a_node_core pm initPM 973 l11PmSliding0 9602 (by native_decide)
      l11_pm_sliding_node0 (by decide) (by native_decide) (by native_decide)]
    exact l11a_ring_sliding_first_out pm _ 0 9598 9600 9586 5552 5553 9602 5555
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 9603 =
      applyNodeRingAttn_sliding_window pm fp' l11PmSliding1 := by
    rw [l11a_node_core pm initPM 974 l11PmSliding1 9603 (by native_decide)
      l11_pm_sliding_node1 (by decide) (by native_decide) (by native_decide)]
    exact l11a_ring_sliding_first_out pm _ 1 9599 9601 9587 5552 5553 9603 5555
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9598, fp 9599])
      (allGatherPrimDimN 0 2 0 [fp 9600, fp 9601])
      (allGatherPrimDimN 0 2 0 [fp 9586, fp 9587])
      (fp 5552) (fp 5553) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [l11a_attn_shape, ← hqfull, bs 5550 (by native_decide) (by native_decide), hq.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9598, fp' 9599])
      (allGatherPrimDimN 0 2 0 [fp' 9600, fp' 9601])
      (allGatherPrimDimN 0 2 0 [fp' 9586, fp' 9587])
      (fp' 5552) (fp' 5553) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9598, ← e9599,
      ← e9600, ← e9601,
      ← e9586, ← e9587,
      ← e5552, ← e5553]
    exact hfull
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm pm fs fp l11SmSliding l11PmSliding0 l11PmSliding1 2048 16 64
    (by omega) (by omega) (by omega) l11_sm_sliding_buddy l11_pm_sliding_buddy0
    l11_pm_sliding_buddy1 (by native_decide) (by native_decide)
    (by show 0 < (fs 5550).shape.length; rw [bs 5550 (by native_decide) (by native_decide), hq.full_shape]; decide)
    (by show 0 < (fs 5551).shape.length; rw [bs 5551 (by native_decide) (by native_decide), hk.full_shape]; decide)
    (by show 0 < (fs 5548).shape.length; rw [bs 5548 (by native_decide) (by native_decide), hv.full_shape]; decide)
    hqfull hkfull hvfull hcuQ' hcuK' rfl rfl rfl rfl hfull
  have hval : denoteGraphDistributed sm initSM 5554 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9602, denoteGraphDistributed pm initPM 9603] := by
    rw [rSM, hrec, bridge, ← rP0, ← rP1]
  have hs0 : (denoteGraphDistributed pm initPM 9602).shape = [2048, 16, 64] := by
    rw [rP0, applyNodeRingAttn_sliding_window_pair_eq_chunk pm fp l11PmSliding0
      l11PmSliding0 l11PmSliding1 0 l11_pm_sliding_buddy0 (by native_decide)]
    simp only [l11PmSliding0, l11PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 0 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9598, fp 9599])
      (allGatherPrimDimN 0 2 0 [fp 9600, fp 9601])
      (allGatherPrimDimN 0 2 0 [fp 9586, fp 9587])
      (fp 5552) (fp 5553) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] hfull (by omega)]
    rfl
  have hs1 : (denoteGraphDistributed pm initPM 9603).shape = [2048, 16, 64] := by
    rw [rP1, applyNodeRingAttn_sliding_window_pair_eq_chunk pm fp' l11PmSliding1
      l11PmSliding0 l11PmSliding1 1 l11_pm_sliding_buddy1 (by native_decide)]
    simp only [l11PmSliding0, l11PmSliding1, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    change (chunkPrimDimN 0 2 1 (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9598, fp' 9599])
      (allGatherPrimDimN 0 2 0 [fp' 9600, fp' 9601])
      (allGatherPrimDimN 0 2 0 [fp' 9586, fp' 9587])
      (fp' 5552) (fp' 5553) 16 4 64 64 true 512)).shape = [2048, 16, 64]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] hfull' (by omega)]
    rfl
  exact ⟨hval, by rw [hval, allGatherPrimDimN_shape 0 2 _ [2048,16,64] (by simp [hs0])]; rfl,
    hs0, hs1, by decide⟩

private theorem l11a_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  l11a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l11a_view (g : GraphDecl) (init : Store) (k r i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  l11a_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l11a_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o = fw_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  l11a_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l11a_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = denoteGraphDistributed g init i := by
  have h := l11a_reduce1 g init k _ i o id hk hn (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l11a_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o = elemwiseAdd (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  l11a_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

/-- Conditional L11 attention projection and residual boundary, from raw attention
and the bypass relation. -/
theorem l11o_residual5562_rel_of_raw
    (initSM initPM : Store) (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hraw : Gather2Rel (denoteGraphDistributed sm initSM 5554)
      (denoteGraphDistributed pm initPM 9602) (denoteGraphDistributed pm initPM 9603)
      [4096, 16, 64] [2048, 16, 64])
    (hbypass : Gather2Rel (denoteGraphDistributed sm initSM 8320)
      (denoteGraphDistributed pm initPM 15794) (denoteGraphDistributed pm initPM 15802)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5562)
      (denoteGraphDistributed pm initPM 9632) (denoteGraphDistributed pm initPM 9633)
      [4096, 1024] [2048, 1024] := by
  have rs0 := l11a_reshape sm initSM 439 0 5554 5556 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r00 := l11a_reshape pm initPM 975 0 9602 9604 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r10 := l11a_reshape pm initPM 976 1 9603 9605 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h0 : Gather2Rel (denoteGraphDistributed sm initSM 5556) (denoteGraphDistributed pm initPM 9604)
      (denoteGraphDistributed pm initPM 9605) [4096,1024] [2048,1024] := by
    refine ⟨?_, by rw [rs0]; rfl, by rw [r00]; rfl, by rw [r10]; rfl, by decide⟩
    rw [rs0, hraw.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ hraw.shard0_shape hraw.shard1_shape, r00, r10]
  have rs1 := l11a_reshape sm initSM 440 0 5556 5557 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r01 := l11a_reshape pm initPM 977 0 9604 9610 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r11 := l11a_reshape pm initPM 978 1 9605 9611 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h1 : Gather2Rel (denoteGraphDistributed sm initSM 5557) (denoteGraphDistributed pm initPM 9610)
      (denoteGraphDistributed pm initPM 9611) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributed sm initSM 5557 = denoteGraphDistributed sm initSM 5556 := by rw [rs1, fw_view_id_shape _ _ h0.full_shape]
    have e0 : denoteGraphDistributed pm initPM 9610 = denoteGraphDistributed pm initPM 9604 := by rw [r01, fw_view_id_shape _ _ h0.shard0_shape]
    have e1 : denoteGraphDistributed pm initPM 9611 = denoteGraphDistributed pm initPM 9605 := by rw [r11, fw_view_id_shape _ _ h0.shard1_shape]
    exact ⟨by rw [es, h0.value, ← e0, ← e1], by rw [es]; exact h0.full_shape,
      by rw [e0]; exact h0.shard0_shape, by rw [e1]; exact h0.shard1_shape, by decide⟩
  have hw := l11a_init_value initSM initPM hInit initGoal_5558
    (by native_decide) 5558 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l11a_init_shape initSM initPM hInit initGoal_5558
    (by native_decide) 5558 [1024,1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5558).shape = [1024,1024] := by rw [← hw]; exact hws
  have rsl := l11a_linear sm initSM 441 0 5557 5558 5559 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0l := l11a_linear pm initPM 979 0 9610 5558 9614 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1l := l11a_linear pm initPM 980 1 9611 5558 9615 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hl : Gather2Rel (denoteGraphDistributed sm initSM 5559) (denoteGraphDistributed pm initPM 9614)
      (denoteGraphDistributed pm initPM 9615) [4096,1024] [2048,1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rsl, h1.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h1.shard0_shape h1.shard1_shape hpw, r0l, r1l]
    · rw [rsl]; exact l11a_linear_shape 4096 1024 1024 _ _ h1.full_shape hws
    · rw [r0l]; exact l11a_linear_shape 2048 1024 1024 _ _ h1.shard0_shape hpw
    · rw [r1l]; exact l11a_linear_shape 2048 1024 1024 _ _ h1.shard1_shape hpw
  have rsv := l11a_view sm initSM 442 0 5559 5560 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0v := l11a_view pm initPM 981 0 9614 9624 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1v := l11a_view pm initPM 982 1 9615 9625 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hvw : Gather2Rel (denoteGraphDistributed sm initSM 5560) (denoteGraphDistributed pm initPM 9624)
      (denoteGraphDistributed pm initPM 9625) [4096,1024] [2048,1024] := by
    have es : denoteGraphDistributed sm initSM 5560 = denoteGraphDistributed sm initSM 5559 := by rw [rsv, fw_view_id_shape _ _ hl.full_shape]
    have e0 : denoteGraphDistributed pm initPM 9624 = denoteGraphDistributed pm initPM 9614 := by rw [r0v, fw_view_id_shape _ _ hl.shard0_shape]
    have e1 : denoteGraphDistributed pm initPM 9625 = denoteGraphDistributed pm initPM 9615 := by rw [r1v, fw_view_id_shape _ _ hl.shard1_shape]
    exact ⟨by rw [es, hl.value, ← e0, ← e1], by rw [es]; exact hl.full_shape,
      by rw [e0]; exact hl.shard0_shape, by rw [e1]; exact hl.shard1_shape, by decide⟩
  have rsf := l11a_float sm initSM 443 0 5560 5561 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0f := l11a_float pm initPM 983 0 9624 9628 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1f := l11a_float pm initPM 984 1 9625 9629 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf : Gather2Rel (denoteGraphDistributed sm initSM 5561) (denoteGraphDistributed pm initPM 9628)
      (denoteGraphDistributed pm initPM 9629) [4096,1024] [2048,1024] :=
    ⟨by rw [rsf, hvw.value, ← r0f, ← r1f], by rw [rsf]; exact hvw.full_shape,
      by rw [r0f]; exact hvw.shard0_shape, by rw [r1f]; exact hvw.shard1_shape, by decide⟩
  have rsa := l11a_add sm initSM 444 0 8320 5561 5562 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0a := l11a_add pm initPM 985 0 15794 9628 9632 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1a := l11a_add pm initPM 986 1 15802 9629 9633 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rsa, hbypass.value, hf.value, elemwiseAdd_allGather0_commute_cp2 _ _ _ _
      2048 1024 (by omega) (by omega) hbypass.shard0_shape hbypass.shard1_shape
      hf.shard0_shape hf.shard1_shape, r0a, r1a]
  · rw [rsa]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.full_shape hf.full_shape
  · rw [r0a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard0_shape hf.shard0_shape
  · rw [r1a]; exact elemwiseAdd_shape_of_shapes _ _ _ hbypass.shard1_shape hf.shard1_shape

/-- Full conditional L11 ordinary attention-to-residual boundary. -/
theorem l11o_residual5562_rel_of_qkv
    (initSM initPM : Store) (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq : Gather2Rel (denoteGraphDistributed sm initSM 5550) (denoteGraphDistributed pm initPM 9598)
      (denoteGraphDistributed pm initPM 9599) [4096,16,64] [2048,16,64])
    (hk : Gather2Rel (denoteGraphDistributed sm initSM 5551) (denoteGraphDistributed pm initPM 9600)
      (denoteGraphDistributed pm initPM 9601) [4096,4,64] [2048,4,64])
    (hv : Gather2Rel (denoteGraphDistributed sm initSM 5548) (denoteGraphDistributed pm initPM 9586)
      (denoteGraphDistributed pm initPM 9587) [4096,4,64] [2048,4,64])
    (hcuQ : denoteGraphDistributed sm initSM 5552 = denoteGraphDistributed pm initPM 5552)
    (hcuK : denoteGraphDistributed sm initSM 5553 = denoteGraphDistributed pm initPM 5553)
    (hbypass : Gather2Rel (denoteGraphDistributed sm initSM 8320) (denoteGraphDistributed pm initPM 15794)
      (denoteGraphDistributed pm initPM 15802) [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5562) (denoteGraphDistributed pm initPM 9632)
      (denoteGraphDistributed pm initPM 9633) [4096,1024] [2048,1024] :=
  l11o_residual5562_rel_of_raw initSM initPM hInit
    (l11o_raw5554_rel_of_qkv initSM initPM hq hk hv hcuQ hcuK) hbypass

/-- Complete L11 ordinary-attention composition from its incoming residual
boundary.  Q, K, and V are reconstructed internally from `L11OrdinaryQKV`;
the residual bypass and packed-cu aliases are discharged from the graph and
init goals. -/
theorem l11o_residual5562_rel_from_boundary5540
    (initSM initPM : Store) (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributed sm initSM 5540)
      (denoteGraphDistributed pm initPM 9558) (denoteGraphDistributed pm initPM 9559)
      [4096,1024] [2048,1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5562)
      (denoteGraphDistributed pm initPM 9632) (denoteGraphDistributed pm initPM 9633)
      [4096,1024] [2048,1024] := by
  obtain ⟨hq, hk⟩ := l11o_q5550_k5551_rels_from_boundary initSM initPM hInit h
  have hv := l11o_v5548_rel_from_boundary initSM initPM hInit h
  have ms := l11a_reduce1 sm initSM 431
    { rank := 0, op := "OpName.FW_multiref", ins := [5540], outs := [8316, 8320], params := [2] }
    5540 8320 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11a_multiref_at sm st 0 5540 [8316, 8320] 2 rfl 8320 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11a_reduce1 pm initPM 956
    { rank := 0, op := "OpName.FW_multiref", ins := [9558], outs := [15790, 15794], params := [2] }
    9558 15794 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11a_multiref_at pm st 0 9558 [15790, 15794] 2 rfl 15794 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11a_reduce1 pm initPM 957
    { rank := 1, op := "OpName.FW_multiref", ins := [9559], outs := [15798, 15802], params := [2] }
    9559 15802 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11a_multiref_at pm st 1 9559 [15798, 15802] 2 rfl 15802 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hbypass : Gather2Rel (denoteGraphDistributed sm initSM 8320)
      (denoteGraphDistributed pm initPM 15794) (denoteGraphDistributed pm initPM 15802)
      [4096,1024] [2048,1024] :=
    ⟨by rw [ms, h.value, ← m0, ← m1], by rw [ms]; exact h.full_shape,
      by rw [m0]; exact h.shard0_shape, by rw [m1]; exact h.shard1_shape, by decide⟩
  have hcuQ := l11a_init_value initSM initPM hInit initGoal_5552
    (by native_decide) 5552 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuK := l11a_init_value initSM initPM hInit initGoal_5553
    (by native_decide) 5553 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact l11o_residual5562_rel_of_qkv initSM initPM hInit hq hk hv hcuQ hcuK hbypass

end TrainVerify.Denote.GeneratedPatterns
