import denote.yoco_goals.L11OrdinaryQKV

set_option linter.style.longLine false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

/-- Faithful one-input reduction, retaining the old helper's argument order so
L10 local proofs can be migrated without changing their node certificates. -/
theorem l10f_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (_hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid = opfun (s inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init inTid) :=
  denoteGraphDistributedFaithful_reduce1 g init k node inTid outTid opfun
    hk hnode happly hdrop_nil hdrop hpre_nil hpre

/-- Faithful two-input reduction with the legacy L10 call surface. -/
theorem l10f_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (_hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid = opfun (s in1) (s in2))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2) :=
  denoteGraphDistributedFaithful_reduce2 g init k node in1 in2 outTid opfun
    hk hnode happly hdrop_nil hdrop hpre_nil hpre1 hpre2

/-- Faithful four-input reduction used by the L10 rotary node. -/
theorem l10f_reduce4 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in0 in1 in2 in3 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (_hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hdrop_nil hdrop,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpre_nil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpre_nil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpre_nil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpre_nil hpre3]

/-- A faithful multiref node is conservative and returns its selected input. -/
theorem l10f_apply_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs,
        params := [n] } outTid = s xTid := by
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by simp) (by simp) (by simp)]
  unfold applyNodeDistributed
  rw [if_neg (by simp)]
  exact l11o_apply_multiref_at g s rank xTid outs n hn outTid hmem

/-- Faithful init-value bridge on the exact Goal-1 graph pair. -/
theorem l10f_init_value (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals) (W : Tid)
    (htp : gW.tps = [{ rank := 0, tid := W }]) (hgd : gW.gatherDim = 0)
    (hrep : gW.replicated = false) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM W =
      denoteGraphDistributedFaithful pm_goal_1 initPM W := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  have hv := hg.2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hv
  simp only [List.map, reconstructWithDim] at hv
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM W (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM W (by native_decide) hpm]
  exact hv

/-- Faithful init-shape bridge on the exact Goal-1 SM graph. -/
theorem l10f_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (htsShape : gW.tsShape = sh) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
    initSM W (by native_decide) hsm, ← hts, ← htsShape]
  exact hg.1

/-- Faithful RMS reduction. -/
theorem l10f_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_rms_norm", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o =
      fw_rms_norm (denoteGraphDistributedFaithful g init x)
        (denoteGraphDistributedFaithful g init w) :=
  l10f_reduce2 g init k _ x w o fw_rms_norm hk hn (by simp)
    (fun s => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp)]
      exact applyNode_fw_rms_norm_out_1p g s r x w o)
    hdn hdw hpn hpx hpw

/-- Faithful per-head projection reduction. -/
theorem l10f_per_head (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o =
      fw_per_head_linear (denoteGraphDistributedFaithful g init x)
        (denoteGraphDistributedFaithful g init w) :=
  l10f_reduce2 g init k _ x w o fw_per_head_linear hk hn (by simp)
    (fun s => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp)]
      exact l11o_apply_per_head g s r x w o)
    hdn hdw hpn hpx hpw

/-- Faithful generated AllGather reduction. -/
theorem l10f_allgather2 (g : GraphDecl) (init : Store) (k r x0 x1 o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.AllGatherPrim", ins := [x0, x1], outs := [o], params := [0] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hp0 : ∀ n ∈ g.nodes.drop k, x0 ∉ n.outs)
    (hp1 : ∀ n ∈ g.nodes.drop k, x1 ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = allGatherPrimDimN 0 g.numRanks r
      [denoteGraphDistributedFaithful g init x0,
       denoteGraphDistributedFaithful g init x1] :=
  l10f_reduce2 g init k _ x0 x1 o
    (fun a b => allGatherPrimDimN 0 g.numRanks r [a, b]) hk hn (by simp)
    (fun s => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp), applyNodeRingAttn_eq_applyNode_of_not_ring g s _
        (by simp) (by simp)]
      exact applyNode_allGatherPrimDimN_out g s r [x0, x1] o 0)
    hdn hdw hpn hp0 hp1

/-- Faithful generated Chunk reduction. -/
theorem l10f_chunk (g : GraphDecl) (init : Store) (k r x o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.ChunkPrim", ins := [x], outs := [o], params := [0] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs) :
    denoteGraphDistributedFaithful g init o =
      chunkPrimDimN 0 g.numRanks r (denoteGraphDistributedFaithful g init x) :=
  l10f_reduce1 g init k _ x o (fun a => chunkPrimDimN 0 g.numRanks r a)
    hk hn (by simp)
    (fun s => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp), applyNodeRingAttn_eq_applyNode_of_not_ring g s _
        (by simp) (by simp)]
      exact applyNode_chunkPrimDimN_out g s r x o 0)
    hdn hdw hpn hpx

end
end TrainVerify.Denote.GeneratedPatterns
